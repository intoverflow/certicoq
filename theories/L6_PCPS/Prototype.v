Require Import Coq.Strings.Ascii Coq.Strings.String.
Infix "+++" := append (at level 60, right associativity).

Require Import Coq.Lists.List.
Import ListNotations.

From MetaCoq Require Import Template.All.
Import MonadNotation.
Module TM := MetaCoq.Template.monad_utils.

From ExtLib.Core Require Import RelDec.
From ExtLib.Data Require Import Nat List Option Pair String.
From ExtLib.Structures Require Import Monoid Functor Applicative Monads Traversable.
From ExtLib.Data.Monads Require Import IdentityMonad EitherMonad StateMonad.

Require Import Coq.NArith.BinNat.
Local Open Scope N_scope.

Require Import Coq.Relations.Relations.

Require Import Ltac2.Ltac2.
Import Ltac2.Notations.
Set Default Proof Mode "Ltac2".

Set Universe Polymorphism.

Require Export CertiCoq.L6.Rewriting.
Require Export CertiCoq.L6.PrototypeGenFrame.

(* -------------------- Converting between named and indices --------------------
   Indices are a real pain for some of the things we want to do.
   Hack: quoted ASTs will never contain names starting with $, so we're free to use
   names like $1, $2, and $3 internally. So, to stay sane, we'll use tVar + nNamed
   binders for naming.
   Before unquoting, all internally generated names will be replaced by the proper
   indices. *)

Fail Run TemplateProgram (tmUnquote (tLambda (nNamed "$oof") <%nat%> (tRel 0))).

Definition gensym (suffix : string) : GM string :=
  let! n := get in
  let! _ := modify (fun n => 1 + n) in
  ret (string_of_N n +++ "$" +++ suffix).

Definition add_sigils (x : name) : GM string :=
  match x with
  | nAnon => gensym ""
  | nNamed s => gensym s
  end.

Fixpoint remove_sigils (s : string) : name :=
  match s with
  | EmptyString => nNamed s
  | "$" => nAnon
  | String "$" s => nNamed s
  | String _ s => remove_sigils s
  end.

Fixpoint remove_sigils' (s : string) : string :=
  match s with
  | EmptyString => s
  | "$" => ""
  | String "$" s => s
  | String _ s => remove_sigils' s
  end.

Definition named_of (Γ : list string) (tm : term) : GM term :=
  let fix go (n : nat) (Γ : list string) (tm : term) : GM term :=
    match n with O => raise "named_of: OOF" | S n =>
      let go := go n in
      let go_mfix mfix : GM (mfixpoint term) :=
        let! names := mapM (fun d => add_sigils d.(dname)) mfix in
        let Γ' := rev names ++ Γ in
        mapM
          (fun '(s, d) =>
            mkdef _ (nNamed s)
              <$> go Γ d.(dtype)
              <*> go Γ' d.(dbody)
              <*> ret d.(rarg))
          (combine names mfix)
      in
      match tm with
      | tRel n => tVar <$> nthM_nat n Γ
      | tVar id => ret tm
      | tEvar ev args => ret tm
      | tSort s => ret tm
      | tCast t kind v => tCast <$> go Γ t <*> ret kind <*> go Γ v
      | tProd na ty body =>
        let! s := add_sigils na in
        tProd (nNamed s) <$> go Γ ty <*> go (s :: Γ) body
      | tLambda na ty body =>
        let! s := add_sigils na in
        tLambda (nNamed s) <$> go Γ ty <*> go (s :: Γ) body
      | tLetIn na def def_ty body =>
        let! s := add_sigils na in
        tLetIn (nNamed s) <$> go Γ def <*> go Γ def_ty <*> go (s :: Γ) body
      | tApp f args => mkApps <$> go Γ f <*> mapM (go Γ) args
      | tConst c u => ret tm
      | tInd ind u => ret tm
      | tConstruct ind idx u => ret tm
      | tCase ind_and_nbparams type_info discr branches =>
        tCase ind_and_nbparams
          <$> go Γ type_info <*> go Γ discr
          <*> mapM (fun '(n, t) => pair n <$> go Γ t) branches
      | tProj proj t => tProj proj <$> go Γ t
      | tFix mfix idx => tFix <$> go_mfix mfix <*> ret idx
      | tCoFix mfix idx => tCoFix <$> go_mfix mfix <*> ret idx
      end
    end
  in go 1000%nat Γ tm.

(*
Compute runGM' 0 (named_of [] <%
  fun x y z w : nat =>
  match x, y with
  | S x, S y => z * x + y * w
  | O, y => z + z
  | _, _ => w
  end%nat%>).
Compute runGM' 0 (named_of [] <%forall x y z : nat, x = y -> y = z -> x = z%>).
*)

Definition find_str (s : string) (ss : list string) : GM nat :=
  let fix go n ss :=
    match ss with
    | [] => raise ("find_str: " +++ s)
    | s' :: ss => if s ==? s' then ret n else go (S n) ss
    end
  in go O ss.

Definition indices_of (Γ : list string) (t : term) : GM term :=
  let index_of Γ s := find_str s Γ in
  let go_name (x : name) : (name × string) :=
    match x with
    | nAnon => (nAnon, "anon")
      (* can never be referred to in named rep, so we don't care if there are clashes *)
    | nNamed s => (remove_sigils s, s)
    end
  in
  let fix go (n : nat) (Γ : list string) (tm : term) : GM term :=
    match n with O => raise "named_of: OOF" | S n =>
      let go := go n in
      let go_mfix mfix : GM (mfixpoint term) :=
        let nass := map (fun d => go_name d.(dname)) mfix in
        let '(names, strings) := split nass in
        let Γ' := rev strings ++ Γ in
        mapM
          (fun '(na, d) =>
            mkdef _ na
              <$> go Γ d.(dtype)
              <*> go Γ' d.(dbody)
              <*> ret d.(rarg))
          (combine names mfix)
      in
      match tm with
      | tRel n => ret tm
      | tVar id => tRel <$> index_of Γ id
      | tEvar ev args => ret tm
      | tSort s => ret tm
      | tCast t kind v => tCast <$> go Γ t <*> ret kind <*> go Γ v
      | tProd na ty body =>
        let '(na, s) := go_name na in tProd na <$> go Γ ty <*> go (s :: Γ) body
      | tLambda na ty body =>
        let '(na, s) := go_name na in tLambda na <$> go Γ ty <*> go (s :: Γ) body
      | tLetIn na def def_ty body =>
        let '(na, s) := go_name na in tLetIn na <$> go Γ def <*> go Γ def_ty <*> go (s :: Γ) body
      | tApp f args => mkApps <$> go Γ f <*> mapM (go Γ) args
      | tConst c u => ret tm
      | tInd ind u => ret tm
      | tConstruct ind idx u => ret tm
      | tCase ind_and_nbparams type_info discr branches =>
        tCase ind_and_nbparams
          <$> go Γ type_info <*> go Γ discr
          <*> mapM (fun '(n, t) => pair n <$> go Γ t) branches
      | tProj proj t => tProj proj <$> go Γ t
      | tFix mfix idx => tFix <$> go_mfix mfix <*> ret idx
      | tCoFix mfix idx => tCoFix <$> go_mfix mfix <*> ret idx
      end
    end
  in go 1000%nat [] t.

Definition check_roundtrip (Γ : list string) (t : term) : GM (option (term × term)) :=
  let! named := named_of Γ t in
  let! t' := indices_of Γ named in
  ret (if string_of_term t ==? string_of_term t' then None else Some (t, t')).

Compute runGM' 0 (check_roundtrip [] <%
  fun x y z w : nat =>
  match x, y with
  | S x, S y => z * x + y * w
  | O, y => z + z
  | _, _ => w
  end%nat%>).
Compute runGM' 0 (check_roundtrip [] <%forall x y z : nat, x = y -> y = z -> x = z%>).
Compute runGM' 0 (check_roundtrip [] <%
  fix ev n :=
    match n with
    | 0 => true
    | S n => odd n
    end%nat
  with odd n :=
    match n with
    | 0 => false
    | S n => ev n
    end%nat
  for ev%>).

(* Renames binders too; in general, doesn't respect scope at all *)
Definition rename (σ : Map string string) : term -> term :=
  let go_str (s : string) : string := find_d s s σ in
  let go_name (na : name) : name :=
    match na with
    | nAnon => na
    | nNamed id => nNamed (go_str id)
    end
  in
  fix go (tm : term) : term :=
    let go_mfix (mfix : list (def term)) : list (def term) :=
      map (fun '(mkdef f ty body rarg) => mkdef _ (go_name f) (go ty) (go body) rarg) mfix
    in
    match tm with
    | tRel n => tm
    | tVar id => tVar (go_str id)
    | tEvar ev args => tEvar ev (map go args)
    | tSort s => tm
    | tCast t kind v => tCast (go t) kind (go v)
    | tProd na ty body => tProd (go_name na) (go ty) (go body)
    | tLambda na ty body => tLambda (go_name na) (go ty) (go body)
    | tLetIn na def def_ty body => tLetIn (go_name na) (go def) (go def_ty) (go body)
    | tApp f args => mkApps (go f) (map go args)
    | tConst c u => tm
    | tInd ind u => tm
    | tConstruct ind idx u => tm
    | tCase ind_and_nbparams type_info discr branches =>
      tCase ind_and_nbparams (go type_info) (go discr) (map (on_snd go) branches)
    | tProj proj t => tProj proj (go t)
    | tFix mfix idx => tFix (go_mfix mfix) idx
    | tCoFix mfix idx => tCoFix (go_mfix mfix) idx
    end.

(* -------------------- Generation of helper function types -------------------- *)

(* The type of correct rewriters (AuxData and Preserves instances are additional assumptions
   needed by the generator) *)
Definition rewriter {U} `{Frame U} `{AuxData U} (root : U) (R : relation (univD root))
  (D : forall {A}, univD A -> Set) `{@Delayed U H (@D)}
  (R_C : forall {A}, frames_t A root -> Set)
  (St : forall {A}, frames_t A root -> univD A -> Set)
 `{@Preserves_R U H root (@R_C)}
 `{@Preserves_S U H root (@St)}
:=
  Fuel -> forall A (C : @frames_t U H A root) (e : univD A) (d : D e),
  rw_for root R (@R_C) (@St) C (delayD e d).

(* ---------- Flags to aid in proof saerch ---------- *)

(* For each rule, *)
Inductive ExtraVars (s : string) : Prop := MkExtraVars.
Inductive TopdownRunRule (s : string) : Prop := MkTopdownRunRule.
Inductive BottomupRunRule (s : string) : Prop := MkBottomupRunRule.
Inductive Success (s : string) : Prop := MkSuccess.
Inductive Failure (s : string) : Prop := MkFailure.

(* For each constructor, *)
Inductive ConstrDelay {A} (c : A) : Prop := MkConstrDelay.
Inductive SmartConstr {A} (c : A) : Prop := MkSmartConstr.
Inductive SmartConstrCase {A} (e : A) : Prop := MkSmartConstrCase.

(* For each nonatomic type, *)
Inductive Topdown {A} (u : A) : Prop := MkTopdown.
Inductive Bottomup {A} (u : A) : Prop := MkBottomup.
Inductive InspectCaseRule (s : string) : Prop := MkInspectCaseRule.
Inductive InspectCaseCongruence {A} (c : A) : Prop := MkInspectCaseCongruence.
Inductive Active (s : string) : Prop := MkActive.
Inductive Congruence {A} (c : A) : Prop := MkCongruence.
Inductive Fallback : Prop := MkFallback.
Inductive Impossible : Prop := MkImpossible.

Record RwObligations A := mk_obs {
  (* For each rule, *)
  obExtraVars : list A;
  obRunRules : list A;
  (* For each constructor, *)
  obConstrDelays : list A;
  obSmartConstrs : list A;
  (* For each nonatomic type, *)
  obTopdowns : list A;
  obBottomups : list A }.
Arguments mk_obs {_}.

(* ---------- MetaCoq helpers ---------- *)

Fixpoint quote_pos (n : positive) : term :=
  match n with
  | xH => <%xH%>
  | xI n => mkApps <%xI%> [quote_pos n]
  | xO n => mkApps <%xO%> [quote_pos n]
  end.

Definition quote_N (n : N) : term :=
  match n with
  | N0 => <%N0%>
  | Npos n => mkApps <%Npos%> [quote_pos n]
  end.

Definition quote_nat (n : nat) : term :=
  Nat.iter n (fun t => mkApps <%S%> [t]) <%O%>.

Definition quote_bool (b : bool) : term := if b then <%true%> else <%false%>.

Definition quote_char (c : ascii) : term :=
  match c with
  | Ascii x x0 x1 x2 x3 x4 x5 x6 =>
    tApp <%Ascii%> (map quote_bool [x; x0; x1; x2; x3; x4; x5; x6])
  end.

Fixpoint quote_string (s : string) : term :=
  match s with
  | EmptyString => <%EmptyString%>
  | String c s => tApp <%String%> [quote_char c; quote_string s]
  end.

Run TemplateProgram (tmPrint =<< tmUnquote (quote_string "abc")).

(* abbreviate = map head . splitOn "_" *)
Fixpoint abbreviate s :=
  let fix skip_to_underscore s := 
    match s with
    | "" => s
    | String "_" s => abbreviate s
    | String _ s => skip_to_underscore s
    end
  in
  match s with
  | "" => s
  | String "_" s => abbreviate s
  | String c s => String c (skip_to_underscore s)
  end.
Compute abbreviate "list_var".

Fixpoint vars_of (t : term) : Set' string :=
  match t with
  | tRel n => empty
  | tVar id => sing id tt
  | tEvar ev args => union_all (map vars_of args)
  | tSort s => empty
  | tCast t kind v => vars_of t ∪ vars_of v
  | tProd na ty body => vars_of ty ∪ vars_of body
  | tLambda na ty body => vars_of ty ∪ vars_of body
  | tLetIn na def def_ty body => vars_of def ∪ vars_of def_ty ∪ vars_of body
  | tApp f args => vars_of f ∪ union_all (map vars_of args)
  | tConst c u => empty
  | tInd ind u => empty
  | tConstruct ind idx u => empty
  | tCase ind_and_nbparams type_info discr branches =>
    vars_of type_info ∪ vars_of discr ∪ union_all (map (fun '(_, t) => vars_of t) branches)
  | tProj proj t => vars_of t
  | tFix mfix idx => union_all (map (fun def => vars_of def.(dtype) ∪ vars_of def.(dbody)) mfix)
  | tCoFix mfix idx => union_all (map (fun def => vars_of def.(dtype) ∪ vars_of def.(dbody)) mfix)
  end.

(* ---------- Parsing the inductive relation ---------- *)

Definition named_ctx := list (string × context_decl).

Definition named_of_context (Γ : context) : GM named_ctx :=
  foldrM
    (fun d m =>
      match d.(decl_name) with
      | nAnon => raise "named_of_context: nAnon"
      | nNamed s => ret ((s, d) :: m)
      end)
    []
    Γ.

Definition drop_names : named_ctx -> context := map snd.

Inductive rule_direction := dTopdown | dBottomup.
Definition path_step := (string × list term) × nat.
Record rule_t := mk_rule {
  rName : string;
  rType : term;
  rArity : nat;
  rDir : rule_direction;
  rHoleU : nat; (* index into the inductive type rw_univ *)
  rΓ : named_ctx;
  rC : term;
  rLhs : term;
  rRhs : term;
  rLhsVars : Set' string;
  rRecVars : Set' string;
  rSpecialVars : Set' string; }.
Record rules_t := mk_rules {
  rR : inductive;
  rRules : list rule_t;
  rUniv : inductive;
  rRootU : nat;
  rHFrame : term; }.

Definition ctor_ty := (string × term) × nat.
Definition ctors_ty := list ctor_ty.

Section GoalGeneration.

Context (R_C St : term).

(* Check if a term is a variable if you strip off casts *)
Fixpoint is_var (x : term) : option string :=
  match x with
  | tVar x => Some x
  | tCast x _ _ => is_var x
  | _ => None
  end.

(* Rec (f .. x) *)
(* TODO: this is a hack and depends on the _CoqProject file+name of this file *)
Compute <%@Rec%>.
Definition prefix := "CertiCoq.L6.Rewriting.". 
Definition rec_rhs_vars_of : term -> Set' string.
  ltac1:(refine(
  let fix go tm :=
    match tm with
    | tApp (tConstruct _ _ _) args => union_all (map go args)
    | tApp (tConst func []) args =>
      if func ==? (prefix +++ "Rec") then
        match args with
        | [_A; x] =>
          match is_var x with
          | Some x => sing x tt
          | None =>
            match x with
            | tApp (tConstruct _ _ _) _ => empty
            | tApp _f ((x :: _) as xs) =>
              match is_var (last xs x) with
              | Some x => sing x tt
              | None => empty
              end
            | _ => empty
            end
          end
        | _ => empty
        end
      else empty
    | _ => empty
    end
  in go
)). (* TODO will Prototype. always work? *)
Defined.

Definition rule_of_ind_ctor (ind_ctor : ctor_ty) : GM rule_t. ltac1:(refine(
  let '(name, ctor_ty, arity) := ind_ctor in
  let! ctor_ty :=
    let! name := gensym name in
    named_of [name] ctor_ty
  in
  let '(Γ, rty) := decompose_prod_assum [] ctor_ty in
  let! Γ := named_of_context Γ in
  match rty with
  (* Topdown rule *)
  | tApp (tVar _) [
      tApp (tConst framesD1 []) [
        _univ; _HFrame; tConstruct _univ_ind hole_ut []; _root_univ_ty; tVar _ as C; lhs];
      tApp (tConst framesD2 []) [_; _; _; _; _; rhs]] =>
    let lhs_vars := vars_of lhs in
    let rec_vars := rec_rhs_vars_of rhs in
    let special_vars := rec_vars in (*∩ lhs_vars in*)
    ret (mk_rule name ctor_ty arity dTopdown hole_ut Γ C lhs rhs
      lhs_vars rec_vars special_vars)
  (* Bottomup rule *)
  | tApp (tConst _BottomUp []) [_; tApp (tVar _) [
      tApp (tConst _framesD []) [
        _univ; _HFrame; tConstruct _univ_ind hole_ut []; _root_univ_ty; C; lhs];
      tApp (tConst _ []) [_; _; _; _; _; rhs]]] =>
    let lhs_vars := vars_of lhs in
    let rec_vars := rec_rhs_vars_of rhs in
    let special_vars := rec_vars ∩ lhs_vars in
    ret (mk_rule name ctor_ty arity dBottomup hole_ut Γ C lhs rhs
      lhs_vars rec_vars special_vars)
  | rty => raise ("rule_of_ind_ctor: " +++ string_of_term rty)
  end
)).
Defined.

Definition parse_rel_pure (ind : inductive) (mbody : mutual_inductive_body)
           (body : one_inductive_body) : GM rules_t. ltac1:(refine(
  let! rules :=
    mapiM
      (fun i ctor => rule_of_ind_ctor ctor)
      body.(ind_ctors)
  in
  match rules with
  | [] => raise "parse_rel: empty relation"
  | {| rΓ := Γ; rC := tVar C |} :: _ =>
    let! Cty := findM C Γ in
    match Cty.(decl_type) with
    | tApp (tConst _frames_t []) [tInd univ []; HFrame; _hole; tConstruct _univ root []] =>
      ret (mk_rules ind rules univ root HFrame)
    | _ => raise "parse_rel: C's type illformed"
    end
  | _ :: _ => raise "parse_rel: C not tRel"
  end
)).
Defined.

Definition parse_rel {A} (ind : A) : TemplateMonad rules_t :=
  ind <- tmQuote ind ;;
  match ind with
  | tInd ind [] =>
    mbody <- tmQuoteInductive ind.(inductive_mind) ;;
    match mbody.(ind_bodies) with
    | [body] => runGM (parse_rel_pure ind mbody body)
    | _ => tmFail "rel_constr_types: relation has more than one body"
    end
  | _ => tmFail "rel_constr_types: not an inductive relation"
  end.

End GoalGeneration.

Ltac runGM n m k :=
  let res := eval cbv in (runGM' n m) in
  match res with
  | inl ?e => fail 10 "runGM:" e
  | inr (?x, ?n) => k x n
  end.

Ltac parse_rel n R k :=
  run_template_program (
    ind <- tmQuote R ;;
    match ind with
    | tInd ind [] =>
      mbody <- tmQuoteInductive ind.(inductive_mind) ;;
      match mbody.(ind_bodies) with
      | [body] => ret (ind, mbody, body)
      | _ => tmFail "rel_constr_types: relation has more than one body"
      end
    | _ => tmFail "rel_constr_types: not an inductive relation"
    end) ltac:(fun pack =>
  match pack with
  | (?ind, ?mbody, ?body) =>
    runGM n (parse_rel_pure ind mbody body) k
  end).

(* ---------- Types of helpers for computing preconditions/intermediate values ---------- *)

Section GoalGeneration.

Context
  (aux_data : aux_data_t)
  (typename := aux_data.(aTypename))
  (ind_info := aux_data.(aIndInfo))
  (graph := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname))
  (frames_of_constr := aux_data.(aFramesOfConstr)).
Context (delay_t : term)
        (delayD : term) (* specialized to forall {A}, univD A -> delay_t -> univD A *).
Context (R_C St : term) (rules : rules_t)
        (rw_univ := rules.(rUniv))
        (HFrame := rules.(rHFrame))
        (root := rules.(rRootU))
        (* specialize to univD rw_univ -> univD rw_univ -> Set *)
        (frames_t := mkApps <%@frames_t%> [tInd rw_univ []; HFrame])
        (* specialize to rw_univ -> Set *)
        (univD := mkApps <%@univD%> [tInd rw_univ []; HFrame]) 
        (mk_univ := fun n => tConstruct rw_univ n []).

Definition gen_extra_vars_ty (rule : rule_t) : GM term :=
  match rule.(rDir) with
  | dTopdown =>
    let hole := rule.(rHoleU) in
    let lhs := rule.(rLhs) in
    let lhs_vars := rule.(rLhsVars) in
    (* Currently, the context rΓ contains (lhs vars ∪ rhs vars) in unspecified order. *)
    (*    We will rearrange it to be (lhs vars .. rhs vars ..). *)
    let ctx := map (fun '(x, decl) => (member x lhs_vars, x, decl)) rule.(rΓ) in
    let '(lhs_ctx, rhs_ctx) := partition (fun '(in_lhs, _, _) => in_lhs) ctx in
    (* rhs_ctx also contains C: C will actually be introduced in the outer scope
       already. We'll just borrow its name. *)
    let! C :=
      match rule.(rC) with
      | tVar C => ret C
      | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
      end
    in
    (* Filter to drop C *)
    let rhs_ctx := filter (fun '(_, x, decl) => negb (x ==? C)) rhs_ctx in
    let rhs_ctx := map (fun '(_, x, decl) => (x, decl)) rhs_ctx in
    let! R := gensym "R" in
    (* let n_univs := mfold (fun u n m => insert n u m) empty univ_of_tyname in *)
    (* let! t_tyname := findM'' (N.of_nat hole) n_univs "t_univ_i" in *)
    (* let! e := gensym (abbreviate t_tyname) in *)
    let! d := gensym "d" in
    let! r_C := gensym "r_C" in
    let! s := gensym "s" in
    let hole := mk_univ hole in
    let root := mk_univ root in
    let rule_name := quote_string rule.(rName) in
    let rΓ := filter (fun '(x, decl) => negb (x ==? C)) rule.(rΓ) in
    let! '(extra_vars, σ) :=
      let Γ := map_of_list rΓ in
      mfoldM
        (fun x 'tt '(extras, σ) =>
          let! x' := gensym (remove_sigils' x) in
          let! md' := if member x rule.(rSpecialVars) then Some <$> gensym "d" else ret None in
          let! decl := findM' x Γ "special_var" in
          let ty := decl.(decl_type) in
          let! tyname := mangle ind_info ty in
          let! univ_n := findM' tyname univ_of_tyname "applicable: univ_n" in
          let u := mk_univ (N.to_nat univ_n) in
          ret ((x, x', md', ty, u) :: extras, insert x x' σ))
        ([], empty) (rule.(rLhsVars) ∪ rule.(rSpecialVars))
    in
    let lhs' := rename σ rule.(rLhs) in
    ret (fn (mkApps <%ExtraVars%> [rule_name])
      (tProd (nNamed R) type0 (tProd (nNamed C) (mkApps frames_t [hole; root])
      (fold_right
        (fun '(x, x', md', xty, u) ty =>
          if member x rule.(rLhsVars)
          then tProd (nNamed x') xty ty
          else ty)
        (tProd (nNamed d) (mkApps delay_t [hole; lhs'])
        (tProd (nNamed r_C) (mkApps R_C [hole; tVar C])
        (tProd (nNamed s) (mkApps St [hole; tVar C; mkApps delayD [hole; lhs'; tVar d]])
        (fn (fn (mkApps <%Success%> [rule_name])
          (fold_right
            (fun '(x, x', md', xty, u) ty =>
              (if member x rule.(rLhsVars) then tProd (nNamed x) xty else tProd (nNamed x') xty)
              match md' with
              | Some d' => tProd (nNamed d') (mkApps delay_t [u; tVar x']) ty
              | None => ty
              end)
            (it_mkProd_or_LetIn (drop_names rhs_ctx)
            (fn (mkApps <%@eq%> [mkApps univD [hole]; mkApps delayD [hole; lhs'; tVar d]; rule.(rLhs)])
            (fold_right
              (fun '(x, x', md', xty, u) ty =>
                match md' with
                | Some d' => fn (mkApps <%@eq%> [xty; tVar x; mkApps delayD [u; tVar x'; tVar d']]) ty
                | None => ty
                end)
              (fn (mkApps R_C [hole; tVar C]) (fn (mkApps St [hole; tVar C; rule.(rRhs)]) (tVar R)))
              extra_vars)))
            extra_vars))
        (fn (fn (mkApps <%Failure%> [rule_name]) (tVar R))
        (tVar R))))))
        (* (fold_right (fun '(_, s, d) ty => tProd (nNamed s) d.(decl_type) ty) *)
        (*   (tProd (nNamed d) (mkApps delay_t [hole; lhs']) *)
        (*         (tProd (nNamed r_C) (mkApps R_C [hole; tVar C]) *)
        (*         (tProd (nNamed s) (mkApps St [hole; tVar C; lhs]) *)
        (*         (fn (mkApps <%@eq%> [mkApps univD [hole]; *)
        (*                             mkApps delayD [hole; lhs'; tVar d]; *)
        (*                             rule.(rLhs)]) *)
        (*         (fold_right *)
        (*           (fun '(x, x', md', xty, u) ty => *)
        (*             match md' with *)
        (*             | Some d' => fn (mkApps <%@eq%> [xty; tVar x; mkApps delayD [u; tVar x'; tVar d']]) ty *)
        (*             | None => ty *)
        (*             end) *)
        (*           (fn (fn (mkApps <%Success%> [rule_name]) *)
        (*                 (it_mkProd_or_LetIn (drop_names rhs_ctx) *)
        (*                 (tVar R))) *)
        (*               (fn (fn (mkApps <%Failure%> [rule_name]) (tVar R)) (tVar R))) *)
        (*           extra_vars))))) *)
        (*   (rev lhs_ctx)) *)
        extra_vars))))
  | dBottomup =>
    let hole := rule.(rHoleU) in
    let lhs := rule.(rLhs) in
    let rhs := rule.(rRhs) in
    let lhs_vars := rule.(rLhsVars) in
    (* Currently, the context rΓ contains (lhs vars ∪ rhs vars) in unspecified order.
       We will rearrange it to be (lhs vars .. rhs vars ..). *)
    let ctx := map (fun '(x, decl) => (member x lhs_vars, x, decl)) rule.(rΓ) in
    let '(lhs_ctx, rhs_ctx) := partition (fun '(in_lhs, _, _) => in_lhs) ctx in
    (* rhs_ctx also contains C: C will actually be introduced in the outer scope
       already. We'll just borrow its name. *)
    let! C :=
      match rule.(rC) with
      | tVar C => ret C
      | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
      end
    in
    (* Filter to drop C *)
    let rhs_ctx := filter (fun '(_, x, decl) => negb (x ==? C)) rhs_ctx in
    let! R := gensym "R" in
    let! r_C := gensym "r_C" in
    let! s := gensym "s" in
    let hole := mk_univ hole in
    let root := mk_univ root in
    let rule_name := quote_string rule.(rName) in
    ret (fn (mkApps <%ExtraVars%> [rule_name])
      (tProd (nNamed R) type0 (tProd (nNamed C) (mkApps frames_t [hole; root])
      (fold_right
        (fun '(_, s, d) ty => tProd (nNamed s) d.(decl_type) ty)
         (tProd (nNamed r_C) (mkApps R_C [hole; tVar C])
         (tProd (nNamed s) (mkApps St [hole; tVar C; lhs])
         (fn
           (fn (mkApps <%Success%> [rule_name]) (fold_right
             (fun '(_, s, d) ty => tProd (nNamed s) d.(decl_type) ty)
             (fn (mkApps R_C [hole; tVar C]) (fn (mkApps St [hole; tVar C; rhs]) (tVar R)))
             (rev rhs_ctx)))
           (fn (fn (mkApps <%Failure%> [rule_name]) (tVar R)) (tVar R)))))
        (rev lhs_ctx)))))
  end.

Definition gen_extra_vars_tys : GM (list term) :=
  mapM
    (fun r => let! ty := gen_extra_vars_ty r in indices_of [] ty)
    (* (fun r => gen_extra_vars_ty r) *)
    rules.(rRules).

End GoalGeneration.

(* ---------- Types of helpers for taking a single step ---------- *)

Section GoalGeneration.

Context
  (R_C St : term)
  (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rw_univ_i [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU))
  (* specialize to forall A, frames_t A root -> univD A -> Set *)
  (rw_for := mkApps <%@rw_for%> [
    rw_univ; HFrame; root; rw_rel; R_C; St]).

Definition gen_run_rule_ty (r : rule_t) : term. ltac1:(refine(
  let hole := mk_univ r.(rHoleU) in
  let run_rule :=
    match r.(rDir) with
    | dTopdown => <%TopdownRunRule%>
    | dBottomup => <%BottomupRunRule%>
    end
  in
  fn (mkApps run_rule [quote_string r.(rName)])
  (it_mkProd_or_LetIn (drop_names r.(rΓ))
  ((match r.(rDir) with dTopdown => fn (mkApps R_C [hole; r.(rC)]) | dBottomup => id end)
  (fn (mkApps St [hole; r.(rC); r.(rRhs)])
  (fn (mkApps rw_for [hole; r.(rC); r.(rRhs)])
  (mkApps rw_for [hole; r.(rC); r.(rLhs)])))))
)).
Defined.

Definition gen_run_rule_tys : GM (list term) :=
  mapM (fun t => indices_of [] (gen_run_rule_ty t)) rules.(rRules).

End GoalGeneration.

(* ---------- Types of helpers for incrementalizing delayed computation ---------- *)

Section GoalGeneration.

Context
  (delay_t : term)
  (delayD : term) (* specialized to forall {A}, univD A -> delay_t -> univD A *)
  (aux_data : aux_data_t)
  (typename := aux_data.(aTypename)) (g := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname)).

Definition gen_constr_delay_ty (c : string) : GM term. ltac1:(refine(
  let! '(n, children, rtyname) := findM c g.(mgChildren) in
  let! rty := findM rtyname g.(mgTypes) in
  let! '(ind, pars) := decompose_ind rty in
  let ctr := mkApps (tConstruct ind (N.to_nat n) []) pars in
  let univ_name := typename +++ "_univ" in
  let! univ_n := findM rtyname univ_of_tyname in
  let univ := tConstruct (mkInd univ_name 0) (N.to_nat univ_n) [] in
  let! children :=
    mapM
      (fun tyname =>
        let! ty := findM tyname g.(mgTypes) in
        let! old := gensym (abbreviate tyname) in
        let! univ_n := findM tyname univ_of_tyname in
        let univ := tConstruct (mkInd univ_name 0) (N.to_nat univ_n) [] in
        let atomic := member tyname g.(mgAtoms) in
        let! new := if atomic then gensym (abbreviate tyname) else gensym "d" in
        ret (tyname, old, new, ty, univ, atomic))
      children
  in
  let! R := gensym "R" in
  let! d := gensym "d" in
  let ctr_ty := fold_right (fun '(_, _, _, ty, _, _) res => fn ty res) rty children in 
  let before_delayD := mkApps ctr (map (fun '(_, old, _, _, _, _) => tVar old) children) in
  ret (fn (mkApps <%@ConstrDelay%> [ctr_ty; ctr]) (tProd (nNamed R) type0
    (fold_right
      (fun '(_, old, _, ty, _, _) res => tProd (nNamed old) ty res)
      (tProd (nNamed d) (mkApps delay_t [univ; before_delayD])
      (fn
        (fold_right
          (fun '(_, old, new, ty, univ, atomic) res =>
            tProd (nNamed new) (if (atomic : bool) then ty else mkApps delay_t [univ; tVar old]) res)
          (fn
            (mkApps <%@eq%> [rty;
               mkApps delayD [univ; before_delayD; tVar d];
               mkApps ctr (map
                 (fun '(tyname, old, new, ty, _, atomic) => 
                   if atomic : bool then tVar new
                   else
                     let n := find_d tyname 0 univ_of_tyname in
                     let univ := tConstruct (mkInd univ_name 0) (N.to_nat n) [] in
                     mkApps delayD [univ; tVar old; tVar new])
                 children)])
            (tVar R))
          children)
        (tVar R)))
      children)))
)).
Defined.

Definition gen_constr_delay_tys : GM (list term) :=
  let constrs :=
    fold_right
      (fun '(_, cs) m =>
         fold_right (fun c m => insert c tt m) m cs)
      empty
      (list_of_map g.(mgConstrs))
  in
  mapM
    (fun constr => let! ty := gen_constr_delay_ty constr in indices_of [] ty)
    (* (fun constr => let! ty := gen_constr_delay_ty constr in ret ty) *)
    (map fst (list_of_map constrs)).

End GoalGeneration.

(* ---------- Types of smart constructors ---------- *)

Section GoalGeneration.

Context
  (aux_data : aux_data_t)
  (typename := aux_data.(aTypename)) (graph := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname))
  (frames_of_constr := aux_data.(aFramesOfConstr)).
Context
  (R_C St : term) (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rules.(rUniv) [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU))
  (* specialize to univD rw_univ -> univD rw_univ -> Set *)
  (frames_t := mkApps <%@frames_t%> [rw_univ; HFrame])
  (* specialize to rw_univ -> Set *)
  (univD := mkApps <%@univD%> [rw_univ; HFrame]) 
  (* specialize to forall A, frames_t A root -> univD A -> Set *)
  (result := mkApps <%@result%> [rw_univ; HFrame; root; rw_rel; St])
  (* specialize to forall A (C : frames_t A root) (e : univD A),
       (resTree : univD A), St A C resTree ->
       C⟦e⟧ R* C⟦resTree⟧ -> result root R St C e *)
  (mk_result := mkApps <%@mk_result%> [rw_univ; HFrame; root; rw_rel; St])
  (* specialize to forall A (C : frames_t A root) (e : univD A),
       result root R St C e -> univD A *)
  (resTree := mkApps <%@resTree%> [rw_univ; HFrame; root; rw_rel; St])
  (* specialize to forall A (C : frames_t A root) (e : univD A)
       (r : result root R St C e), St A C (resTree root R St C e r) *)
  (resState := mkApps <%@resState%> [rw_univ; HFrame; root; rw_rel; St])
  (* specialize to forall A (C : frames_t A root) (e : univD A)
       (r : result root R St C e), C⟦e⟧ R* C⟦resTree root R St C e r⟧ *)
  (resProof := mkApps <%@resProof%> [rw_univ; HFrame; root; rw_rel; St])
  (* specialize to forall A, frames_t A root -> univD A -> Set *)
  (rw_for := mkApps <%@rw_for%> [
    rw_univ; HFrame; root; rw_rel; R_C; St])
  (frame_ind := mkInd (typename +++ "_frame_t") 0)
  (frame_t := tInd frame_ind [])
  (frame_cons := fun n => tConstruct frame_ind n [])
  (univ_ind := mkInd (typename +++ "_univ") 0)
  (univ_t := tInd frame_ind [])
  (univ_cons := fun n => tConstruct univ_ind n [])
  (* Specialized to forall A B C, frame_t A B -> frames_t B C -> frames_t A C *)
  (frames_cons := mkApps <%@frames_cons%> [rw_univ; frame_t]).

Definition gen_smart_constr_ty (c : string) : GM term. ltac1:(refine(
  let! '(n_constr, child_tys, rty) := findM' c graph.(mgChildren) "children" in
  let n_constr := N.to_nat n_constr in
  let! rty_term := findM' rty graph.(mgTypes) "types" in
  let! '(ind, pars) := decompose_ind rty_term in
  let constr := mkApps (tConstruct ind n_constr []) pars in
  let frames := find_d c [] frames_of_constr in
  let n_frames := map hIndex frames in
  let get_univ_of ty :=
    let! n := findM' ty univ_of_tyname "univ_of_tyname" in
    ret (univ_cons (N.to_nat n))
  in
  let! univ_rty := get_univ_of rty in
  let! xtys := mapM (fun ty => let! x := gensym (abbreviate ty) in ret (x, ty)) child_tys in
  let! xutfs :=
    mapM
      (fun '(n, (lxtys, (x, ty), rxtys)) =>
        let lxs := map fst lxtys in
        let rxs := map fst rxtys in
        let! univ := get_univ_of ty in
        let! ty_term := findM ty graph.(mgTypes) in
        ret (x, univ, ty_term, frame_cons n, lxs, rxs))
      (combine n_frames (holes_of xtys))
  in
  let! C := gensym "C" in
  let constr_ty := fold_right (fun '(_, _, ty, _, _, _) res => fn ty res) rty_term xutfs in 
  ret (fn (mkApps <%@SmartConstr%> [constr_ty; constr])
    (tProd (nNamed C) (mkApps frames_t [univ_rty; root]) 
    (fold_right
      (fun '(x, _, t, _, _, _) ty => tProd (nNamed x) t ty)
      (fold_right
        (fun '(x, u, t, f, lxs, rxs) ty =>
          fn
            (fn
              (mkApps <%@SmartConstrCase%> [
                rty_term; mkApps <%@frameD%> [
                  rw_univ; HFrame; u; univ_rty;
                  mkApps f (map tVar (lxs ++ rxs)); tVar x]])
              (fold_right
                (fun '(x', _, t, _, _, _) ty => if x ==? x' then ty else tProd (nNamed x') t ty)
                  (mkApps rw_for [
                    u; mkApps frames_cons [
                      u; univ_rty; root; 
                      mkApps f (map tVar (lxs ++ rxs)); tVar C];
                    tVar x])
                xutfs))
            ty)
        (mkApps rw_for [univ_rty; tVar C; mkApps constr (map (fun '(x, _, _, _, _, _) => tVar x) xutfs)])
        (rev xutfs))
      xutfs)))
)).
Defined.

Definition gen_smart_constr_tys : GM (list term) :=
  let constrs :=
    fold_right
      (fun '(_, cs) m =>
         fold_right (fun c m => insert c tt m) m cs)
      empty
      (list_of_map graph.(mgConstrs))
  in
  mapM
    (fun constr => let! ty := gen_smart_constr_ty constr in indices_of [] ty)
    (map fst (list_of_map constrs)).

End GoalGeneration.

(* ---------- Types of pattern matching combinators ---------- *)

Fixpoint unwords (ws : list string) : string :=
  match ws with
  | [] => ""
  | [s] => s
  | s :: ss => s +++ " " +++ unwords ss
  end.

(* Elaborate a single pattern match
     match e1, e2, .. with
     | c x (d y ..) .., pat2, .. => success
     | _ => failure
     end : ret_ty
   into the case tree
     match e with
     | c x fresh .. =>
       match fresh with
       | d y .. =>
         match e2 with
         | pat2 => ..
         | .. => failure
         end
       | ..
       | .. => failure
       end
     | ..
     | .. => failure
     end *)

Definition gen_case_tree (ind_info : ind_info) (epats : list (term × term))
           (ret_ty success failure : term) : GM term. ltac1:(refine(
  let find_ind ind := findM' ind.(inductive_mind) ind_info "find_ind" in
  let fix go F epats :=
    match F with O => raise "gen_case_tree: OOF" | S F =>
      let go := go F in
      let go_pat e ind n_constr args epats :=
        let! '(mbody, inds, _) := find_ind ind in
        let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
        let nparams := mbody.(ind_npars) in
        let pars := firstn nparams args in
        let args := skipn nparams args in
        let! constrs :=
          mapM
            (fun '(name, constr_ty, arity) =>
              let '(xs, ts, rty) := decompose_prod constr_ty in
              let xs := skipn nparams xs in
              let ts := skipn nparams ts in
              let constr_ty := fold_right (fun '(x, t) ty => tProd x t ty) rty (combine xs ts) in
              let constr_ty := subst0 (rev pars ++ rev_map (fun ind => tInd ind []) inds) constr_ty in
              let! constr_ty := named_of [] constr_ty in
              ret (name, constr_ty, arity))
            body.(ind_ctors)
        in
        tCase (ind, nparams) (tLambda nAnon (mkApps (tInd ind []) pars) ret_ty) e <$>
          mapiM_nat
            (fun i '(_, constr_ty, arity) =>
              let '(xs, ts, rty) := decompose_prod constr_ty in
              let! xs :=
                if i ==? n_constr then
                  mapM
                    (fun '(x, arg) =>
                      match x, arg with
                      | nAnon, _ => raise "gen_case_tree: name anon"
                      | _, tVar x => ret x
                      | nNamed x, _ => ret x
                      end)
                    (combine xs args)
                else
                  mapM
                    (fun x =>
                      match x with
                      | nAnon => raise "gen_case_tree: name anon"
                      | nNamed x => ret x
                      end)
                    xs
              in
              let! arm :=
                 if i ==? n_constr
                 then go (combine (map tVar xs) args ++ epats)
                 else ret failure
              in
              let arm :=
                fold_right
                  (fun '(x, t) arm => tLambda (nNamed x) t arm)
                  arm (combine xs ts)
              in
              ret (arity, arm))
            constrs
      in
      match epats with
      | [] => ret success
      | (e, tConstruct ind n_constr []) :: epats => go_pat e ind n_constr [] epats
      | (e, tApp (tConstruct ind n_constr []) args) :: epats => go_pat e ind n_constr args epats
      | (e, tVar _) :: epats => go epats
      | (_, pat) :: _ => raise ("gen_case_tree: bad pat: " +++ string_of_term pat)
      end
    end
  in go 100%nat epats
)).
Defined.

Section GoalGeneration.

Context
  (aux_data : aux_data_t)
  (typename := aux_data.(aTypename))
  (ind_info := aux_data.(aIndInfo))
  (graph := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname))
  (frames_of_constr := aux_data.(aFramesOfConstr)).
Context (delay_t : term)
        (delayD : term) (* specialized to forall {A}, univD A -> delay_t -> univD A *).
Context
  (R_C St : term) (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rw_univ_i [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU))
  (* specialize to univD rw_univ -> univD rw_univ -> Set *)
  (frames_t := mkApps <%@frames_t%> [rw_univ; HFrame])
  (* specialize to rw_univ -> Set *)
  (univD := mkApps <%@univD%> [rw_univ; HFrame]).

Definition gen_topdown_ty (t_univ_i : N) : GM term. ltac1:(refine(
  let n_univs := mfold (fun u n m => insert n u m) empty univ_of_tyname in
  let! t_tyname := findM'' t_univ_i n_univs "t_univ_i" in
  let t_univ_i := N.to_nat t_univ_i in
  let! t_ty := findM' t_tyname graph.(mgTypes) "t_tyname" in
  let! '(ind, pars) := decompose_ind t_ty in
  let! d := gensym "d" in
  let! R := gensym "R" in
  let! C := gensym "C" in
  let! e := gensym (abbreviate t_tyname) in
  let! r_C := gensym "r_C" in
  let! s := gensym "s" in
  let t_univ := mk_univ t_univ_i in
  let! constrs := findM' t_tyname graph.(mgConstrs) "t_tyname" in
  let! congruences :=
    mapM
      (fun c =>
        let! '(index, arg_tynames, rty) := findM' c graph.(mgChildren) "constr" in
        let! xts :=
          mapM
            (fun tyname =>
              let atomic := member tyname graph.(mgAtoms) in
              let abbrev_tyname := abbreviate tyname in
              let! x := gensym abbrev_tyname in
              let! x' := gensym abbrev_tyname in
              let! md := if atomic then ret None else Some <$> gensym "d" in
              let! t := findM tyname graph.(mgTypes) in
              let! univ_n := findM tyname univ_of_tyname in
              let u := mk_univ (N.to_nat univ_n) in
              ret (md, x, x', t, u))
            arg_tynames
        in
        let! rty := findM rty graph.(mgTypes) in
        let constr := mkApps (tConstruct ind (N.to_nat index) []) pars in
        let constr_ty := fold_right (fun '(_, _, _, t, _) res => fn t res) rty xts in
        let pat := mkApps constr (map (fun '(_, x, _, _, _) => tVar x) xts) in
        let! header :=
          gen_case_tree ind_info [(tVar e, pat)] type0
            (mkApps <%@Congruence%> [constr_ty; constr])
            <%Impossible%>
        in
        ret (fn (mkApps <%@InspectCaseCongruence%> [constr_ty; constr]) (fn header
          (fold_right
            (fun '(md, x, x', t, u) ty =>
              tProd (nNamed x) t
              (match md with
               | Some d => tProd (nNamed d) (mkApps delay_t [u; tVar x]) ty
               | None => tProd (nNamed x') t ty
               end))
            (fn
              (mkApps <%@eq%> [rty;
                mkApps delayD [t_univ; tVar e; tVar d];
                mkApps constr (map
                  (fun '(md, x, x', t, u) =>
                    match md with
                    | None => tVar x'
                    | Some d => mkApps delayD [u; tVar x; tVar d]
                    end)
                  xts)])
              (fn
                (mkApps <%@eq%> [rty; 
                  tVar e;
                  mkApps constr (map (fun '(md, x, x', t, u) => tVar x) xts)])
                (tVar R)))
            xts))))
      constrs
  in
  let applicable :=
    filter
      (fun r => match r.(rDir) with dTopdown => r.(rHoleU) ==? t_univ_i | dBottomup => false end)
      rules.(rRules)
  in
  let! applicable :=
    mapM
      (fun r =>
        (* We can't reuse the trick of borrowing the name for C, because this type will have
           multiple continuations corresponding to multiple rules with different names for C.
           So in each rule we have to replace its personal name for C with the C in the outer
           scope. *)
        let! localC :=
          match r.(rC) with
          | tVar C => ret C
          | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
          end
        in
        let rΓ := filter (fun '(x, decl) => negb (x ==? localC)) r.(rΓ) in
        let σ := sing localC C in
        let rΓ := map (on_snd (map_decl (rename σ))) rΓ in
        let! '(extra_vars, σ) :=
          let Γ := map_of_list rΓ in
          mfoldM
            (fun x 'tt '(extras, σ) =>
              let! x' := gensym (remove_sigils' x) in
              let! md' := if member x r.(rSpecialVars) then Some <$> gensym "d" else ret None in
              let! decl := findM' x Γ "special_var" in
              let ty := decl.(decl_type) in
              let! tyname := mangle ind_info ty in
              let! univ_n := findM' tyname univ_of_tyname "applicable: univ_n" in
              let u := mk_univ (N.to_nat univ_n) in
              ret ((x, x', md', ty, u) :: extras, insert x x' σ))
            ([], empty) (r.(rLhsVars) ∪ r.(rSpecialVars))
        in
        let old_lhs := rename σ r.(rLhs) in
        let! header :=
          gen_case_tree ind_info [(tVar e, r.(rLhs))] type0 
            (mkApps <%Active%> [quote_string r.(rName)])
            <%Impossible%>
        in
        ret (fn (mkApps <%InspectCaseRule%> [quote_string r.(rName)]) (fn header
          (it_mkProd_or_LetIn (drop_names rΓ)
          (fold_right
            (fun '(x, x', md', xty, u) ty =>
              tProd (nNamed x') xty
              (match md' with
               | Some d' => tProd (nNamed d') (mkApps delay_t [u; tVar x']) ty
               | None => ty
               end))
            (fn (mkApps <%@eq%> [mkApps univD [t_univ]; mkApps delayD [t_univ; tVar e; tVar d]; r.(rLhs)])
            (fold_right
              (fun '(x, x', md', xty, u) ty =>
                match md' with
                | Some d' => fn (mkApps <%@eq%> [xty; tVar x; mkApps delayD [u; tVar x'; tVar d']]) ty
                | None => ty
                end)
              (fn (mkApps <%@eq%> [mkApps univD [t_univ]; tVar e; old_lhs])
              (fn (mkApps R_C [t_univ; tVar C]) (fn (mkApps St [t_univ; tVar C; r.(rRhs)]) (tVar R))))
              extra_vars))
            extra_vars)))))
      applicable
  in
  ret (fn (mkApps <%@Topdown%> [rw_univ; t_univ])
    (tProd (nNamed R) type0 (tProd (nNamed C) (mkApps frames_t [t_univ; root])
    (tProd (nNamed e) (mkApps univD [t_univ])
    (tProd (nNamed d) (mkApps delay_t [t_univ; tVar e])
    (tProd (nNamed r_C) (mkApps R_C [t_univ; tVar C]) 
    (tProd (nNamed s) (mkApps St [t_univ; tVar C; mkApps delayD [t_univ; tVar e; tVar d]])
    (fold_right fn (fold_right fn (tVar R) congruences) applicable))))))))
)).
Defined.

Definition gen_bottomup_ty (t_univ_i : N) : GM term. ltac1:(refine(
  let n_univs := mfold (fun u n m => insert n u m) empty univ_of_tyname in
  let! t_tyname := findM'' t_univ_i n_univs "t_univ_i" in
  let t_univ_i := N.to_nat t_univ_i in
  let! t_ty := findM' t_tyname graph.(mgTypes) "t_tyname" in
  let! '(ind, pars) := decompose_ind t_ty in
  let! R := gensym "R" in
  let! C := gensym "C" in
  let! e := gensym (abbreviate t_tyname) in
  let! r_C := gensym "r_C" in
  let! s := gensym "s" in
  let t_univ := mk_univ t_univ_i in
  let! constrs := findM' t_tyname graph.(mgConstrs) "t_tyname" in
  let applicable :=
    filter
      (fun r => match r.(rDir) with dBottomup => r.(rHoleU) ==? t_univ_i | dTopdown => false end)
      rules.(rRules)
  in
  let! applicable :=
    mapM
      (fun r =>
        let! localC :=
          match r.(rC) with
          | tVar C => ret C
          | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
          end
        in
        let rΓ := filter (fun '(x, decl) => negb (x ==? localC)) r.(rΓ) in
        let σ := sing localC C in
        let rΓ := map (on_snd (map_decl (rename σ))) rΓ in
        let! header :=
          gen_case_tree ind_info [(tVar e, r.(rLhs))] type0 
            (mkApps <%Active%> [quote_string r.(rName)])
            <%Impossible%>
        in
        ret (fn (mkApps <%InspectCaseRule%> [quote_string r.(rName)]) (fn header
          (it_mkProd_or_LetIn (drop_names rΓ)
          (fn (mkApps <%@eq%> [mkApps univD [t_univ]; tVar e; r.(rLhs)])
          (fn (mkApps St [t_univ; tVar C; r.(rRhs)]) (tVar R)))))))
      applicable
  in
  ret (fn (mkApps <%@Bottomup%> [rw_univ; t_univ])
    (tProd (nNamed R) type0 (tProd (nNamed C) (mkApps frames_t [t_univ; root])
    (tProd (nNamed e) (mkApps univD [t_univ])
    (tProd (nNamed r_C) (mkApps R_C [t_univ; tVar C]) 
    (tProd (nNamed s) (mkApps St [t_univ; tVar C; tVar e])
    (fold_right fn (fn (fn <%Fallback%> (tVar R)) (tVar R)) (rev applicable))))))))
)).
Defined.

Definition gen_inspect_tys : GM (list term × list term). ltac1:(refine(
  let! ns :=
    foldrM
      (fun '(ty, _) ns =>
        if member ty graph.(mgAtoms) then ret ns else
        let! n := findM ty univ_of_tyname in
        ret (n :: ns))
      [] (list_of_map graph.(mgTypes))
  in
  let! tynames :=
    foldrM
      (fun '(ty, _) ns =>
        if member ty graph.(mgAtoms) then ret ns else
        ret (ty :: ns))
      [] (list_of_map graph.(mgTypes))
  in
  let! topdown_named := mapM gen_topdown_ty ns in
  let! bottomup_named := mapM gen_bottomup_ty ns in
  let! topdown_tys := mapM (indices_of []) topdown_named in
  let! bottomup_tys := mapM (indices_of []) bottomup_named in
  ret (topdown_tys, bottomup_tys)
)).
Defined.

End GoalGeneration.

(* ---------- Toplevel tactic to generate the above ---------- *)

Section GoalGeneration.

Context (aux : aux_data_t) (delay_t delayD R_C St : term) (rules : rules_t).

Definition gen_all : GM (RwObligations term). ltac1:(refine(
  let! extra_vars := gen_extra_vars_tys aux delay_t delayD R_C St rules in
  let! run_rules := gen_run_rule_tys R_C St rules in
  let! constr_delays := gen_constr_delay_tys delay_t delayD aux in
  let! smart_constrs := gen_smart_constr_tys aux R_C St rules in
  let! '(topdowns, bottomups) := gen_inspect_tys aux delay_t delayD R_C St rules in
  ret (mk_obs extra_vars run_rules constr_delays smart_constrs topdowns bottomups)
)).
Defined.

(* Danger: once invoked [unquote_all] generates universe constraints between the things inside each
   typed_term and pretty common monomorphic types like [list], [pair], [option], etc.
   It's safer to unquote each term in obs with ltac. *)
Definition unquote_all (obs : RwObligations term)
 : TemplateMonad (RwObligations typed_term). ltac1:(refine(
  let '(mk_obs extra_vars run_rules constr_delays smart_constrs topdowns bottomups) :=
    obs
  in
  extra_vars <- monad_map tmUnquote extra_vars ;;
  run_rules <- monad_map tmUnquote run_rules ;;
  constr_delays <- monad_map tmUnquote constr_delays ;;
  smart_constrs <- monad_map tmUnquote smart_constrs ;;
  topdowns <- monad_map tmUnquote topdowns ;;
  bottomups <- monad_map tmUnquote bottomups ;;
  ret (mk_obs extra_vars run_rules constr_delays smart_constrs topdowns bottomups)
)).
Defined.

End GoalGeneration.

Ltac unquote_and_assert_terms terms k :=
  lazymatch terms with
  | [] => k tt
  | ?t :: ?rest =>
    run_template_program (tmUnquote t) ltac:(fun t' =>
    match t' with
    | {| my_projT2 := ?t'' |} => assert t''; [|unquote_and_assert_terms rest k]
    end)
  end.

Ltac unquote_and_assert_obs obs k :=
  lazymatch obs with
  | mk_obs ?extra_vars ?run_rules ?constr_delays ?smart_constrs ?topdowns ?bottomups =>
    unquote_and_assert_terms extra_vars ltac:(fun _ =>
    unquote_and_assert_terms run_rules ltac:(fun _ =>
    unquote_and_assert_terms constr_delays ltac:(fun _ =>
    unquote_and_assert_terms smart_constrs ltac:(fun _ =>
    unquote_and_assert_terms topdowns ltac:(fun _ =>
    unquote_and_assert_terms bottomups k)))))
  end.

Ltac mk_rw_obs k :=
  lazymatch goal with
  | |- @rewriter ?U ?HFrame ?HAux ?root ?R ?D ?HDelay ?R_C ?St _ _ =>
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      delay_t <- tmQuote D ;;
      delayD <- tmQuote (@delayD U HFrame D HDelay) ;;
      R_C' <- tmQuote (@R_C) ;;
      St' <- tmQuote (@St) ;;
      ret (delay_t, delayD, R_C', St')) ltac:(fun pack =>
    lazymatch pack with
    | (?delay_t, ?delayD, ?R_C', ?St') =>
      runGM n (
        let! delay_t' := named_of [] delay_t in
        let! delayD' := named_of [] delayD in
        let! R_C'' := named_of [] R_C' in
        let! St'' := named_of [] St' in
        gen_all HAux delay_t' delayD' R_C'' St'' rules) ltac:(fun qobs n =>
        unquote_and_assert_obs qobs k)
        (* run_template_program (unquote_all qobs) k) *)
    end))
  end.

Ltac mk_rw' := mk_rw_obs ltac:(fun _ => idtac).

Ltac mk_smart_constr_children root R_C St s hasHrel Hrel :=
  lazymatch goal with
  | H : SmartConstrCase (frameD ?frame ?hole) -> _ |- _ =>
    specialize (H (MkSmartConstrCase _));
    let x := fresh "x" in
    let s' := fresh "s" in
    let Hrel' := fresh "Hrel" in
    edestruct H as [x s' Hrel'];
    [eapply (@preserve_R _ _ root R_C _); cbn; eassumption
    |eapply (@preserve_S_dn _ _ root St _); cbn; eassumption
    |idtac];
    clear H; clear s;
    apply (@preserve_S_up _ _ root St _) in s'; cbn in s';
    lazymatch hasHrel with
    | false => idtac
    | true => apply (rt_trans _ _ _ _ _ Hrel) in Hrel'; clear Hrel
    end;
    mk_smart_constr_children root R_C St s' true Hrel'
  | _ =>
    lazymatch hasHrel with
    | false => econstructor; [exact s|apply rt_refl]
    | true => econstructor; [exact s|exact Hrel]
    end
  end.
Ltac mk_smart_constr :=
   clear;
   let C := fresh "C" in
   let r_C := fresh "r_C" in
   let s := fresh "s" in
   intros _ C; intros;
   lazymatch goal with
   | |- @rw_for _ _ ?root _ ?R_C ?St _ _ _ =>
     unfold rw_for in *; intros r_C s;
     mk_smart_constr_children root R_C St s false None
   end.

(* TODO: hack to get constr given the name of the rule *)
Definition tm_get_constr (s : string) : TemplateMonad typed_term :=
  ref <- tmAbout s ;;
  match ref with
  | Some (ConstructRef ind n) => tmUnquote (tConstruct ind n [])
  | _ => tmFail ("tm_get_constr: not a constructor: " +++ s)
  end.

Ltac mk_run_rule :=
  lazymatch goal with
  | |- TopdownRunRule ?rule -> _ =>
    clear;
    intros;
    let r_C := fresh "r_C" in
    let s := fresh "s" in
    let Hnext := fresh "Hnext" in
    lazymatch goal with H1 : _, H2 : _, H3 : _ |- _ => revert H1 H2 H3 end;
    unfold rw_for; intros r_C s Hnext _ _;
    let x' := fresh "x'" in
    let s' := fresh "s'" in
    let Hrel := fresh "Hrel" in
    destruct (Hnext r_C s) as [x' s' Hrel];
    econstructor; [exact s'|];
    eapply rt_trans; [eapply rt_step|exact Hrel];
    run_template_program (tm_get_constr rule) ltac:(fun ctor =>
    match ctor with
    | {| my_projT2 := ?ctor' |} =>
      eapply ctor';
      lazymatch goal with
      (* | |- When _ => exact I  *)
      | _ => eassumption
      end
    end)
  | |- BottomupRunRule ?rule -> _ =>
    clear;
    intros;
    let r_C := fresh "r_C" in
    let s := fresh "s" in
    let Hnext := fresh "Hnext" in
    lazymatch goal with H1 : _, H2 : _ |- _ => revert H1 H2 end;
    unfold rw_for; intros s Hnext r_C _;
    let x' := fresh "x'" in
    let s' := fresh "s'" in
    let Hrel := fresh "Hrel" in
    destruct (Hnext r_C s) as [x' s' Hrel];
    econstructor; [exact s'|];
    eapply rt_trans; [eapply rt_step|exact Hrel];
    run_template_program (tm_get_constr rule) ltac:(fun ctor =>
    match ctor with
    | {| my_projT2 := ?ctor' |} =>
      eapply ctor';
      lazymatch goal with
      (* | |- When _ => exact I  *)
      | _ => eassumption
      end
    end)
  end.

(* Used by mk_topdown *)
Inductive Sentinel := MkSentinel. 
Ltac strip_one_match :=
  lazymatch goal with
  | H : InspectCaseRule _ -> match ?e with _ => _ end -> _ |- _ =>
    let Heqn := fresh "Heqn" in
    destruct e eqn:Heqn;
    repeat lazymatch goal with
    | H : InspectCaseRule _ -> Impossible -> _ |- _ => clear H
    | H : InspectCaseCongruence _ -> Impossible -> _ |- _ => clear H
    end
  | H : InspectCaseCongruence _ -> match ?e with _ => _ end -> _ |- _ =>
    let Heqn := fresh "Heqn" in
    destruct e eqn:Heqn;
    repeat lazymatch goal with
    | H : InspectCaseRule _ -> Impossible -> _ |- _ => clear H
    | H : InspectCaseCongruence _ -> Impossible -> _ |- _ => clear H
    end
  end.
Ltac mk_topdown_congruence :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active _ -> _ |- _ => fail
  | H : InspectCaseCongruence _ -> Congruence ?constr -> _, Hdelay : ConstrDelay ?constr -> _ |- _ =>
    eapply (Hdelay (MkConstrDelay constr)); intros;
    eapply (H (MkInspectCaseCongruence constr) (MkCongruence constr));
    solve [eassumption|reflexivity]
  end.
Ltac mk_topdown_active r_C s :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active ?rule -> _, Hextras : ExtraVars ?rule -> _ |- _ =>
    eapply (Hextras (MkExtraVars rule));
    [(* Find all the misc. arguments by unification *) eassumption ..
    |(* Success continuation: add rhs vars + assumptions above the line *)
     intros _; intros
    |(* Failure continuation: forget everything about the rule we just applied *)
     intros _; clear Hextras H];
    [(* Success: switch to new env + state and apply the proper rule *)
     lazymatch goal with
     | H1 : _ , H2 : _ |- _ =>
       clear r_C s; rename H1 into r_C, H2 into s;
       eapply (H (MkInspectCaseRule rule) (MkActive rule)); [..|reflexivity|exact r_C|exact s];
       eassumption
     end
    |(* Failure: try to apply other rules *)
      mk_topdown_active r_C s]
  | _ => mk_topdown_congruence
  end.
Ltac mk_topdown :=
  repeat lazymatch goal with
  | H : Topdown -> _ |- _ => clear H
  | H : SmartConstr _ -> _ |- _ => clear H
  end;
  let d := fresh "d" in
  let R := fresh "R" in
  let C := fresh "C" in
  let e := fresh "e" in
  let r_C := fresh "r_C" in
  let s := fresh "s" in
  intros _ R C e d r_C s; intros;
  repeat strip_one_match;
  mk_topdown_active r_C s.

Ltac mk_bottomup_fallback :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active _ -> _ |- _ => fail
  | H : Fallback -> _ |- _ => exact (H MkFallback)
  end.
Ltac mk_bottomup_active :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active ?rule -> _, Hextras : ExtraVars ?rule -> _ |- _ =>
    eapply (Hextras (MkExtraVars rule));
    [eassumption..|intros _; intros|intros _; clear Hextras H];
    [eapply (H (MkInspectCaseRule rule) (MkActive rule)); eauto
    (* TODO: eassumption not sufficient because sometimes need reflexivity? *)
    |mk_bottomup_active]
  | _ => mk_bottomup_fallback
  end.
Ltac mk_bottomup :=
  repeat lazymatch goal with
  | H : Topdown -> _ |- _ => clear H
  | H : Bottomup -> _ |- _ => clear H
  | H : SmartConstr _ -> _ |- _ => clear H
  end;
  let R := fresh "R" in
  let C := fresh "C" in
  let e := fresh "e" in
  let r := fresh "r" in
  let s := fresh "s" in
  intros _ R C e r s; intros;
  repeat strip_one_match;
  mk_bottomup_active.

Ltac try_find_constr e k_constr k_atom :=
  lazymatch goal with
  | H : SmartConstr e -> _ |- _ => k_constr e H
  | _ =>
    lazymatch e with
    | ?e' _ => try_find_constr e' k_constr k_atom
    | _ => k_atom e
    end
  end.
Ltac next_action e k_rec k_constr k_atom :=
  lazymatch e with
  | Rec ?e' => k_rec e'
  | _ => try_find_constr e k_constr k_atom
  end.

Ltac mk_edit_rhs recur univ HFrame root R delay_t HD R_C St :=
  let rec go _ :=
    lazymatch goal with
    | |- @rw_for _ _ _ _ _ _ _ _ ?e =>
      next_action e 
        (* Recursive calls: *)
        ltac:(fun e' =>
          match e' with
          (* If the recursive call is on a variable... *)
          | ?x =>
            is_var x;
            (* ...and the variable is the delayed version of some other variable... *)
            match goal with
            | H : x = delayD _ ?d |- _ =>
              (* ...then we can recur with d to save a tree traversal *)
              rewrite H;
              apply (recur _ _ _ d)
            end
          (* If recursive call on arbitrary function call with variable as last argument... *)
          | ?f ?x =>
            is_var x;
            (* ...and the variable is the delayed version of some other expression... *)
            match goal with
            | H : x = @delayD ?U ?HFrame ?D ?HD ?univ ?y ?d |- _ =>
              (* idtac "can fuse" f x "with" U HFrame D HD univ y d; *)
              (* ...then we can ask the user to prove a fusion law and use it to save a call to f: *)
              let r_C := fresh "r_C" in
              let s := fresh "s" in
              intros r_C s;
              let Hfuse := fresh "Hfuse" in
              assert (Hfuse : {d' : @D univ y |
                f (@delayD U HFrame D HD univ y d) = @delayD U HFrame D HD univ y d'});
              [|let r_C' := fresh "r_C" in
                let s' := fresh "s" in
                let r_Cty := type of r_C in
                let sty := type of s in
                (assert (r_C' : r_Cty) by exact r_C);
                (assert (s' : sty) by exact s);
                revert r_C' s'; clear r_C s;
                let Hd' := fresh "Hd" in
                let d' := fresh "d" in
                destruct Hfuse as [d' Hd'];
                rewrite H, Hd';
                apply (recur _ _ _ d')]
            end
          (* If recursive call isn't on a variable at all, recur with the identity delay *)
          | _ =>
            lazymatch goal with
            | |- @rw_for _ _ _ _ _ _ _ ?C _ =>
              let hole :=
                lazymatch type of C with
                | @frames_t _ _ ?hole _ => hole
                | @frames_t' univ _ ?hole _ => hole
                end
              in
              rewrite <- (@delay_id_law univ HFrame delay_t HD hole e');
              apply (recur _ _ _ (@delay_id univ HFrame delay_t HD hole e'))
            end
          end)
        (* Constructor nodes: apply the smart constructor... *)
        ltac:(fun constr Hconstr =>
          apply (Hconstr (MkSmartConstr constr));
          (* ...and recursively expand each child *)
          intros; go tt)
        (* Atoms: just return the atom *)
        ltac:(fun e => apply (@rw_id univ HFrame root R R_C St))
    end
  in go tt.

Ltac mk_rewriter :=
  lazymatch goal with
  | |- @rewriter ?univ ?HFrame _ ?root ?R ?delay_t ?HD ?R_C ?St _ _ =>
    unfold rewriter;
    lazymatch goal with
    | |- Rewriting.Fuel -> ?T =>
      let recur := fresh "recur" in
      let A := fresh "A" in
      apply (@Fuel_Fix T); [apply (@rw_base univ _ root _ delay_t HD R_C St)|];
      intros recur A; destruct A;
      lazymatch goal with
      (* Nonatomic children *)
      | Htopdown : Topdown ?hole -> _ |- forall _ : frames_t ?hole _, _ =>
        let C := fresh "C" in
        let e := fresh "e" in
        let d := fresh "d" in
        intros C e d;
        eapply (@rw_chain univ HFrame root R delay_t HD R_C St);
        [(* Topdown *)
         let r_C := fresh "r_C" in
         let s := fresh "s" in
         intros r_C s;
         let r_C' := fresh "r_C" in
         let s' := fresh "s" in
         let r_Cty := type of r_C in
         let sty := type of s in
         (assert (r_C' : r_Cty) by exact r_C);
         (assert (s' : sty) by exact s);
         revert r_C' s';
         change (@rw_for univ _ root R R_C St _ C (delayD e d));
         apply (Htopdown (MkTopdown hole) _ C e d r_C s);
         clear r_C s;
         lazymatch goal with
         (* Rule applications *)
         | Hrun : TopdownRunRule ?rule -> _ |- InspectCaseRule ?rule -> _ =>
           intros _ _; intros;
           lazymatch goal with He : delayD e d = _ |- _ => rewrite He end;
           let r_C'' := fresh "r_C" in
           let s'' := fresh "s" in
           lazymatch goal with H1 : _, H2 : _ |- _ => rename H1 into r_C'', H2 into s'' end;
           eapply (Hrun (MkTopdownRunRule rule));
           [idtac..|exact r_C''|exact s''|idtac];
           [try eassumption..|mk_edit_rhs recur univ HFrame root R delay_t HD R_C St]
         (* Congruence cases *)
         | Hconstr : SmartConstr ?constr -> _ |- InspectCaseCongruence ?constr -> _ =>
           intros _ _; intros;
           lazymatch goal with Hdelay : delayD e d = _ |- _ => rewrite Hdelay end;
           apply (Hconstr (MkSmartConstr constr));
           intros;
           lazymatch goal with
           (* If child is nonatomic (has call to delayD), recur *)
           | |- @rw_for _ _ _ _ _ _ _ _ (delayD _ _) =>
             apply recur
           (* Otherwise, just return it *)
           | |- @rw_for _ _ _ _ _ _ _ _ _ =>
             apply (@rw_id univ HFrame root R R_C St)
           end
         end
        |(* Bottomup *)
         lazymatch goal with
         | Hbottomup : Bottomup hole -> _ |- _ =>
           clear d e; intros e;
           let r_C := fresh "r_C" in
           let s := fresh "s" in
           intros r_C s;
           let r_C' := fresh "r_C" in
           let s' := fresh "s" in
           let r_Cty := type of r_C in
           let sty := type of s in
           (assert (r_C' : r_Cty) by exact r_C);
           (assert (s' : sty) by exact s);
           revert r_C' s';
           change (@rw_for univ _ root R R_C St _ C e);
           apply (Hbottomup (MkBottomup hole) _ C e r_C s);
           clear r_C s;
           lazymatch goal with
           (* Rule applications *)
           | Hrun : BottomupRunRule ?rule -> _ |- InspectCaseRule ?rule -> _ =>
             intros _ _; intros;
             lazymatch goal with He : e = _ |- _ => rewrite He end;
             (* Run the rule... *)
             let s'' := fresh "s" in
             lazymatch goal with H : _ |- _ => rename H into s'' end;
             eapply (Hrun (MkBottomupRunRule rule));
             [idtac..|exact s''|idtac];
             (* ...and then just return the modified tree *)
             [try eassumption..|apply (@rw_id univ HFrame root R R_C St)]
           (* Fallback (just return the child) *)
           | |- Fallback -> _ =>
             intros _;
             apply (@rw_id univ HFrame root R R_C St)
           end
         end]
      (* Atomic children: just run the delayed computation *)
      | |- forall _ : frames_t ?hole _, _ =>
        let C := fresh "C" in
        let e := fresh "e" in
        let d := fresh "d" in
        intros C e d;
        apply (@rw_base univ HFrame root R delay_t HD R_C St _ _ _ d)
      end
    end
  end.


(* Like mk_rw', but apply the default automation and only leave behind nontrivial goals *)
Ltac mk_rw :=
  mk_rw';
  lazymatch goal with
  | |- SmartConstr _ -> _ => mk_smart_constr
  | |- TopdownRunRule _ -> _ => mk_run_rule
  | |- BottomupRunRule _ -> _ => mk_run_rule
  | |- Topdown _ -> _ => mk_topdown
  | |- Bottomup _ -> _ => mk_bottomup
  | _ => idtac
  end;
  [..|mk_rewriter].

Ltac mk_easy_delay :=
  try lazymatch goal with
  | |- ConstrDelay _ -> _ =>
    clear; simpl; intros; lazymatch goal with H : forall _, _ |- _ => eapply H; try reflexivity; eauto end
  end.

Ltac cond_failure :=
  lazymatch goal with
  | H : Failure ?rule -> ?R |- ?R =>
    apply (H (MkFailure rule))
  end.

Ltac cond_success name :=
  lazymatch goal with
  | Hs : Success ?rule -> _, Hf : Failure ?rule -> _ |- ?R =>
    specialize (Hs (MkSuccess rule)); clear Hf; rename Hs into name
  end.
