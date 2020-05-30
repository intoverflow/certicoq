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

Require Export CertiCoq.L6.Rewriting.

Instance Monad_TemplateMonad : Monad TemplateMonad := {
  ret _ := TM.ret;
  bind _ _ := TM.bind }.

Notation "'let!' x ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).
Notation "'let!' ' p ':=' c1 'in' c2" :=
  (@bind _ _ _ _ c1 (fun x => match x with p => c2 end))
  (at level 61, p pattern, c1 at next level, right associativity).
Infix "<$>" := fmap (at level 52, left associativity).
Infix "<*>" := ap (at level 52, left associativity).

Section Helpers.

Context {M : Type -> Type} {A B : Type} `{Monad M}.

Definition mapM (f : A -> M B) : list A -> M (list B) :=
  fix go xs :=
    match xs with
    | [] => pure []
    | x :: xs => pure cons <*> f x <*> go xs
    end.

Definition mapi' (f : nat -> A -> B) : list A -> list B :=
  (fix go n xs :=
    match xs with
    | [] => []
    | x :: xs => f n x :: go (S n) xs
    end) O.

Definition mapiM (f : N -> A -> M B) : list A -> M (list B) :=
  (fix go n xs :=
    match xs with
    | [] => pure []
    | x :: xs => pure cons <*> f n x <*> go (1 + n) xs
    end) 0.

Definition mapiM_nat (f : nat -> A -> M B) : list A -> M (list B) :=
  (fix go n xs :=
    match xs with
    | [] => pure []
    | x :: xs => pure cons <*> f n x <*> go (S n) xs
    end) O.

Definition foldrM (f : A -> B -> M B) (e : B) (xs : list A) : M B :=
  fold_right (fun x m => let! y := m in f x y) (ret e) xs.

Definition foldlM (f : B -> A -> M B) (x : B) : list A -> M B :=
  let fix go acc xs :=
    match xs with
    | [] => ret acc
    | x :: xs =>
      let! acc := f acc x in
      go acc xs
    end
  in go x.

Definition foldri {A B} (f : N -> A -> B -> B) (g : N -> B) : list A -> B :=
  let fix go n xs :=
    match xs with
    | [] => g n
    | x :: xs => f n x (go (1 + n) xs)
    end
  in go 0.

Definition foldri_nat {A B} (f : nat -> A -> B -> B) (g : nat -> B) : list A -> B :=
  let fix go n xs :=
    match xs with
    | [] => g n
    | x :: xs => f n x (go (S n) xs)
    end
  in go O.

Definition foldli (f : N -> B -> A -> B) (x : B) : list A -> B :=
  let fix go n acc xs :=
    match xs with
    | [] => acc
    | x :: xs =>
      let acc := f n acc x in
      go (1 + n) acc xs
    end
  in go 0 x.

Definition foldriM (f : N -> A -> B -> M B) (x : B) : list A -> M B :=
  let fix go n xs :=
    match xs with
    | [] => ret x
    | x :: xs => let! y := go (1 + n) xs in f n x y
    end
  in go 0.

Definition foldriM_nat (f : nat -> A -> B -> M B) (x : B) : list A -> M B :=
  let fix go n xs :=
    match xs with
    | [] => ret x
    | x :: xs => let! y := go (S n) xs in f n x y
    end
  in go O.

Definition foldliM (f : N -> B -> A -> M B) (x : B) : list A -> M B :=
  let fix go n acc xs :=
    match xs with
    | [] => ret acc
    | x :: xs =>
      let! acc := f n acc x in
      go (1 + n) acc xs
    end
  in go 0 x.

End Helpers.

(* -------------------- Finite maps -------------------- *)

Notation "'Eq' A" := (RelDec (@eq A)) (at level 1, no associativity).
Infix "==?" := eq_dec (at level 40, no associativity).

Instance Eq_N : Eq N := {rel_dec := N.eqb}.

Definition Map A B := list (A * B).
Definition Set' A := Map A unit.

Definition empty {A B} : Map A B := [].

Definition sing {A B} k v : Map A B := [(k, v)].

Definition size {A B} (m : Map A B) : nat := #|m|.

Definition insert {A B} k v m : Map A B := (k, v) :: m.

Definition delete {A B} `{Eq A} k : Map A B -> Map A B :=
 filter (fun '(k', _) => negb (k ==? k')).

Fixpoint find {A B} `{Eq A} k m : option B :=
  match m with
  | [] => None
  | (k', v) :: m => if k ==? k' then Some v else find k m
  end.

Fixpoint find_d {A B} `{Eq A} k d m : B :=
  match m with
  | [] => d
  | (k', v) :: m => if k ==? k' then v else find_d k d m
  end.

Definition find_exc {M E A B} `{Eq A} `{Monad M} `{MonadExc E M} k m e : M B :=
  match find k m with
  | Some v => ret v
  | None => raise e
  end.

Definition update {A B} `{Eq A} k (f : B -> B) d m : Map A B :=
  insert k (f (find_d k d m)) m.

Definition list_of_map {A B} : Map A B -> list (A * B) := id.

Definition map_of_list {A B} : list (A * B) -> Map A B := id.
Definition set_of_list {A} (xs : list A) : Set' A := map_of_list (map (fun x => (x, tt)) xs).
Definition list_of_set {A} : Set' A -> list A := map fst.
Definition set_of_option {A} (x : option A) : Set' A :=
  match x with
  | Some x => sing x tt
  | None => empty
  end.

Definition map_of_ilist {A} : list A -> Map N A :=
  let fix go n xs :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: go (1 + n) xs
    end
  in go 0.

Definition subset {A B} `{Eq A} `{Eq B} (m1 m2 : Map A B) : bool :=
  forallb
    (fun '(k1, v1) =>
       existsb
         (fun '(k2, v2) =>
            if k1 ==? k2
            then v1 ==? v2
            else false)
         m2)
    m1.

Definition mmap {A B C} (f : B -> C) : Map A B -> Map A C :=
  fix go m :=
    match m with
    | [] => []
    | (k, x) :: m => (k, f x) :: go m
    end.

Definition mkmap {A B C} (f : A -> B -> C) : Map A B -> Map A C :=
  fix go m :=
    match m with
    | [] => []
    | (k, x) :: m => (k, f k x) :: go m
    end.

Definition mfold {A B C} (f : A -> B -> C -> C) (e : C) : Map A B -> C :=
  fix go m :=
    match m with
    | [] => e
    | (k, x) :: m => f k x (go m)
    end.

Definition mfoldM {M A B C} `{Monad M} (f : A -> B -> C -> M C) (e : C) : Map A B -> M C :=
  fix go m :=
    match m with
    | [] => ret e
    | (k, x) :: m => let! r := go m in f k x r
    end.

Definition mmapM {M A B C} `{Monad M} (f : B -> M C) : Map A B -> M (Map A C) :=
  fix go m :=
    match m with
    | [] => ret []
    | (k, x) :: m => cons <$> (pair k <$> f x) <*> go m
    end.

Definition mchoose {A B} (m : Map A B) : option (A * B) :=
  match m with
  | [] => None
  | kv :: _ => Some kv
  end.

Definition member {A B} `{Eq A} k (m : Map A B) : bool := if find k m then true else false.

Definition intersect {A B C} `{Eq A} (m1 : Map A B) (m2 : Map A C) : Map A B :=
  filter (fun '(x, _) => if find x m2 then true else false) m1.
(* Definition union {A B} (m1 m2 : Map A B) := m1 ++ m2. *)
Definition union {A B} `{Eq A} (m1 m2 : Map A B) := m1 ++ filter (fun '(x, _) => if find x m1 then false else true) m2.
Infix "∪" := union (at level 50, left associativity).
Infix "∩" := intersect (at level 50, left associativity).

Definition minus {A B C} `{Eq A} (m1 : Map A B) (m2 : Map A C) : Map A B :=
  filter (fun '(x, _) => if find x m2 then false else true) m1.
Infix "\" := minus (at level 50, left associativity).

Definition union_all {A B} `{Eq A} : list (Map A B) -> Map A B := fold_right union empty.

Definition intersect_by {A B C} `{Eq A} (f : A -> B -> B -> option C) (m1 m2 : Map A B) : Map A C :=
  fold_right
   (fun '(k, v1) acc =>
      match find k m2 with
      | Some v2 => match f k v1 v2 with Some c => (k, c) :: acc | None => acc end
      | None => acc
      end)
   [] m1.

(* -------------------- Context generation -------------------- *)

(* Reverse hex *)
Fixpoint string_of_positive n :=
  match n with
  | xH => "1"
  | xO xH => "2"
  | xI xH => "3"
  | xO (xO xH) => "4"
  | xI (xO xH) => "5"
  | xO (xI xH) => "6"
  | xI (xI xH) => "7"
  | xO (xO (xO xH)) => "8"
  | xI (xO (xO xH)) => "9"
  | xO (xI (xO xH)) => "A"
  | xI (xI (xO xH)) => "B"
  | xO (xO (xI xH)) => "C"
  | xI (xO (xI xH)) => "D"
  | xO (xI (xI xH)) => "E"
  | xI (xI (xI xH)) => "F"
  | xO (xO (xO (xO n))) => String "0" (string_of_positive n)
  | xI (xO (xO (xO n))) => String "1" (string_of_positive n)
  | xO (xI (xO (xO n))) => String "2" (string_of_positive n)
  | xI (xI (xO (xO n))) => String "3" (string_of_positive n)
  | xO (xO (xI (xO n))) => String "4" (string_of_positive n)
  | xI (xO (xI (xO n))) => String "5" (string_of_positive n)
  | xO (xI (xI (xO n))) => String "6" (string_of_positive n)
  | xI (xI (xI (xO n))) => String "7" (string_of_positive n)
  | xO (xO (xO (xI n))) => String "8" (string_of_positive n)
  | xI (xO (xO (xI n))) => String "9" (string_of_positive n)
  | xO (xI (xO (xI n))) => String "A" (string_of_positive n)
  | xI (xI (xO (xI n))) => String "B" (string_of_positive n)
  | xO (xO (xI (xI n))) => String "C" (string_of_positive n)
  | xI (xO (xI (xI n))) => String "D" (string_of_positive n)
  | xO (xI (xI (xI n))) => String "E" (string_of_positive n)
  | xI (xI (xI (xI n))) => String "F" (string_of_positive n)
  end.
Definition string_of_N n :=
  match n with
  | N0 => "0"
  | Npos n => string_of_positive n
  end.
Compute (string_of_N 100).
Compute (string_of_N 200).
Compute (string_of_N 350).

Notation "'GM'" := (stateT N (sum string)).

Definition fresh (prefix : string) : GM string :=
  let! n := get in
  let! _ := modify (fun x => 1 + x) in
  ret (prefix +++ string_of_N n).

Definition runGM {A} (m : GM A) : TemplateMonad A :=
  m <- tmEval cbv m ;; (* Necessary: if removed, evaluation takes forever *)
  match runStateT m 0 with
  | inl e => tmFail ("runGM: " +++ e)
  | inr (x, _) => TM.ret x
  end.

Definition runGM' {A} (n : N) (m : GM A) : string + (A × N) :=
  runStateT m n.

Definition findM {A} (k : string) (m : Map string A) : GM A :=
  match find k m with
  | Some v => ret v
  | None => raise ("findM: " +++ k)
  end.

Definition findM' {A} (k : string) (m : Map string A) (s : string) : GM A :=
  match find k m with
  | Some v => ret v
  | None => raise ("findM': " +++ s +++ ": " +++ k)
  end.

Definition findM'' {A B} `{Eq A} (k : A) (m : Map A B) (s : string) : GM B :=
  match find k m with
  | Some v => ret v
  | None => raise ("findM'': " +++ s)
  end.

Definition nth_errorN {A} (xs : list A) (n : N) : option A :=
  let fix go n xs :=
    match n, xs with
    | _, [] => None
    | N0, x :: _ => Some x
    | n, _ :: xs => go (n - 1) xs
    end
  in go 0 xs.

Definition nthM {A} (n : N) (xs : list A) : GM A :=
  match nth_errorN xs n with
  | Some v => ret v
  | None => raise ("nthM: " +++ string_of_N n)
  end.

Definition nthM_nat {A} (n : nat) (xs : list A) : GM A :=
  match nth_error xs n with
  | Some v => ret v
  | None => raise ("nthM: " +++ nat2string10 n)
  end.

(* Parse a mutual inductive definition into constructor names + argument types *)

Definition ind_info := Map string ((mutual_inductive_body × list inductive) × nat).

Record mind_graph_t := mk_mg {
  mgAtoms : Map string term; (* name -> AST e.g. "list_nat" -> tApp {| .. |} {| .. |} *)
  mgTypes : Map string term; (* name -> AST *)
  mgConstrs : Map string (list string); (* e.g. "nat" -> ["S"; "O"] *)
  mgChildren : Map string ((N × list string) × string) }. (* e.g. "cons_nat" -> (1, ["nat"; "list_nat"], "list_nat") *)

Definition is_sep (c : ascii) : bool :=
  match c with
  | "." | "#" => true
  | _ => false
  end%char.

Fixpoint qualifier (s : string) : string :=
  let fix go s :=
    match s with
    | "" => ("", false)
    | String c s => 
      let '(s, qualified) := go s in
      let qualified := (qualified || is_sep c)%bool in
      (if qualified then String c s else s, qualified)
    end
  in fst (go s).

Definition inductives_of_env (decls : global_env) : ind_info :=
  fold_right
    (fun '(kername, decl) m =>
      match decl with
      | ConstantDecl _ => m
      | InductiveDecl mbody =>
        let qual := qualifier kername in
        let kernames := mapi (fun i body => (i, qual +++ body.(ind_name))) mbody.(ind_bodies) in
        let inds := map (fun '(i, kername) => mkInd kername i) kernames in
        fold_right
          (fun '(i, kername) m =>
            insert kername (mbody, inds, i) m)
          m kernames
      end)
    empty
    decls.

Fixpoint mangle (inds : ind_info) (e : term) : GM string :=
  match e with
  | tRel n => raise "mangle: relative binders not allowed"
  | tApp tycon tys =>
    let! tycon := mangle inds tycon in
    foldlM
      (fun tys ty =>
        let! ty := mangle inds ty in
        ret (tys +++ "_" +++ ty))
      tycon tys
  | tInd ind n =>
    let! '(mbody, _, _) := findM ind.(inductive_mind) inds in
    let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
    ret body.(ind_name)
  | tConstruct ind n _ =>
    let! '(mbody, _, _) := findM ind.(inductive_mind) inds in
    let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
    let! '(c, _, _) := nthM_nat n body.(ind_ctors) in
    ret c
  | e => raise ("mangle: Unrecognized type: " +++ string_of_term e)
  end.

Fixpoint decompose_sorts (ty : term) : list name × term :=
  match ty with
  | tProd n (tSort _) ty =>
    let '(ns, ty) := decompose_sorts ty in
    (n :: ns, ty)
  | ty => ([], ty)
  end.

Definition tm_type_of (inds : ind_info) (ind : inductive) (n : nat) (pars : list term) : GM term :=
  let! '(mbody, inductives, _) := findM ind.(inductive_mind) inds in
  let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
  let! '(c, cty, arity) := nthM_nat n body.(ind_ctors) in
  let '(_, cty) := decompose_sorts cty in
  let ind_env := (rev pars ++ rev_map (fun ind => tInd ind []) inductives)%list in
  ret (subst0 ind_env cty).

(* Types of constructors for ind specialized to pars *)
Definition constr_types (inds : ind_info) (ind : inductive) (pars : list term)
  : GM (list (string × (list term × term))) :=
  let! '(mbody, _, _) := findM ind.(inductive_mind) inds in
  let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
  foldriM_nat
    (fun n _ cs =>
      let ctr := mkApps (tConstruct ind n []) pars in
      let! ctr_ty := tm_type_of inds ind n pars in
      let '(_, tys, rty) := decompose_prod ctr_ty in
      let! c := mangle inds ctr in
      ret ((c, (tys, rty)) :: cs))
    [] body.(ind_ctors).

Definition decompose_ind (ty : term) : GM (inductive × list term) :=
  match ty with
  | tInd ind _ => ret (ind, [])
  | tApp (tInd ind _) ts => ret (ind, ts)
  | ty => raise "decompose_ind: Unrecognized type"
  end.

Definition build_graph (atoms : list term) (p : program) : GM (ind_info × mind_graph_t) :=
  let '(decls, ty) := p in
  let! '(ind, pars) := decompose_ind ty in
  let inds := inductives_of_env decls in
  let! atoms :=
    fold_right
      (fun '(k, v) m => insert k v m)
      empty
      <$> (let! ids := mapM (mangle inds) atoms in ret (combine ids atoms))
  in
  let fix go n (ind : inductive) (pars : list term) g
      : GM mind_graph_t :=
    match n with O => ret g | S n =>
      let ty := mkApps (tInd ind []) pars in
      let! s := mangle inds ty in
      if member s g.(mgTypes) then ret g else
      let mgTypes := insert s ty g.(mgTypes) in
      let! ctys := constr_types inds ind pars in
      let mgConstrs := insert s (map fst ctys) g.(mgConstrs) in
      let! mgChildren :=
        foldriM
          (fun n '(c, (tys, _)) m =>
            let! tys := mapM (mangle inds) tys in
            ret (insert c (n, tys, s) m))
          g.(mgChildren) ctys
      in
      let g := mk_mg g.(mgAtoms) mgTypes mgConstrs mgChildren in
      let! g :=
        foldrM
          (fun '(c, (tys, _)) g =>
            foldrM
              (fun ty g =>
                let! '(ind, pars) := decompose_ind ty in
                go n ind pars g)
              g tys)
          g ctys
      in
      ret g
    end
  in
  let! g := go 100%nat ind pars (mk_mg atoms atoms empty empty) in
  ret (inds, g).

(* Generate a type of depth-1 frames + associated operations *)

Record frame := mk_frame {
  hIndex : nat;
  hName : string;
  hConstr : term;
  hLefts : list term;
  hFrame : term;
  hRights : list term;
  hRoot : term }.

Definition fn : term -> term -> term := tProd nAnon.
Definition type0 := tSort Universe.type0.
Definition func x t e := tLambda (nNamed x) t e.
Definition lam t e := tLambda nAnon t e.

Definition gen_univ_univD (typename : string) (g : mind_graph_t)
  : ((mutual_inductive_entry × Map string N) × string) × term :=
  let ty_u := typename +++ "_univ" in
  let mgTypes := list_of_map g.(mgTypes) in
  let tys := map (fun '(ty, _) => (ty, ty_u +++ "_" +++ ty)) mgTypes in
  let ty_ns := foldri (fun n '(ty, _) m => insert ty n m) (fun _ => empty) tys in
  let tys := map snd tys in
  let ind_entry : one_inductive_entry := {|
    mind_entry_typename := ty_u;
    mind_entry_arity := type0;
    mind_entry_template := false;
    mind_entry_consnames := tys;
    mind_entry_lc := repeat (tRel 0) #|tys| |}
  in
  let univ_ind := mkInd (typename +++ "_univ") 0 in
  let univ := tInd univ_ind [] in
  let body :=
    func "u" univ
      (tCase (univ_ind, O)
        (lam univ type0)
        (tRel 0) (map (fun '(_, ty) => (O, ty)) mgTypes))
  in ({|
    mind_entry_record := None;
    mind_entry_finite := Finite;
    mind_entry_params := [];
    mind_entry_inds := [ind_entry];
    mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
    mind_entry_variance := None;
    mind_entry_private := None |}, ty_ns, typename +++ "_univD", body).

Definition holes_of {A} (xs : list A) : list ((list A × A) × list A) :=
  let fix go l xs :=
    match xs with
    | [] => []
    | x :: xs => (rev l, x, xs) :: go (x :: l) xs
    end
  in go [] xs.

Definition gen_frames (g : mind_graph_t) : GM (list frame × Map string (list frame)) :=
  let! cfs :=
    foldrM
      (fun '(c, (n_constr, tys, rty)) hs =>
        let! tys := mapM (fun ty => findM ty g.(mgTypes)) tys in
        let! rty := findM rty g.(mgTypes) in
        let! '(ind, pars) := decompose_ind rty in
        foldriM
          (fun n_arg '(l, x, r) hs =>
            ret ((c, {|
              hIndex := 0; (* bogus! filled in below *)
              hName := c +++ string_of_N n_arg;
              hConstr := mkApps (tConstruct ind (N.to_nat n_constr) []) pars;
              hLefts := l;
              hFrame := x;
              hRights := r;
              hRoot := rty |}) :: hs))
          hs (holes_of tys))
      [] (list_of_map g.(mgChildren))
  in
  ret (foldri_nat
    (fun i '(c, f) '(fs, m) =>
      let f := mk_frame i f.(hName) f.(hConstr) f.(hLefts) f.(hFrame) f.(hRights) f.(hRoot) in
      (f :: fs, update c (cons f) [] m))
    (fun _ => ([], empty))
    cfs).

Definition index_of {A} (f : A -> bool) (xs : list A) : GM nat :=
  let fix go n xs :=
    match xs with
    | [] => raise "index_of: not found"
    | x :: xs => if f x then ret n else go (S n) xs
    end
  in go O xs.

Definition gen_frame_t (typename : string) (inds : ind_info) (g : mind_graph_t) (fs : list frame)
  : GM mutual_inductive_entry :=
  let univ := tInd (mkInd (typename +++ "_univ") 0) [] in
  let to_univ ty :=
    let! mangled := mangle inds ty in
    let! n := index_of (fun '(s, _) => eq_string s mangled) (list_of_map g.(mgTypes)) in
    ret (tConstruct (mkInd (typename +++ "_univ") 0) n [])
  in
  let! ctr_types :=
    mapM
      (fun '(mk_frame _ _ _ ls t rs root) =>
        let! args := mapM to_univ [t; root] in
        let rty := mkApps (tRel #|ls ++ rs|) args in
        ret (fold_right fn (fold_right fn rty rs) ls))
      fs
  in
  let ind_entry : one_inductive_entry := {|
    mind_entry_typename := typename +++ "_frame_t";
    mind_entry_arity := fn univ (fn univ type0);
    mind_entry_template := false;
    mind_entry_consnames := map (fun h => h.(hName)) fs;
    mind_entry_lc := ctr_types |}
  in
  ret {|
    mind_entry_record := None;
    mind_entry_finite := Finite;
    mind_entry_params := [];
    mind_entry_inds := [ind_entry];
    mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
    mind_entry_variance := None;
    mind_entry_private := None |}.

Definition gen_frameD (typename : string) (univD_kername : string) (fs : list frame)
  : string × term :=
  let univ_ty := tInd (mkInd (typename +++ "_univ") O) [] in
  let univD ty := mkApps (tConst univD_kername []) [ty] in
  let frame_ind := mkInd (typename +++ "_frame_t") O in
  let frame_ty := mkApps (tInd frame_ind []) [tRel 1; tRel O] in
  let mk_arm h :=
    let 'mk_frame _ name constr lefts frame rights root := h in
    let ctr_arity := #|lefts ++ rights| in
    let indices := rev (seq (1 + #|rights|) #|lefts|) ++ [O] ++ rev (seq 1 #|rights|) in
    let add_arg arg_ty body := lam arg_ty body in
    (ctr_arity, fold_right lam (fold_right lam (lam frame (mkApps constr (map tRel indices))) rights) lefts)
  in
  let body :=
    func "A" univ_ty (func "B" univ_ty (func "h" frame_ty
      (tCase (frame_ind, O)
        (func "A" univ_ty (func "B" univ_ty (func "h" frame_ty
          (fn (univD (tRel 2)) (univD (tRel 2))))))
        (tRel O) (map mk_arm fs))))
  in
  (typename +++ "_frameD", body).

Definition kername_of_const (s : string) : TemplateMonad string :=
  ref <- tmAbout s ;;
  match ref with
  | Some (ConstRef kername) => TM.ret kername
  | Some _ => tmFail ("kername_of_const: Not a constant: " +++ s)
  | None => tmFail ("kername_of_const: Not in scope: " +++ s)
  end.

Definition gen_Frame_ops (typename : string) (T : program) (atoms : list term) : GM _ :=
  let! '(inds, g) := build_graph atoms T in
  let! '(fs, cfs) := gen_frames g in
  let '(univ, univ_of_tyname, univD, univD_body) := gen_univ_univD typename g in
  let! frame_t := gen_frame_t typename inds g fs in
  ret (inds, g, fs, cfs, univ, univ_of_tyname, univD, univD_body, frame_t).

Record aux_data_t := mk_aux_data {
  aIndInfo : ind_info;
  aTypename : string;
  aGraph : mind_graph_t;
  aUnivOfTyname : Map string N;
  aFramesOfConstr : Map string (list frame) }.

Class AuxData (U : Set) := aux_data : aux_data_t.

Polymorphic Definition mk_Frame_ops (typename : string) (T : Type) (atoms : list Type) : TemplateMonad unit :=
  p <- tmQuoteRec T ;;
  atoms <- monad_map tmQuote atoms ;;
  mlet (inds, g, fs, cfs, univ, univ_of_tyname, univD, univD_body, frame_t) <-
    runGM (gen_Frame_ops typename p atoms) ;;
  tmMkInductive univ ;;
  tmMkDefinition univD univD_body ;;
  tmMkInductive frame_t ;;
  univD_kername <- kername_of_const univD ;;
  let '(frameD, frameD_body) := gen_frameD typename univD_kername fs in
  tmMkDefinition frameD frameD_body ;;
  tmMkDefinition (typename +++ "_Frame_ops") (
    mkApps (tConstruct (mkInd "Frame" 0) 0 []) [
      tInd (mkInd (typename +++ "_univ") 0) [];
      tConst (typename +++ "_univD") [];
      tInd (mkInd (typename +++ "_frame_t") 0) [];
         tConst (typename +++ "_frameD") []]) ;;
  qinds <- tmQuote inds ;;
  qg <- tmQuote g ;;
  quniv_of_tyname <- tmQuote univ_of_tyname ;;
  qtypename <- tmQuote typename ;;
  qcfs <- tmQuote cfs ;;
  tmMkDefinition (typename +++ "_aux_data")
    (mkApps <%@mk_aux_data%> [qinds; qtypename; qg; quniv_of_tyname; qcfs]).

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

Inductive Fuel := Empty | More (F : Fuel).
Definition Fuel_Fix {A} (d : A) (f : A -> A) : Fuel -> A :=
  let fix go F :=
    match F with
    | Empty => d
    | More F => f (go F)
    end
  in go.

(* The type of correct rewriters (AuxData and Preserves instances are additional assumptions
   needed by the generator) *)
Definition rewriter {U} `{Frame U} `{AuxData U} (root : U) (R : relation (univD root))
  (R_misc S_misc : Set)
  (D : forall {A}, univD A -> Set) `{@Delayed U H (@D)}
  (R_C : forall {A}, frames_t A root -> Set)
  (R_e : forall {A}, univD A -> Set)
  (St : forall {A}, frames_t A root -> univD A -> Set)
 `{@Preserves_R_C U H root (@R_C)}
 `{@Preserves_S U H root (@St)}
:=
  Fuel -> R_misc -> S_misc -> forall A (C : @frames_t U H A root) (e : univD A) (d : D e),
  rw_for root R S_misc (@R_C) (@R_e) (@St) C (delayD e d).

(* ---------- Flags to aid in proof saerch ---------- *)

(* For each rule, *)
Inductive ExtraVars (s : string) : Prop := MkExtraVars.
Inductive EditDelay (s : string) : Prop := MkEditDelay.
Inductive PreserveTopdownEdit (s : string) : Prop := MkPreserveTopdownEdit.
Inductive PreserveBottomupEdit (s : string) : Prop := MkPreserveBottomupEdit.
Inductive RunRule (s : string) : Prop := MkRunRule.

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
  obEditDelays : list A;
  obPreserveEdits : list A;
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
  rSpecialVars : Set' string;
  rOneRMisc : term;
  rOneSMisc : term;
  rGuard : term }.
Record rules_t := mk_rules {
  rR : inductive;
  rRules : list rule_t;
  rUniv : inductive;
  rRootU : nat;
  rHFrame : term;
  rRMisc : term;
  rSMisc : term }.

Definition ctor_ty := (string × term) × nat.
Definition ctors_ty := list ctor_ty.

Section GoalGeneration.

Context (R_C R_e St : term).

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
      else if (
          (func ==? (prefix +++ "Put")) ||
          (func ==? (prefix +++ "Modify")) ||
          (func ==? (prefix +++ "Local")))%bool
      then
        match args with
        | [_; _; _; rhs] => go rhs
        | _ => empty
        end
      else
        empty
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
  let! '(Γ, R_misc, S_misc, guard) :=
    match Γ with
    | (_, {| decl_type := tApp <%@When%> [R_misc; S_misc; guard] |}) :: Γ =>
      ret (Γ, R_misc, S_misc, guard)
    | _ => raise "rule_of_ind_ctor: missing When clause"
    end
  in
  match rty with
  (* Topdown rule *)
  | tApp (tVar _) [
      tApp (tConst framesD1 []) [
        _univ; _HFrame; tConstruct _univ_ind hole_ut []; _root_univ_ty; tVar _ as C; lhs];
      tApp (tConst framesD2 []) [_; _; _; _; _; rhs]] =>
    let lhs_vars := vars_of lhs in
    let rec_vars := rec_rhs_vars_of rhs in
    let special_vars := rec_vars ∩ lhs_vars in
    ret (mk_rule name ctor_ty arity dTopdown hole_ut Γ C lhs rhs
      lhs_vars rec_vars special_vars R_misc S_misc guard)
  (* Bottomup rule *)
  | tApp (tConst _BottomUp []) [_; tApp (tVar _) [
      tApp (tConst _framesD []) [
        _univ; _HFrame; tConstruct _univ_ind hole_ut []; _root_univ_ty; C; lhs];
      tApp (tConst _ []) [_; _; _; _; _; rhs]]] =>
    let lhs_vars := vars_of lhs in
    let rec_vars := rec_rhs_vars_of rhs in
    let special_vars := rec_vars ∩ lhs_vars in
    ret (mk_rule name ctor_ty arity dBottomup hole_ut Γ C lhs rhs
      lhs_vars rec_vars special_vars R_misc S_misc guard)
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
  | {| rΓ := Γ; rC := tVar C; rOneRMisc := R_misc; rOneSMisc := S_misc |} :: _ =>
    let! Cty := findM C Γ in
    match Cty.(decl_type) with
    | tApp (tConst _frames_t []) [tInd univ []; HFrame; _hole; tConstruct _univ root []] =>
      ret (mk_rules ind rules univ root HFrame R_misc S_misc)
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

(* ---------- Types of helpers for delayed computation in each edit ---------- *)

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
  (R_C R_e St : term) (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (R_misc := rules.(rRMisc))
  (S_misc := rules.(rSMisc))
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rw_univ_i [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU))
  (* specialize to rw_univ -> Set *)
  (univD := mkApps <%@univD%> [rw_univ; HFrame]).

Definition gen_edit_delay_ty (r : rule_t) : GM term. ltac1:(refine(
  let! R := gensym "R" in
  let! d := gensym "d" in
  let lhs_univ := mk_univ r.(rHoleU) in
  let lhs_vars := r.(rLhsVars) in
  let rhs_recs := r.(rRecVars) in
  let! '(xts, σ) :=
    mfoldM
      (fun x _ '(xts, σ) =>
        let! decl := findM' x r.(rΓ) "special_var" in
        let ty := decl.(decl_type) in
        let! tyname := mangle ind_info ty in
        let! x' := gensym (remove_sigils' x) in
        let σ := insert x x' σ in
        if member x rhs_recs then
          let! d' := gensym "d" in
          let! univ_n := findM' tyname univ_of_tyname "edit_delay univ_of_tyname" in
          let u := mk_univ (N.to_nat univ_n) in
          ret ((x, x', ty, Some (d', u)) :: xts, σ)
        else ret ((x, x', ty, None) :: xts, σ))
      ([], empty) lhs_vars
  in
  let new_lhs := rename σ r.(rLhs) in
  ret (fn (mkApps <%EditDelay%> [quote_string r.(rName)])
    (tProd (nNamed R) type0
    (fold_right
      (fun '(x, _, xty, _) ty => tProd (nNamed x) xty ty)
      (tProd (nNamed d) (mkApps delay_t [lhs_univ; r.(rLhs)])
      (fn
        (fold_right
          (fun '(x, x', xty, mdu') ty =>
            match mdu' with
            | None => tProd (nNamed x') xty ty
            | Some (d', u) =>
              tProd (nNamed x') xty (tProd (nNamed d') (mkApps delay_t [u; tVar x]) ty)
            end)
          (fn
            (mkApps <%@eq%> [
               mkApps univD [lhs_univ];
               mkApps delayD [lhs_univ; r.(rLhs); tVar d];
               new_lhs])
            (fold_right
              (fun '(x, x', xty, mdu') ty =>
                match mdu' with
                | None => ty
                | Some (d', u) =>
                  fn (mkApps <%@eq%> [xty; tVar x'; mkApps delayD [u; tVar x; tVar d']]) ty
                end)
              (tVar R)
              xts))
          xts)
        (tVar R)))
      xts)))
)).
Defined.

Definition gen_edit_delay_tys : GM (list term). ltac1:(refine(
  let rules :=
    filter
      (fun 'r => match r.(rDir) with dTopdown => true | dBottomup => false end)
      rules.(rRules)
  in
  let! named := mapM (fun r => gen_edit_delay_ty r) rules in
  mapM (indices_of []) named
  (* ret named *)
)).
Defined.

End GoalGeneration.

(* ---------- Types of helpers for computing preconditions/intermediate values ---------- *)

Section GoalGeneration.

Context (R_C R_e St : term) (rules : rules_t)
        (rw_univ := rules.(rUniv))
        (HFrame := rules.(rHFrame))
        (root := rules.(rRootU))
        (* specialize to univD rw_univ -> univD rw_univ -> Set *)
        (frames_t := mkApps <%@frames_t%> [tInd rw_univ []; HFrame])
        (* specialize to rw_univ -> Set *)
        (univD := mkApps <%@univD%> [tInd rw_univ []; HFrame]) 
        (R_misc := rules.(rRMisc))
        (S_misc := rules.(rSMisc))
        (mk_univ := fun n => tConstruct rw_univ n []).

Definition gen_extra_vars_ty (rule : rule_t) : GM term :=
  let hole := rule.(rHoleU) in
  let lhs := rule.(rLhs) in
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
  let! mr := gensym "mr" in
  let! ms := gensym "ms" in
  let! r_C := gensym "r_C" in
  let! r_e := gensym "r_e" in
  let! s := gensym "s" in
  let guard := rule.(rGuard) in
  let hole := mk_univ hole in
  let root := mk_univ root in
  ret (fn (mkApps <%ExtraVars%> [quote_string rule.(rName)])
    (tProd (nNamed mr) R_misc (tProd (nNamed ms) S_misc
    (tProd (nNamed R) type0 (tProd (nNamed C) (mkApps frames_t [hole; root])
    (fold_right
      (fun '(_, s, d) ty => tProd (nNamed s) d.(decl_type) ty)
      (tProd (nNamed r_C) (mkApps R_C [hole; tVar C])
       (tProd (nNamed r_e) (mkApps R_e [hole; lhs])
       (tProd (nNamed s) (mkApps St [hole; tVar C; lhs])
       (fn
         (fold_right
           (fun '(_, s, d) ty => tProd (nNamed s) d.(decl_type) ty)
           (fn
             (mkApps <%@eq%> [<%bool%>; mkApps guard [tVar mr; tVar ms]; <%true%>])
             (tVar R))
           (rev rhs_ctx))
         (fn (tVar R) (tVar R))))))
      (rev lhs_ctx))))))).

Definition gen_extra_vars_tys : GM (list term) :=
  mapM
    (fun r => let! ty := gen_extra_vars_ty r in indices_of [] ty)
    (* (fun r => gen_extra_vars_ty r) *)
    rules.(rRules).

End GoalGeneration.

(* ---------- Types of helpers for preserving env/state across edits ---------- *)

Section GoalGeneration.

Context (R_C R_e St : term)
        (rs : rules_t)
        (rw_univ := rs.(rUniv)).

Definition gen_preserve_edit_ty  (rule : rule_t) : term :=
  let '{| rDir := d; rHoleU := hole_ut; rΓ := Γ; rC := C; rLhs := lhs; rRhs := rhs |} := rule in
  let hole_t := tConstruct rw_univ hole_ut [] in
  match d with
  | dTopdown =>
    fn (mkApps <%PreserveTopdownEdit%> [quote_string rule.(rName)])
    (it_mkProd_or_LetIn (drop_names Γ)
    (fn (mkApps R_C [hole_t; C])
    (fn (mkApps R_e [hole_t; lhs])
    (fn (mkApps St [hole_t; C; lhs])
    (mkApps <%prod%> [mkApps R_e [hole_t; rhs]; mkApps St [hole_t; C; rhs]])))))
  | dBottomup =>
    fn (mkApps <%PreserveBottomupEdit%> [quote_string rule.(rName)])
    (it_mkProd_or_LetIn (drop_names Γ)
    (fn (mkApps R_C [hole_t; C])
    (fn (mkApps R_e [hole_t; lhs])
    (fn (mkApps St [hole_t; C; lhs])
    (mkApps St [hole_t; C; rhs])))))
  end.

Definition gen_preserve_edit_tys : GM (list term) :=
  mapM (fun t => indices_of [] (gen_preserve_edit_ty t)) rs.(rRules).

End GoalGeneration.

(* ---------- Types of helpers for taking a single step ---------- *)

Section GoalGeneration.

Context
  (R_C R_e St : term)
  (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rw_univ_i [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU))
  (R_misc := rules.(rRMisc))
  (S_misc := rules.(rSMisc))
  (* specialize to forall A, frames_t A root -> univD A -> Set *)
  (rw_for := mkApps <%@rw_for%> [
    rw_univ; HFrame; root; rw_rel; S_misc; R_C; R_e; St])
  (rw_for' := mkApps <%@rw_for'%> [
    rw_univ; HFrame; root; rw_rel; S_misc; R_C; St]).

Definition gen_run_rule_ty (r : rule_t) : term. ltac1:(refine(
  let hole := mk_univ r.(rHoleU) in
  let rw_for := match r.(rDir) with dTopdown => rw_for | dBottomup => rw_for' end in
  fn (mkApps <%RunRule%> [quote_string r.(rName)])
  (fn R_misc (fn S_misc
  (it_mkProd_or_LetIn (drop_names r.(rΓ))
  (fn
    (mkApps rw_for [hole; r.(rC); r.(rRhs)])
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
  (R_C R_e St : term) (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (R_misc := rules.(rRMisc))
  (S_misc := rules.(rSMisc))
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
    rw_univ; HFrame; root; rw_rel; S_misc; R_C; R_e; St])
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
    (fn R_misc (fn S_misc (tProd (nNamed C) (mkApps frames_t [univ_rty; root]) 
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
              (fn R_misc (fn S_misc
              (fold_right
                (fun '(x', _, t, _, _, _) ty => if x ==? x' then ty else tProd (nNamed x') t ty)
                  (mkApps rw_for [
                    u; mkApps frames_cons [
                      u; univ_rty; root; 
                      mkApps f (map tVar (lxs ++ rxs)); tVar C];
                    tVar x])
                xutfs))))
            ty)
        (mkApps rw_for [univ_rty; tVar C; mkApps constr (map (fun '(x, _, _, _, _, _) => tVar x) xutfs)])
        xutfs)
      xutfs)))))
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
  (R_C R_e St : term) (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (R_misc := rules.(rRMisc))
  (S_misc := rules.(rSMisc))
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
  let! mr := gensym "mr" in
  let! ms := gensym "ms" in
  let! d := gensym "d" in
  let! R := gensym "R" in
  let! C := gensym "C" in
  let! e := gensym (abbreviate t_tyname) in
  let! r_C := gensym "r_C" in
  let! r_e := gensym "r_e" in
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
              tProd (nNamed x) t (tProd (nNamed x') t
              (match md with
               | Some d => tProd (nNamed d) (mkApps delay_t [u; tVar x]) ty
               | None => ty
               end)))
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
        let rGuard := rename σ r.(rGuard) in
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
            ([], empty) r.(rLhsVars)
        in
        let old_lhs := rename σ r.(rLhs) in
        let! header :=
          gen_case_tree ind_info [(tVar e, r.(rLhs))] type0 
            (mkApps <%Active%> [quote_string r.(rName)])
            <%Impossible%>
        in
        ret (fn (mkApps <%InspectCaseRule%> [quote_string r.(rName)]) (fn header
          (it_mkProd_or_LetIn (drop_names rΓ)
          (fn (mkApps <%@eq%> [<%bool%>; mkApps rGuard [tVar mr; tVar ms]; <%true%>])
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
              (fn (mkApps <%@eq%> [mkApps univD [t_univ]; tVar e; old_lhs]) (tVar R))
              extra_vars))
            extra_vars))))))
      applicable
  in
  ret (fn (mkApps <%@Topdown%> [rw_univ; t_univ])
    (tProd (nNamed mr) R_misc (tProd (nNamed ms) S_misc 
    (tProd (nNamed R) type0 (tProd (nNamed C) (mkApps frames_t [t_univ; root])
    (tProd (nNamed e) (mkApps univD [t_univ])
    (tProd (nNamed d) (mkApps delay_t [t_univ; tVar e])
    (tProd (nNamed r_C) (mkApps R_C [t_univ; tVar C]) 
    (tProd (nNamed r_e) (mkApps R_e [t_univ; mkApps delayD [t_univ; tVar e; tVar d]]) 
    (tProd (nNamed s) (mkApps St [t_univ; tVar C; mkApps delayD [t_univ; tVar e; tVar d]])
    (fold_right fn (fold_right fn (tVar R) congruences) applicable)))))))))))
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
  let! mr := gensym "mr" in
  let! ms := gensym "ms" in
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
        let rGuard := rename σ r.(rGuard) in
        let! header :=
          gen_case_tree ind_info [(tVar e, r.(rLhs))] type0 
            (mkApps <%Active%> [quote_string r.(rName)])
            <%Impossible%>
        in
        ret (fn (mkApps <%InspectCaseRule%> [quote_string r.(rName)]) (fn header
          (it_mkProd_or_LetIn (drop_names rΓ)
          (fn (mkApps <%@eq%> [mkApps univD [t_univ]; tVar e; r.(rLhs)])
          (fn (mkApps <%@eq%> [<%bool%>; mkApps rGuard [tVar mr; tVar ms]; <%true%>]) (tVar R)))))))
      applicable
  in
  ret (fn (mkApps <%@Bottomup%> [rw_univ; t_univ])
    (tProd (nNamed mr) R_misc (tProd (nNamed ms) S_misc
    (tProd (nNamed R) type0 (tProd (nNamed C) (mkApps frames_t [t_univ; root])
    (tProd (nNamed e) (mkApps univD [t_univ])
    (tProd (nNamed r_C) (mkApps R_C [t_univ; tVar C]) 
    (tProd (nNamed s) (mkApps St [t_univ; tVar C; tVar e])
    (fold_right fn (fn (fn <%Fallback%> (tVar R)) (tVar R)) applicable)))))))))
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

Context (aux : aux_data_t) (delay_t delayD R_C R_e St : term) (rules : rules_t).

Definition gen_all : GM (RwObligations term). ltac1:(refine(
  let! extra_vars := gen_extra_vars_tys R_C R_e St rules in
  let! edit_delays := gen_edit_delay_tys aux delay_t delayD rules in
  let! preserve_edits := gen_preserve_edit_tys R_C R_e St rules in
  let! run_rules := gen_run_rule_tys R_C R_e St rules in
  let! constr_delays := gen_constr_delay_tys delay_t delayD aux in
  let! smart_constrs := gen_smart_constr_tys aux R_C R_e St rules in
  let! '(topdowns, bottomups) := gen_inspect_tys aux delay_t delayD R_C R_e St rules in
  ret (mk_obs extra_vars edit_delays preserve_edits run_rules constr_delays smart_constrs topdowns bottomups)
)).
Defined.

Definition unquote_all (obs : RwObligations term) : TemplateMonad (RwObligations typed_term). ltac1:(refine(
  let '(mk_obs extra_vars edit_delays preserve_edits run_rules constr_delays smart_constrs topdowns bottomups) :=
    obs
  in
  extra_vars <- monad_map tmUnquote extra_vars ;;
  edit_delays <- monad_map tmUnquote edit_delays ;;
  preserve_edits <- monad_map tmUnquote preserve_edits ;;
  run_rules <- monad_map tmUnquote run_rules ;;
  constr_delays <- monad_map tmUnquote constr_delays ;;
  smart_constrs <- monad_map tmUnquote smart_constrs ;;
  topdowns <- monad_map tmUnquote topdowns ;;
  bottomups <- monad_map tmUnquote bottomups ;;
  ret (mk_obs extra_vars edit_delays preserve_edits run_rules constr_delays smart_constrs topdowns bottomups)
)).
Defined.

End GoalGeneration.

Ltac mk_rw_obs k :=
  lazymatch goal with
  | |- @rewriter ?U ?HFrame ?HAux ?root ?R _ _ ?D ?HDelay ?R_C ?R_e ?St _ _ =>
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      delay_t <- tmQuote D ;;
      delayD <- tmQuote (@delayD U HFrame D HDelay) ;;
      R_C' <- tmQuote (@R_C) ;;
      R_e' <- tmQuote (@R_e) ;;
      St' <- tmQuote (@St) ;;
      ret (delay_t, delayD, R_C', R_e', St')) ltac:(fun pack =>
    lazymatch pack with
    | (?delay_t, ?delayD, ?R_C', ?R_e', ?St') =>
      runGM n (
        let! delay_t' := named_of [] delay_t in
        let! delayD' := named_of [] delayD in
        let! R_C'' := named_of [] R_C' in
        let! R_e'' := named_of [] R_e' in
        let! St'' := named_of [] St' in
        gen_all HAux delay_t' delayD' R_C'' R_e'' St'' rules) ltac:(fun qobs n =>
        run_template_program (unquote_all qobs) k)
    end))
  end.

Ltac assert_typed_terms terms k :=
  lazymatch terms with
  | [] => k tt
  | {| my_projT2 := ?t |} :: ?rest => assert t; [|assert_typed_terms rest k]
  end.

Ltac assert_obs obs k :=
  lazymatch obs with
  | @mk_obs _ ?extra_vars ?edit_delays ?preserve_edits ?run_rules ?constr_delays
            ?smart_constrs ?topdowns ?bottomups =>
    assert_typed_terms extra_vars ltac:(fun _ =>
    assert_typed_terms edit_delays ltac:(fun _ =>
    assert_typed_terms preserve_edits ltac:(fun _ =>
    assert_typed_terms run_rules ltac:(fun _ =>
    assert_typed_terms constr_delays ltac:(fun _ =>
    assert_typed_terms smart_constrs ltac:(fun _ =>
    assert_typed_terms topdowns ltac:(fun _ =>
    assert_typed_terms bottomups k)))))))
  end.

Ltac mk_rw' := mk_rw_obs ltac:(fun obs => assert_obs obs ltac:(fun _ => idtac)).

Ltac mk_smart_constr_children root R_C R_e St mr ms s hasHrel Hrel :=
  lazymatch goal with
  | H : SmartConstrCase (frameD ?frame ?hole) -> _ |- _ =>
    specialize (H (MkSmartConstrCase _) mr ms);
    let x := fresh "x" in
    let s' := fresh "s" in
    let ms' := fresh "ms" in
    let Hrel' := fresh "Hrel" in
    edestruct H as [x s' ms' Hrel'];
    [eapply (@preserve_R_C _ _ root R_C _); cbv; eassumption
    |apply (@preserve_R_e _ _ R_e _ _ _ frame hole); assumption
    |eapply (@preserve_S_dn _ _ root St _); cbv; eassumption
    |idtac];
    clear H; clear s ms;
    apply (@preserve_S_up _ _ root St _) in s'; cbv in s';
    lazymatch hasHrel with
    | false => idtac
    | true => apply (rt_trans _ _ _ _ _ Hrel) in Hrel'; clear Hrel
    end;
    mk_smart_constr_children root R_C R_e St mr ms' s' true Hrel'
  | _ =>
    lazymatch hasHrel with
    | false => econstructor; [exact s|exact ms|apply rt_refl]
    | true => econstructor; [exact s|exact ms|exact Hrel]
    end
  end.
Ltac mk_smart_constr :=
   clear;
   let mr := fresh "mr" in
   let ms := fresh "ms" in
   let C := fresh "C" in
   let r_C := fresh "r_C" in
   let r_e := fresh "r_e" in
   let s := fresh "s" in
   intros _ mr ms C; intros;
   lazymatch goal with
   | |- @rw_for _ _ ?root _ _ ?R_C ?R_e ?St _ _ _ =>
     unfold rw_for in *; intros r_C r_e s;
     mk_smart_constr_children root R_C R_e St mr ms s false None
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
  | H : PreserveTopdownEdit ?rule -> _ |- RunRule ?rule -> _ =>
    clear - H;
    intros;
    let Hnext := fresh "Hnext" in
    lazymatch goal with H : _ |- _ => revert H end;
    let r_C := fresh "r_C" in
    let r_e := fresh "r_e" in
    let s := fresh "s" in
    unfold rw_for; intros Hnext r_C r_e s;
    eapply (H (MkPreserveTopdownEdit rule)) in s; try eassumption;
    clear r_e; destruct s as [r_e s];
    let x' := fresh "x'" in
    let s' := fresh "s'" in
    let ms' := fresh "ms'" in
    let Hrel := fresh "Hrel" in
    destruct (Hnext r_C r_e s) as [x' s' ms' Hrel];
    econstructor; [exact s'|exact ms'|];
    eapply rt_trans; [eapply rt_step|exact Hrel];
    run_template_program (tm_get_constr rule) ltac:(fun ctor =>
    match ctor with
    | {| my_projT2 := ?ctor' |} =>
      eapply ctor';
      lazymatch goal with
      | |- When _ => exact I 
      | _ => eassumption
      end
    end)
  | H : PreserveBottomupEdit ?rule -> _ |- RunRule ?rule -> _ =>
    clear - H;
    intros;
    let Hnext := fresh "Hnext" in
    lazymatch goal with H : _ |- _ => revert H end;
    let r_C := fresh "r_C" in
    let s := fresh "s" in
    unfold rw_for'; intros Hnext r_C s;
    eapply (H (MkPreserveBottomupEdit rule)) in s; try eassumption;
    let x' := fresh "x'" in
    let s' := fresh "s'" in
    let ms' := fresh "ms'" in
    let Hrel := fresh "Hrel" in
    destruct (Hnext r_C s) as [x' s' ms' Hrel];
    econstructor; [exact s'|exact ms'|];
    eapply rt_trans; [eapply rt_step|exact Hrel];
    run_template_program (tm_get_constr rule) ltac:(fun ctor =>
    match ctor with
    | {| my_projT2 := ?ctor' |} =>
      eapply ctor';
      lazymatch goal with
      | |- When _ => exact I 
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
Ltac mk_topdown_active mr ms s :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active ?rule -> _, Hdelay : EditDelay ?rule -> _,
    Hextras : ExtraVars ?rule -> _ |- _ =>
    eapply (Hdelay (MkEditDelay rule));
    assert Sentinel by exact MkSentinel; intros;
    lazymatch goal with
    | HdelayD : delayD _ _ = _ |- _ =>
      rewrite HdelayD in s;
      eapply (Hextras (MkExtraVars rule) mr ms);
      [(* Find all the misc. arguments by unification *) eassumption ..
      |(* Success continuation: add rhs vars + assumptions above the line *) intros
      |(* Failure continuation: forget everything about the rule we just applied *)
       rewrite <- HdelayD in s;
       clear Hdelay Hextras H;
       repeat lazymatch goal with
       | H : ?T |- _ => lazymatch T with Sentinel => fail | _ => clear H end
       end;
       lazymatch goal with H : Sentinel |- _ => clear H end];
      [(* Success: apply the proper rule *)
       eapply (H (MkInspectCaseRule rule) (MkActive rule)); [..|reflexivity]; eassumption
      |(* Failure: try to apply other rules *)
        mk_topdown_active mr ms s]
    end
  | _ => mk_topdown_congruence
  end.
Ltac mk_topdown :=
  repeat lazymatch goal with
  | H : Topdown -> _ |- _ => clear H
  | H : SmartConstr _ -> _ |- _ => clear H
  | H : PreserveTopdownEdit _ -> _ |- _ => clear H
  | H : PreserveBottomupEdit _ -> _ |- _ => clear H
  end;
  let mr := fresh "mr" in
  let ms := fresh "ms" in
  let d := fresh "d" in
  let R := fresh "R" in
  let C := fresh "C" in
  let e := fresh "e" in
  let r_C := fresh "r_C" in
  let r_e := fresh "r_e" in
  let s := fresh "s" in
  intros _ mr ms R C e d r_C r_e s; intros;
  repeat strip_one_match;
  mk_topdown_active mr ms s.

Ltac mk_bottomup_fallback :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active _ -> _ |- _ => fail
  | H : Fallback -> _ |- _ => exact (H MkFallback)
  end.
Ltac mk_bottomup_active mr ms :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active ?rule -> _, Hextras : ExtraVars ?rule -> _ |- _ =>
    eapply (Hextras (MkExtraVars rule) mr ms);
    [eassumption..|intros|clear Hextras H];
    [eapply (H (MkInspectCaseRule rule) (MkActive rule)); eauto
    (* TODO: eassumption not sufficient because sometimes need reflexivity? *)
    |mk_bottomup_active mr ms]
  | _ => mk_bottomup_fallback
  end.
Ltac mk_bottomup :=
  repeat lazymatch goal with
  | H : Topdown -> _ |- _ => clear H
  | H : Bottomup -> _ |- _ => clear H
  | H : SmartConstr _ -> _ |- _ => clear H
  | H : PreserveTopdownEdit _ -> _ |- _ => clear H
  | H : PreserveBottomupEdit _ -> _ |- _ => clear H
  end;
  let mr := fresh "mr" in
  let ms := fresh "ms" in
  let R := fresh "R" in
  let C := fresh "C" in
  let e := fresh "e" in
  let r := fresh "r" in
  let s := fresh "s" in
  intros _ mr ms R C e r s; intros;
  repeat strip_one_match;
  mk_bottomup_active mr ms.

Ltac try_find_constr e k_constr k_atom :=
  lazymatch goal with
  | H : SmartConstr e -> _ |- _ => k_constr e H
  | _ =>
    lazymatch e with
    | ?e' _ => try_find_constr e' k_constr k_atom
    | _ => k_atom e
    end
  end.
Ltac next_action e k_put k_modify k_local k_rec k_constr k_atom :=
  lazymatch e with
  | Put ?s ?e' => k_put s e'
  | Modify ?f ?e' => k_modify f e'
  | Local ?f ?e' => k_local f e'
  | Rec ?e' => k_rec e'
  | _ => try_find_constr e k_constr k_atom
  end.

Ltac mk_edit_rhs recur univ HFrame root R R_misc S_misc delay_t HD R_C R_e St mr ms :=
  let rec go _ :=
    lazymatch goal with
    | |- rw_for _ _ _ _ _ _ _ ?e =>
      next_action e 
        (* Monadic operations: apply the corresponding combinator and continue *)
        ltac:(fun f e' =>
          (* idtac "put" f e'; *)
          (* match goal with |- ?G => idtac G end; *)
          (* idtac) *)
          apply (@rw_Put univ HFrame root R R_misc S_misc mr ms R_C R_e St);
          clear mr ms; intros mr ms; go tt)
        ltac:(fun f e' =>
          (* idtac "modify" f e'; *)
          (* match goal with |- ?G => idtac G end; *)
          (* idtac) *)
          apply (@rw_Modify univ HFrame root R R_misc S_misc mr ms R_C R_e St);
          clear mr ms; intros mr ms; go tt)
        ltac:(fun f e' => 
          apply (@rw_Local univ HFrame root R R_misc S_misc mr ms R_C R_e St);
          clear mr ms; intros mr ms; go tt)
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
              apply (recur mr ms _ _ _ d)
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
              let r_e := fresh "r_e" in
              let s := fresh "s" in
              intros r_C r_e s;
              let Hfuse := fresh "Hfuse" in
              assert (Hfuse : {d' : @D univ y |
                f (@delayD U HFrame D HD univ y d) = @delayD U HFrame D HD univ y d'});
              [|let r_C' := fresh "r_C" in
                let r_e' := fresh "r_e" in
                let s' := fresh "s" in
                let r_Cty := type of r_C in
                let r_ety := type of r_e in
                let sty := type of s in
                (assert (r_C' : r_Cty) by exact r_C);
                (assert (r_e' : r_ety) by exact r_e);
                (assert (s' : sty) by exact s);
                revert r_C' r_e' s'; clear r_C r_e s;
                let Hd' := fresh "Hd" in
                let d' := fresh "d" in
                destruct Hfuse as [d' Hd'];
                rewrite H, Hd';
                apply (recur mr ms _ _ _ d')]
            end
          (* If recursive call isn't on a variable at all, recur with the identity delay *)
          | _ =>
            lazymatch goal with
            | |- rw_for _ _ _ _ _ _ ?C _ =>
              let hole :=
                lazymatch type of C with
                | @frames_t _ _ ?hole _ => hole
                | @frames_t' univ _ ?hole _ => hole
                end
              in
              rewrite <- (@delay_id_law univ HFrame delay_t HD hole e');
              apply (recur mr ms _ _ _ (@delay_id univ HFrame delay_t HD hole e'))
            end
          end)
        (* Constructor nodes: apply the smart constructor... *)
        ltac:(fun constr Hconstr =>
          apply (Hconstr (MkSmartConstr constr) mr ms);
          (* ...and recursively expand each child (with proper mr, ms!) *)
          clear mr ms; intros _ mr ms; intros;
          go tt)
        (* Atoms: just return the atom *)
        ltac:(fun e => apply (@rw_id univ HFrame root R R_misc S_misc R_C R_e St mr ms))
    end
  in go tt.

Ltac mk_rewriter :=
  lazymatch goal with
  | |- @rewriter ?univ ?HFrame _ ?root ?R ?R_misc ?S_misc ?delay_t ?HD ?R_C ?R_e ?St _ _ =>
    unfold rewriter;
    lazymatch goal with
    | |- Fuel -> ?T =>
      let recur := fresh "recur" in
      let mr := fresh "mr" in
      let ms := fresh "ms" in
      let A := fresh "A" in
      apply (@Fuel_Fix T); [apply (@rw_base univ _ root _ R_misc S_misc delay_t HD R_C R_e St)|];
      intros recur mr ms A; destruct A;
      lazymatch goal with
      (* Nonatomic children *)
      | Htopdown : Topdown ?hole -> _ |- forall _ : frames_t ?hole _, _ =>
        let C := fresh "C" in
        let e := fresh "e" in
        let d := fresh "d" in
        intros C e d;
        revert mr ms;
        eapply (@rw_chain univ HFrame root R R_misc S_misc delay_t HD R_C R_e St);
        [(* Topdown *)
         intros mr ms;
         let r_C := fresh "r_C" in
         let r_e := fresh "r_e" in
         let s := fresh "s" in
         intros r_C r_e s;
         let r_C' := fresh "r_C" in
         let r_e' := fresh "r_e" in
         let s' := fresh "s" in
         let r_Cty := type of r_C in
         let r_ety := type of r_e in
         let sty := type of s in
         (assert (r_C' : r_Cty) by exact r_C);
         (assert (r_e' : r_ety) by exact r_e);
         (assert (s' : sty) by exact s);
         revert r_C' r_e' s';
         change (@rw_for univ _ root R S_misc R_C R_e St _ C (delayD e d));
         apply (Htopdown (MkTopdown hole) mr ms _ C e d r_C r_e s);
         clear r_C r_e s;
         lazymatch goal with
         (* Rule applications *)
         | Hrun : RunRule ?rule -> _ |- InspectCaseRule ?rule -> _ =>
           intros _ _; intros;
           lazymatch goal with He : delayD e d = _ |- _ => rewrite He end;
           eapply (Hrun (MkRunRule rule)); [eassumption..|];
           mk_edit_rhs recur univ HFrame root R R_misc S_misc delay_t HD R_C R_e St mr ms
         (* Congruence cases *)
         | Hconstr : SmartConstr ?constr -> _ |- InspectCaseCongruence ?constr -> _ =>
           intros _ _; intros;
           lazymatch goal with Hdelay : delayD e d = _ |- _ => rewrite Hdelay end;
           apply (Hconstr (MkSmartConstr constr) mr ms);
           (* For each child, intros new mr, ms *)
           clear mr ms; intros _ mr ms; intros;
           lazymatch goal with
           (* If child is nonatomic (has call to delayD), recur *)
           | |- rw_for _ _ _ _ _ _ _ (delayD _ _) =>
             apply (recur mr ms)
           (* Otherwise, just return it *)
           | |- rw_for _ _ _ _ _ _ _ _ =>
             apply (@rw_id univ HFrame root R R_misc S_misc R_C R_e St mr ms)
           end
         end
        |(* Bottomup *)
         lazymatch goal with
         | Hbottomup : Bottomup hole -> _ |- _ =>
           clear d e; intros e;
           intros mr ms;
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
           change (@rw_for' univ _ root R S_misc R_C St _ C e);
           apply (Hbottomup (MkBottomup hole) mr ms _ C e r_C s);
           clear r_C s;
           lazymatch goal with
           (* Rule applications *)
           | Hrun : RunRule ?rule -> _ |- InspectCaseRule ?rule -> _ =>
             intros _ _; intros;
             lazymatch goal with He : e = _ |- _ => rewrite He end;
             (* Run the rule... *)
             idtac Hrun;
             eapply (Hrun (MkRunRule rule) mr ms); [eassumption..|];
             (* (* ...and then just return the modified tree *) *)
             apply (@rw_id' univ HFrame root R R_misc S_misc R_C St mr ms);
             idtac
           (* Fallback (just return the child) *)
           | |- Fallback -> _ =>
             intros _;
             apply (@rw_id' univ HFrame root R R_misc S_misc R_C St mr ms)
           end
         end]
      (* Atomic children: just run the delayed computation *)
      | |- forall _ : frames_t ?hole _, _ =>
        let C := fresh "C" in
        let e := fresh "e" in
        let d := fresh "d" in
        intros C e d;
        apply (@rw_base univ HFrame root R R_misc S_misc delay_t HD R_C R_e St mr ms _ _ _ d)
      end
    end
  end.

(* Like mk_rw', but apply the default automation and only leave behind nontrivial goals *)
Ltac mk_rw :=
  mk_rw';
  try lazymatch goal with
  | |- SmartConstr _ -> _ => mk_smart_constr
  | |- RunRule _ -> _ => mk_run_rule
  | |- Topdown _ -> _ => mk_topdown
  | |- Bottomup _ -> _ => mk_bottomup
  end;
  [..|mk_rewriter].
