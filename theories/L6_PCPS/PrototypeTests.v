From CertiCoq.L6 Require Import Prototype MockExpr.

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

Unset Strict Unquote Universe Mode.

(* ---------- Example ---------- *)

Instance Frame_exp_inj : @Frame_inj exp_univ _.
Proof. unfold Frame_inj; destruct f; simpl; ltac1:(congruence). Defined.

Ltac EqDec_auto := try solve [now left|right; congruence].

Instance EqDec_nat : EqDec nat.
Proof. unfold EqDec; repeat ltac1:(decide equality). Defined.

Instance EqDec_var : EqDec var.
Proof. unfold EqDec; repeat ltac1:(decide equality). Defined.

Instance EqDec_constr : EqDec constr.
Proof. unfold EqDec; repeat ltac1:(decide equality). Defined.

Lemma exp_eq_dec' (x y : exp) : {x = y} + {x <> y}
with fd_eq_dec' (x y : fundef) : {x = y} + {x <> y}.
Proof.
- repeat ltac1:(decide equality).
- repeat ltac1:(decide equality).
Defined.

Instance EqDec_exp : EqDec exp := {eq_dec' := exp_eq_dec'}.
Instance EqDec_fd : EqDec fundef := {eq_dec' := fd_eq_dec'}.

Instance EqDec_list {A} `{EqDec A} : EqDec (list A) := {eq_dec' := list_eq_dec eq_dec'}.

(* Instance univ_eq_exp : @UnivEq exp_univ exp_frame_t. *)
(* Proof. ltac1:(derive_UnivEq). Defined. *)

Check frames_nil >:: cons_fundef0 [] >:: fFun2 (mk_var 0) [].
Check fun e => <[ cons_fundef0 []; fFun2 (mk_var 0) [] ]> ⟦ e ⟧.

Definition used_vars_var : var -> list var := fun x => [x].
Definition used_vars_constr : constr -> list var := fun _ => [].
Definition used_vars_list_var : list var -> list var := fun xs => xs.
Definition used_vars_list {A} (f : A -> list var) (xs : list A) : list var := concat (map f xs).
Definition used_vars_arm' used_vars_exp : constr * exp -> list var := fun '(_, e) => used_vars_exp e.
Fixpoint used_vars_exp (e : exp) : list var :=
  match e with
  | eHalt x => [x]
  | eApp f xs => f :: xs
  | eCons x c ys e => x :: ys ++ used_vars_exp e
  | eProj x y n e => x :: y :: used_vars_exp e
  | eCase x arms => x :: used_vars_list (used_vars_arm' used_vars_exp) arms
  | eFuns fds e => used_vars_list used_vars_fundef fds ++ used_vars_exp e
  end
with used_vars_fundef (fd : fundef) :=
  let 'fFun f xs e := fd in
  f :: xs ++ used_vars_exp e.
Definition used_vars_arm := used_vars_arm' used_vars_exp.

(* Example: commonly want to track max used vars for fresh name generation *)
Definition used_vars_prop {A : exp_univ} (C : frames_t A exp_univ_exp) (e : univD A) (x : var) : Prop :=
  ~ In x (used_vars_exp (C ⟦ e ⟧)).

(* When just moving up and down, next fresh var doesn't need to be updated *)

Instance Preserves_S_dn_exp : Preserves_S_dn (@used_vars_prop).
Proof. intros A B C C_ok f x; destruct f; unfold used_vars_prop; simpl; intros; assumption. Defined.

Instance Preserves_S_up_exp : Preserves_S_up (@used_vars_prop).
Proof. intros A B C C_ok f x; destruct f; unfold used_vars_prop; simpl; intros; assumption. Defined.

(* ---------- Mock relation + state for testing ---------- *)

Inductive R : exp -> exp -> Prop :=
| R0 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys ys' e,
    ys' = ys ++ ys ->
    R (C⟦eCons x c ys e⟧) (C⟦eCons x c ys' (Rec e)⟧)
| R1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c y ys ys' e,
    #|ys| = 4%nat ->
    (forall D : frames_t exp_univ_exp exp_univ_exp, D >++ C = D >++ C) ->
    e = e ->
    ys' = ys ++ [y; y] ->
    R (C⟦eCons x c (y :: ys) e⟧) (C⟦eCons x c ys' (Rec e)⟧)
| R2 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x xs xs' e fds,
    #|xs| = 0%nat ->
    xs ++ [x] = xs' ->
    C = C ->
    BottomUp (R (C⟦fFun f (x :: xs) e :: fds⟧) (C⟦fFun f xs' e :: fds⟧))
| R3 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x x' xs xs' e fds,
    #|xs| = 0%nat ->
    xs ++ [x] = xs' ->
    C = C ->
    BottomUp (R (C⟦fFun f (x :: x' :: xs) e :: fds⟧) (C⟦fFun f xs' e :: fds⟧)).

Definition I_R {A} (C : frames_t A exp_univ_exp) (n : nat) : Prop := C = C.

Definition I_S {A} (C : frames_t A exp_univ_exp) (x : univD A) (n : nat) : Prop := C⟦x⟧ = C⟦x⟧.

Instance Preserves_R_R_C : Preserves_R (@I_R).
Proof. intros A B C C_ok f [n _]; exists n; unerase; reflexivity. Defined.

Instance Preserves_S_dn_St : Preserves_S_dn (@I_S).
Proof. intros A B C C_ok f x [n _]; exists n; unerase; reflexivity. Defined.

Instance Preserves_S_up_St : Preserves_S_up (@I_S).
Proof. intros A B C C_ok f x [n _]; exists n; unerase; reflexivity. Defined.

(* Run TemplateProgram (tmPrint =<< parse_rel R). *) (* For some reason, this hangs.. *)

(* ...but this doesn't: *)
Goal True.
  ltac1:(parse_rel 0 R ltac:(fun x n => idtac x)).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_extra_vars_tys AuxData_exp rules D'' I_D'' R'' I_R'' S'' I_S'' delayD') ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_run_rule_tys rules R'' I_R'' S'' I_S'') ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_constr_delay_tys rules D'' I_D'' delayD' AuxData_exp) ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_smart_constr_tys AuxData_exp rules R'' I_R'' S'' I_S'') ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Definition test_case_tree (pat pat_ty ret_ty success failure : term) : TemplateMonad unit :=
  mlet (ast, nameless) <- runGM (
    let! ast :=
      gen_case_tree exp_aux_data.(aIndInfo) [(tVar "$input", pat)] ret_ty success failure
    in
    let ast := tLambda (nNamed "$input") pat_ty ast in
    let! nameless := indices_of [] ast in
    (* let nameless := tRel 0 in *)
    ret (ast, nameless)) ;;
  (* print_nf nameless ;; *)
  tm <- tmUnquote nameless ;;
  tmPrint tm ;;
  print_nf ast ;;
  ret tt.

Compute runGM' 0 (gen_case_tree exp_aux_data.(aIndInfo)
  [(tVar "discr", mkApps <%S%> [mkApps <%S%> [mkApps <%S%> [tVar "n"]]])] <%nat%> <%true%> <%false%>).

Compute <%(mk_constr 0, eApp (mk_var 0) [])%>.
Run TemplateProgram (test_case_tree <%3%nat%> <%nat%> <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%@nil nat%> <%list nat%> <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%eApp (mk_var 0) []%> <%exp%> <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%(mk_constr 0, eApp (mk_var 0) [])%> <%(constr * exp)%type%>
                                   <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%eCase (mk_var 1) [(mk_constr 0, eApp (mk_var 0) [])]%> <%exp%>
                                   <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree
  (mkApps <%eCase%> [mkApps <%mk_var%> [tVar "$n"]; mkApps <%@cons (constr * exp)%type%> [
    mkApps <%@pair constr exp%> [mkApps <%mk_constr%> [tVar "$m"];
    mkApps <%eApp%> [<%mk_var 0%>; <%@nil var%>]]; <%@nil (constr * exp)%type%>]])
  <%exp%> <%nat%> (mkApps <%plus%> [tVar "$n"; tVar "$m"]) <%O%>).

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_inspect_tys AuxData_exp rules D'' I_D'' R'' I_R'' S'' I_S'' delayD') ltac:(fun qobs n =>
        run_template_program (
          let '(topdown, bottomup) := qobs in
          topdown' <- monad_map tmUnquote topdown ;;
          bottomup' <- monad_map tmUnquote bottomup ;;
          tmPrint "-------------------- topdown --------------------" ;;
          tmPrint topdown' ;;
          tmPrint "-------------------- bottomup --------------------" ;;
          tmPrint bottomup')
          ltac:(fun x => idtac))
    end))).
Abort.

(* Context (opaque_delay_t : forall {A : exp_univ}, univD A -> Set) *)
(*        `{Hopaque_delay : @Delayed exp_univ Frame_exp (@opaque_delay_t)}. *)
Definition opaque_delay_t {A : exp_univ} (e : univD A) := unit.

Definition const_fun {A B} (x : A) (y : B) : B := y.

Inductive R' : exp -> exp -> Prop :=
| R'0 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys ys' e,
    ys' = ys ++ ys ->
    R' (C⟦eCons x c ys e⟧) (C⟦eCons x c ys' (Rec (const_fun tt e))⟧) . (*
| R'1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c y ys ys' e,
    #|ys| = 4%nat /\
    (forall D : frames_t exp_univ_exp exp_univ_exp, D >++ C = D >++ C) /\
    e = e /\
    ys' = ys ++ [y; y] ->
    R' (C⟦eCons x c (y :: ys) e⟧) (C⟦eCons x c ys' (Rec e)⟧)
| R'4 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys e,
    R' (C⟦eCons x c ys e⟧) (C⟦eCons x c ys (Rec (eCons x c ys e))⟧)
| R'2 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x xs xs' e fds,
    #|xs| = 0%nat /\
    xs ++ [x] = xs' /\
    C = C ->
    BottomUp (R' (C⟦fFun f (x :: xs) e :: fds⟧) (C⟦fFun f xs' e :: fds⟧))
| R'3 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x x' xs xs' e fds,
    #|xs| = 0%nat /\
    xs ++ [x] = xs' /\
    C = C ->
    BottomUp (R' (C⟦fFun f (x :: x' :: xs) e :: fds⟧) (C⟦fFun f xs' e :: fds⟧)). *)

Goal True.
  ltac1:(
  parse_rel 0 R' ltac:(fun rules n => idtac rules n)).
Abort.

Definition rw_R' : fueled_rewriter exp_univ_exp R' unit (I_D_plain (U:=exp_univ) (D:=unit)) nat (@I_R) nat (@I_S).
Proof.
  ltac1:(mk_rw';
    try lazymatch goal with
    | |- SmartConstr _ -> _ => mk_smart_constr
    | |- TopdownRunRule _ -> _ => mk_run_rule
    | |- BottomupRunRule _ -> _ => mk_run_rule
    | |- Topdown _ -> _ => mk_topdown
    | |- Bottomup _ -> _ => mk_bottomup
    end;
    (* This particular rewriter's delayed computation is just the identity function, *)
    (*    so ConstrDelay and EditDelay are easy *)
    mk_easy_delay;
    (* try lazymatch goal with *)
    (* | |- ConstrDelay _ -> _ => admit *)
    (* | |- EditDelay _ -> _ => admit *)
    (* end; *)
    (* try lazymatch goal with *)
    (* | |- ExtraVars _ -> _ => admit *)
    (* end; *)
    [..|mk_rewriter];
    idtac).
  { cbn; intros; ltac1:(cond_success success).
    eapply success; eauto.
    constructor > [exact O|reflexivity]. }
Defined.

Definition rw_R'' : 
  rewriter exp_univ_exp R' (@opaque_delay_t) (@R_C) (@St).
Proof.
  ltac1:(let x := eval unfold rw_R', Fuel_Fix, rw_chain, rw_id, rw_base in rw_R' in
  let x := eval unfold preserve_R, Preserves_R_R_C, Preserves_S_St in x in
  let x := eval lazy beta iota zeta in x in
  let x := eval unfold delayD, opaque_delay_t, Delayed_D_unit in x in
  let x := eval lazy beta iota zeta in x in
  exact x).
Defined.

Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction rw_R''.
(* - is directly recursive (no fixpoint combinator) 
   - the context parameter C looks dead by induction *)

(*
Compute rw_R'' (xI xH) exp_univ_exp <[]>
  (eCons (mk_var 0) (mk_constr 0) [] (eApp (mk_var 1) []))
  tt
  {| envVal := 0; envPrf := eq_refl |}
  {| stVal := 0; stPrf := eq_refl |}. *)

(* -------------------- Example with state (not working yet) -------------------- *)

Instance Eq_var : Eq var := {rel_dec := fun '(mk_var n) '(mk_var m) => n ==? m}.

Definition renaming {A : exp_univ} (e : univD A) := var -> var.

Definition one_renaming x y := fun x' => if x ==? x' then y else x'.

Definition subst_arm' (subst_exp : (var -> var) -> exp -> exp) (σ : var -> var)
  : _ -> constr * exp := fun '(c, e) => (c, subst_exp σ e).
Fixpoint subst_exp σ e :=
  match e with
  | eHalt x => eHalt (σ x)
  | eApp f xs => eApp (σ f) (map σ xs)
  | eCons x c ys e => eCons (σ x) c (map σ ys) (subst_exp σ e)
  | eProj x y n e => eProj (σ x) (σ y) n (subst_exp σ e)
  | eCase x arms => eCase (σ x) (map (subst_arm' subst_exp σ) arms)
  | eFuns fds e => eFuns (map (subst_fd σ) fds) (subst_exp σ e)
  end
with subst_fd σ fd :=
  let 'fFun f xs e := fd in
  fFun (σ f) (map σ xs) (subst_exp σ e).
Definition subst_arm := subst_arm' subst_exp.

Lemma map_id {A} (f : A -> A) xs : (forall x, f x = x) -> map f xs = xs.
Proof. induction xs as [|x xs IHxs]; auto; simpl; intros; now rewrite IHxs. Defined.

Lemma subst_exp_id σ e : (forall x, σ x = x) -> subst_exp σ e = e
with subst_fd_id σ fd : (forall x, σ x = x) -> subst_fd σ fd = fd.
Proof.
  - intros Hσ; destruct e; simpl.
    + now rewrite Hσ.
    + now rewrite Hσ, map_id.
    + now rewrite Hσ, map_id, subst_exp_id.
    + now rewrite Hσ, subst_exp_id.
    + induction arms as [|[] arms Harms]; simpl; try ltac1:(congruence).
      rewrite Hσ in *; do 2 f_equal.
      * now rewrite subst_exp_id.
      * ltac1:(congruence).
    + rewrite subst_exp_id > [|assumption]; f_equal.
      induction fds; auto; simpl.
      rewrite subst_fd_id > [|assumption]; f_equal; assumption.
  - intros Hσ; destruct fd; simpl.
    now rewrite Hσ, map_id, subst_exp_id.
Defined.

Lemma map_comp {A} (f g : A -> A) xs : map (f ∘ g) xs = map f (map g xs).
Proof. induction xs as [|x xs IHxs]; auto; simpl; intros; now rewrite IHxs. Defined.

Lemma subst_exp_comp σ1 σ2 e : subst_exp (σ1 ∘ σ2) e = subst_exp σ1 (subst_exp σ2 e)
with subst_fd_comp σ1 σ2 fd : subst_fd (σ1 ∘ σ2) fd = subst_fd σ1 (subst_fd σ2 fd).
Proof.
  - destruct e; simpl; f_equal; try (now (rewrite map_comp)); try (now (apply subst_exp_comp)).
    + induction arms as [|[] arm Harm]; auto; simpl.
      rewrite subst_exp_comp; now f_equal.
    + induction fds as [|[] fd Hfd]; auto; simpl.
      rewrite subst_exp_comp, map_comp; now f_equal.
  - destruct fd; simpl; f_equal > [now rewrite map_comp|now rewrite subst_exp_comp].
Defined.

Instance Delayed_renaming : Delayed (@renaming).
Proof.
  ltac1:(unshelve econstructor).
  - destruct A; simpl; intros x σ.
    + exact (subst_arm σ x).
    + exact (map (subst_arm σ) x).
    + exact (subst_fd σ x).
    + exact (map (subst_fd σ) x).
    + exact (subst_exp σ x).
    + exact (σ x).
    + exact x.
    + exact x.
    + exact (map σ x).
  - intros. exact id.
  - intros [] []; simpl;
      try ltac1:(match goal with p : constr * exp |- _ => destruct p; simpl end);
      repeat (rewrite map_id);
      repeat (rewrite subst_exp_id);
      repeat (rewrite subst_fd_id);
      try ltac1:(match goal with |- forall _ : constr * exp, _ => intros []; simpl end);
      repeat (rewrite subst_exp_id);
      try (now (intros; apply subst_fd_id; auto));
      auto.
Defined.

Definition subst_compose_law :
  forall {A} (x : univD A) (σ2 : renaming x) (σ1 : renaming (delayD x σ2)),
  delayD (delayD x σ2) σ1 = delayD x (σ1 ∘ σ2).
Proof.
  intros [] [] σ1 σ2; simpl; auto;
    try ltac1:(match goal with p : constr * exp |- _ => destruct p; simpl end);
    try (rewrite <- subst_exp_comp);
    try (rewrite <- subst_fd_comp);
    try (rewrite <- map_comp); repeat f_equal;
    auto.
  - apply (@FunctionalExtensionality.functional_extensionality (constr * exp) (constr * exp)); intros []; simpl.
    now rewrite <- subst_exp_comp.
  - apply (@FunctionalExtensionality.functional_extensionality fundef); intros.
    now rewrite <- subst_fd_comp.
  - apply (@FunctionalExtensionality.functional_extensionality (constr * exp) (constr * exp)); intros []; simpl.
    now rewrite <- subst_exp_comp.
  - apply (@FunctionalExtensionality.functional_extensionality fundef); intros.
    now rewrite <- subst_fd_comp.
Defined.

Definition Exists' {A} (P : A -> Prop) : list A -> Prop :=
  fix go xs :=
    match xs with
    | [] => False
    | x :: xs => P x \/ go xs
    end.

Definition occurs_arm' (occurs_exp : var -> exp -> Prop) x (ce : constr * exp) : Prop :=
  let '(c, e) := ce in occurs_exp x e.
Fixpoint occurs_exp (x : var) (e : exp) {struct e} : Prop :=
  match e with
  | eHalt x' => x = x'
  | eApp f xs => x = f \/ In x xs
  | eCons x' c ys e => x = x' \/ In x ys \/ occurs_exp x e
  | eProj x' y n e => x = x' \/ x = y \/ occurs_exp x e
  | eCase x' arms => x = x' \/ Exists' (occurs_arm' occurs_exp x) arms
  | eFuns fds e => Exists' (occurs_fd x) fds \/ occurs_exp x e
  end
with occurs_fd (x : var) (fd : fundef) {struct fd} : Prop :=
  match fd with
  | fFun f xs e => x = f \/ In x xs \/ occurs_exp x e
  end.
Definition occurs_arm := occurs_arm' occurs_exp.

Definition occurs {A} : var -> univD A -> Prop :=
  match A with
  | exp_univ_nat => fun _ _ => False
  | exp_univ_prod_constr_exp => occurs_arm
  | exp_univ_list_prod_constr_exp => fun x => Exists' (occurs_arm x)
  | exp_univ_fundef => occurs_fd
  | exp_univ_list_fundef => fun x => Exists' (occurs_fd x)
  | exp_univ_exp => occurs_exp
  | exp_univ_var => eq
  | exp_univ_constr => fun _ _ => False
  | exp_univ_list_var => @In var
  end.

Definition occurs_frame (x : var) {A B} (f : exp_frame_t A B) : Prop. ltac1:(refine(
  match f with
  | pair_constr_exp0 e => occurs_exp x e
  | pair_constr_exp1 c => False
  | cons_prod_constr_exp0 ces => Exists' (occurs_arm x) ces
  | cons_prod_constr_exp1 ce => occurs_arm x ce
  | fFun0 xs e => In x xs \/ occurs_exp x e
  | fFun1 f e => x = f \/ occurs_exp x e
  | fFun2 f xs => x = f \/ In x xs
  | cons_fundef0 fds => Exists' (occurs_fd x) fds
  | cons_fundef1 fd => occurs_fd x fd
  | eHalt0 => False
  | eApp0 xs => In x xs
  | eApp1 f => x = f
  | eCons0 c ys e => In x ys \/ occurs_exp x e
  | eCons1 x' ys e => x = x' \/ In x ys \/ occurs_exp x e
  | eCons2 x' c e => x = x' \/ occurs_exp x e
  | eCons3 x' c ys => x = x' \/ In x ys
  | eProj0 y n e => x = y \/ occurs_exp x e
  | eProj1 x' n e => x = x' \/ occurs_exp x e
  | eProj2 x' y e => x = x' \/ x = y \/ occurs_exp x e
  | eProj3 x' y n => x = x' \/ x = y
  | eCase0 ces => Exists' (occurs_arm x) ces
  | eCase1 x' => x = x'
  | eFuns0 e => occurs_exp x e
  | eFuns1 fds => Exists' (occurs_fd x) fds
  end
)).
Defined.

Definition occurs_ctx {A B} (x : var) (C : frames_t A B) : Prop :=
  frames_any (@occurs_frame x) C.

Definition occurs_frame_split {A B} (x : var) (f : frame_t A B) (e : univD A)
  : occurs x (frameD f e) <-> occurs_frame x f \/ occurs x e.
Proof. destruct f eqn:Hf; simpl; ltac1:(tauto). Defined.

Fixpoint occurs_ctx_split {A B} (x : var) (C : frames_t A B) (e : univD A) {struct C}
  : occurs x (C ⟦ e ⟧) <-> occurs_ctx x C \/ occurs x e.
Proof.
  destruct C.
  - now unfold occurs_ctx, frames_any.
  - rewrite framesD_cons.
    rewrite occurs_ctx_split.
    rewrite occurs_frame_split.
    unfold occurs_ctx; simpl; ltac1:(tauto).
Defined.

Inductive cp_fold : exp -> exp -> Prop :=
| cp_case_fold : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ces e,
    (exists D E ys, C = D >:: eCons3 x c ys >++ E) /\
    (exists l r, ces = l ++ (c, e) :: r) ->
    cp_fold
      (C ⟦ eCase x ces ⟧)
      (C ⟦ Rec e ⟧)
| cp_proj_fold : forall (C : frames_t exp_univ_exp exp_univ_exp) x y y' ys n e,
    (exists D E c, C = D >:: eCons3 y c ys >++ E) /\
    nth_error ys n = Some y' ->
    cp_fold
      (C ⟦ eProj x y n e ⟧)
      (C ⟦ Rec (subst_exp (one_renaming x y') e) ⟧).

Definition cp_env {A} (C : frames_t A exp_univ_exp) : Set := {
  cpConses : var -> option (constr × list var) |
    forall x c ys, cpConses x = Some (c, ys) ->
    exists D E, C = D >:: eCons3 x c ys >++ E }.

Definition var_gt : var -> var -> Prop := fun '(mk_var x) '(mk_var y) => (x > y)%nat.

Definition cp_state {A} (C : frames_t A exp_univ_exp) (e : univD A) : Set :=
  unit.

Lemma eq_var_spec (x y : var) : Bool.reflect (x = y) (x ==? y).
Proof.
  destruct x as [x], y as [y]; simpl.
  destruct (PeanoNat.Nat.eqb_spec x y); constructor; ltac1:(congruence).
Defined.

Instance Preserves_cp_env : Preserves_R exp_univ exp_univ_exp (@cp_env).
Proof.
  intros A B fs.
  unfold cp_env; destruct f eqn:Heqf; intros;
  ltac1:(match goal with H : {_ : _| _} |- _ => destruct H as [cpConses HConses] end);
  ltac1:(
    match type of Heqf with
    (* The case we care about *)
    | _ = eCons3 _ _ _ => idtac
    (* All other cases: just preserve the invariant *)
    | _ =>
      exists cpConses; intros;
      edestruct HConses as [D [E Hctx]]; eauto;
      rewrite Hctx; exists D; eexists;
      match goal with
      | |- ?C >++ ?D >:: ?e = _ =>
        now change (C >++ D >:: e) with (C >++ (D >:: e))
      end
    end).
  exists (fun v' => if v' ==? v then Some (c, l) else cpConses v').
  intros v'; destruct (eq_var_spec v' v); intros c' l' Heq.
  - inversion Heq; subst.
    now exists fs, <[]>.
  - edestruct HConses as [D [E Hctx]]; eauto.
    rewrite Hctx.
    do 2 eexists.
    ltac1:(match goal with
    | |- ?C >:: ?f1 >++ ?E >:: ?f2 = _ =>
      now change (C >:: f1 >++ E >:: f2) with (C >:: f1 >++ (E >:: f2))
    end).
Defined.

Instance Preserves_cp_state : Preserves_S exp_univ exp_univ_exp (@cp_state).
Proof.
  (* Don't need to do anything to the state when moving around, so this is easy *)
  constructor; intros A B fs; unfold cp_state; simpl; intros; assumption.
Defined.

Instance Eq_constr : Eq constr := {rel_dec := fun '(mk_constr n) '(mk_constr m) => n ==? m}.
Lemma eq_constr_spec (x y : constr) : Bool.reflect (x = y) (x ==? y).
Proof.
  destruct x as [x], y as [y]; simpl.
  destruct (PeanoNat.Nat.eqb_spec x y); constructor; ltac1:(congruence).
Defined.

Fixpoint find_arm (c : constr) (ces : list (constr * exp)) : option exp :=
  match ces with
  | [] => None
  | (c', e) :: ces => if c ==? c' then Some e else find_arm c ces
  end.

Lemma find_arm_In : forall c e ces, find_arm c ces = Some e -> exists l r, ces = l ++ (c, e) :: r.
Proof.
  induction ces as [|[c' e'] ces Hces] > [inversion 1|].
  unfold find_arm; fold find_arm.
  destruct (eq_constr_spec c c'); intros Heq.
  - inversion Heq; subst; now exists [], ces.
  - destruct (Hces Heq) as [l [r Hlr]]; subst.
    now exists ((c', e') :: l), r.
Defined.

Require Import Omega.
Lemma fresh_fresher :
  forall {A} x (e : univD A), (forall y, occurs y e -> var_gt x y) -> forall z, var_gt z x -> ~ occurs z e.
Proof.
  intros A x e Hx z Hz; intros Hocc.
  (assert (var_gt x z) by auto); destruct x, z; simpl in *; ltac1:(omega).
Defined.

Lemma occurs_ctx_insert :
  forall {A B} (C : frames_t A B), forall (D : frames_t A A) x e,
  occurs x (C ⟦ e ⟧) -> occurs x (C ⟦ D ⟦ e ⟧ ⟧).
Proof. intros A B C D x e; repeat (rewrite occurs_ctx_split); ltac1:(tauto). Defined.

Lemma app_as_ctx :
  forall l ces c r e, ces = l ++ (c, e) :: r ->
  exists C : frames_t exp_univ_exp exp_univ_list_prod_constr_exp, ces = C ⟦ e ⟧.
Proof.
  induction l; simpl; intros.
  - subst; now exists <[cons_prod_constr_exp0 r; pair_constr_exp1 c]>.
  - subst; edestruct IHl as [C HC]; eauto.
    exists (<[cons_prod_constr_exp1 a]> >++ C).
    rewrite frames_compose_law.
    now rewrite HC; simpl.
Defined.

Lemma In_map_eq {A} (f : A -> A) x xs : In x xs -> f x = x -> In x (map f xs).
Proof.
  induction xs; auto; simpl.
  intros [Heq|Hin]; auto.
  try ltac1:(intuition congruence).
Defined.

Lemma Exists'_map {A} (f : A -> A) P xs :
  Exists' P xs ->
  (forall x, P x -> P (f x)) ->
  Exists' P (map f xs).
Proof. induction xs; auto; simpl; intros [Hhere|Hthere]; auto. Defined.

Lemma occurs_subst_ne_exp x σ e : occurs_exp x e -> σ x = x -> occurs_exp x (subst_exp σ e)
with occurs_subst_ne_fd x σ fd : occurs_fd x fd -> σ x = x -> occurs_fd x (subst_fd σ fd).
Proof.
  - destruct e; simpl; intros.
    + ltac1:(congruence).
    + destruct H > [now left|now (right; apply (In_map_eq σ))].
    + destruct H as [H|H] > [|destruct H] > [now left|now (right; left; apply (In_map_eq σ))|right; right].
      now apply occurs_subst_ne_exp.
    + destruct H as [H|H] > [|destruct H] > [now left|now (right; left)|right; right].
      now apply occurs_subst_ne_exp.
    + induction arms.
      * simpl in H; destruct H > [now left|inversion H].
      * simpl in H; simpl.
        destruct H as [H|H] > [|destruct H] > [now left|right; left|].
        -- destruct a; simpl; now apply occurs_subst_ne_exp.
        -- pose (IHarms (or_intror H)).
           ltac1:(tauto).
    + induction fds.
      * simpl in H; destruct H > [inversion H|now right].
      * simpl in H; simpl.
        destruct H as [H|H] > [destruct H|] >
        [left; now left
        |pose (IHfds (or_introl H)); ltac1:(tauto)
        |pose (IHfds (or_intror H)); ltac1:(tauto)].
  - destruct fd; simpl; intros.
    destruct H as [H|[H|H]] > [now left|right; left; now apply (In_map_eq σ)|].
    right; right; now apply occurs_subst_ne_exp.
Defined.

Definition rw_cp : rewriter exp_univ_exp cp_fold (@renaming) (@cp_env) (@cp_state).
Proof.
  ltac1:(mk_rw; mk_easy_delay).
  (* Now there are two things left: first, we need to explain how to check the preconditions
     of each rule and compute intermediate values *)
  - (* Case folding *)
    intros _ R C x ces d r s success failure.
    destruct r as [cpConses HConses] eqn:Hr.
    destruct (cpConses (d x)) as [[c ys]|] eqn:Hx > [|ltac1:(cond_failure)].
    destruct (find_arm c ces) as [e|] eqn:Hc > [|ltac1:(cond_failure)].
    ltac1:(cond_success success).
    specialize (success e d (d x) (map (subst_arm d) ces) c (subst_exp d e)).
    apply success; auto; split.
    + edestruct HConses as [D [E Hctx]]; eauto.
    + apply find_arm_In in Hc; destruct Hc as [l [r_arms Hlr]].
      exists (map (subst_arm d) l), (map (subst_arm d) r_arms); subst ces.
      now rewrite !map_app.
  - (* Projection folding *)
    clear; intros _ R C e x y n d r s success failure.
    destruct r as [cpConses HConses] eqn:Hr.
    destruct (cpConses (d y)) as [[c ys]|] eqn:Hx > [|ltac1:(cond_failure)].
    destruct (nth_error ys n) as [y'|] eqn:Hn > [|ltac1:(cond_failure)].
    ltac1:(cond_success success); apply (success (subst_exp d e) (fun e => one_renaming (d x) y' (d e))
                                                 (d x) (d y) n y' ys); auto.
    + edestruct HConses as [D [E Hctx]]; eauto.
    + now rewrite <- subst_exp_comp.
Defined.

Check rw_cp.
Eval unfold rewriter, rw_for in rewriter exp_univ_exp cp_fold (@renaming) (@cp_env) (@cp_state).

Definition rw_cp' : 
  rewriter exp_univ_exp cp_fold (@renaming) (@cp_env) (@cp_state).
Proof.
  ltac1:(let x := eval unfold rw_cp, Fuel_Fix, rw_chain, rw_id, rw_base in rw_cp in
  let x := eval unfold preserve_R, Preserves_cp_env, Preserves_cp_state in x in
  let x := eval lazy beta iota zeta in x in
  let x := eval unfold delayD, Delayed_renaming in x in
  let x := eval lazy beta iota zeta in x in
  exact x).
Defined.

Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction rw_cp'.

Definition rw_cp_top e : result exp_univ_exp cp_fold (@cp_state) <[]> e.
Proof.
  rewrite <- delay_id_law.
  ltac1:(refine(
  rw_cp' lots_of_fuel exp_univ_exp <[]> e
    id (exist _ (fun _ => None) _) tt); intros; congruence).
Defined.
Check rw_cp_top.

(*
Compute (rw_cp_top (
  let x0 := mk_var 0 in
  let x1 := mk_var 1 in
  let x2 := mk_var 2 in
  let x3 := mk_var 3 in
  let x4 := mk_var 4 in
  let x5 := mk_var 5 in
  let x6 := mk_var 6 in
  let c1 := mk_constr 1 in
  let c2 :=  mk_constr 2 in
  let c3 := mk_constr 3 in
  eCons x0 c2 [x5; x5; x1; x5; x5]
  (eCons x2 c1 [x0; x3]
  (eCase x0 [
    (c1, eApp x0 [x0]);
    (c2,
      (eProj x4 x0 (2%nat)
      (eProj x5 x2 (1%nat)
      (eApp x4 [x5]))));
    (c3, (eApp x0 [x0]))])))).
*)
