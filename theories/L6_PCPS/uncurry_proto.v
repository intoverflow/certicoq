(** Uncurrying written as a guarded rewrite rule *)

Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require L6.cps. (* for module M *)
Require Import L6.Prototype.
Require Import L6.cps_proto.
Require Import identifiers.  (* for max_var, occurs_in_exp, .. *)
Require Import AltBinNotations.
Require Import L6.Ensembles_util L6.List_util L6.cps_util L6.state.

Require Import Coq.Lists.List.
Import ListNotations.

Definition miscR : Set := unit.
Definition miscS : Set := PM bool * bool.

Definition delay_t {A} (e : univD A) : Set := unit.

Definition R_C {A} (C : exp_c A exp_univ_exp) : Set := unit.
Definition R_e {A} (e : univD A) : Set := unit.

Definition fresher_than (x : cps.var) (S : Ensemble cps.var) : Prop :=
  forall y, y \in S -> (x > y)%positive.

Lemma fresher_than_antimon x S1 S2 : S1 \subset S2 -> fresher_than x S2 -> fresher_than x S1.
Proof. intros HS12 Hfresh y Hy; apply Hfresh, HS12, Hy. Qed.

Definition S {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set :=
  {x | fresher_than x (used_vars ![C ⟦ e ⟧])}.

Instance Delayed_delay_t : Delayed (@delay_t).
Proof.
  unshelve econstructor.
  - intros A e _; exact e.
  - reflexivity.
  - reflexivity.
Defined.

Instance Preserves_R_C_R_C : Preserves_R_C _ exp_univ_exp (@R_C).
Proof. constructor. Defined.

Instance Preserves_R_e_R_e : Preserves_R_e _ (@R_e).
Proof. constructor. Defined.

(* We don't have to do anything to preserve a fresh variable as we move around *)
Instance Preserves_S_S : Preserves_S _ exp_univ_exp (@S).
Proof. constructor; intros; assumption. Defined.

Definition fresh_copies (S : Ensemble cps.var) (l : list cps.var) : Prop :=
  Disjoint _ S (FromList l) /\ NoDup l.

Inductive uncurry_step : exp -> exp -> Prop :=
| uncurry_cps :
  forall (C : frames_t exp_univ_fundefs exp_univ_exp)
    (f f1 : var) (ft ft1 : fun_tag) (k k' : var) (kt : fun_tag) (fv fv1 : list var)
    (g g' : var) (gt : fun_tag) (gv gv1 : list var) (ge : exp) (fds : fundefs)
    (lhs rhs : fundefs) (s : Ensemble cps.var) (next_x : cps.var),
  (* Non-linear LHS constraints *)
  k = k' /\
  g = g' /\
  (* Guards: *)
  (* (1) g can't be recursive or invoke k *)
  ~ ![g] \in used_vars ![ge] /\
  ~ ![k] \in used_vars ![ge] /\
  (* (2) gv1, fv1, f1 must be fresh and contain no duplicates *)
  lhs = Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds /\
  rhs = Fcons f ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
        (Fcons f1 ft1 (gv ++ fv) ge (Rec fds)) /\
  s = used_vars (exp_of_proto (C ⟦ lhs ⟧)) /\
  fresh_copies s ![gv1] -> length gv1 = length gv /\
  fresh_copies (s :|: FromList ![gv1]) ![fv1] -> length fv1 = length fv /\
  ~ ![f1] \in (s :|: FromList ![gv1] :|: FromList ![fv1]) /\
  (* (3) next_x must be a fresh variable *)
  fresher_than next_x (s :|: FromList ![gv1] :|: FromList ![fv1]) /\
  True (* - TODO: fun_tag stuff *) ->
  (* 'Irrelevant' guard *)
  When (fun (r : miscR) (s : miscS) =>
    (* g must not have been already uncurried by an earlier pass *)
    match cps.M.get ![g] (fst s) with
    | Some true => true
    | _ => false
    end) ->
  (* The rewrite *)
  uncurry_step
    (C ⟦ Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds ⟧)
    (C ⟦ (* Mark g as uncurried and set a flag (used to iterate to fixed point) *)
         Modify (fun '(s, _) => (PM.set (un_var g) true s, true))
         (* Rewrite f as a wrapper around the uncurried f1 *)
         (Fcons f ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
         (Fcons f1 ft1 (gv ++ fv) ge (Rec fds))) ⟧).

Definition rw_cp : rewriter exp_univ_exp uncurry_step miscR miscS (@delay_t) (@R_C) (@R_e) (@S).
Proof.
  mk_rw;
    (* This particular rewriter's delayed computation is just the identity function,
        so ConstrDelay and EditDelay are easy *)
    try lazymatch goal with
    | |- ConstrDelay _ -> _ =>
      clear; simpl; intros; lazymatch goal with H : forall _, _ |- _ => eapply H; try reflexivity; eauto end
    | |- EditDelay _ -> _ =>
      clear; simpl; intros; lazymatch goal with H : forall _, _ |- _ => eapply H; try reflexivity; eauto end
    end.
  (* Obligation 1 of 2: explain how to satisfy side conditions for the rewrite *)
  - intros.
    rename X into success, H0 into failure.
    (* Check nonlinearities *)
    destruct k as [k], k' as [k'], g as [g], g' as [g'].
    destruct (eq_var k k') eqn:Hkk'; [|exact failure].
    destruct (eq_var g g') eqn:Hgg'; [|exact failure].
    rewrite Pos.eqb_eq in Hkk', Hgg'.
    (* Check whether g has already been uncurried before *)
    destruct (Maps.PTree.get ![mk_var g] (fst ms)) as [[|]|]; [|exact failure..].
    (* Check that {g, k} ∩ vars(ge) = ∅ *)
    idtac "TODO: occurs_in_exp".
    (* Generate f1, ft1, fv1, gv1, next_x *)
    idtac "TODO: generate f1, ft1, fv1, gv1, next_x".
    (* Prove that these satisfy the proper preconditions *)
    idtac "TODO: vars proof".
    admit.
  (* Obligation 2 of 2: explain how to maintain fresh name invariant across edit *)
  - clear; intros.
    (* Env is easy, because the uncurryer doesn't need it *)
    split; [exact tt|].
    (* For state, need create a fresh variable. Thankfully, we have one: next_x *)
    exists next_x; unfold Modify, Rec.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    eapply fresher_than_antimon; [|eassumption].
    admit.
Admitted.
