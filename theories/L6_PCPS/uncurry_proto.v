(** Uncurrying written as a guarded rewrite rule *)

Require Import Coq.Strings.String Coq.Classes.Morphisms.
Require Import Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Lia.
Require Import L6.Prototype L6.proto_util.
Require Import L6.cps_proto.
Require Import identifiers.  (* for max_var, occurs_in_exp, .. *)
Require Import AltBinNotations.
Require Import L6.Ensembles_util L6.List_util L6.cps_util L6.state.

Require Import Coq.Lists.List.
Import ListNotations.

Require L6.cps.

(** * Auxiliary data used by the rewriter *)

Definition R_misc : Set := unit.

(* pair of 
   1 - max number of arguments 
   2 - encoding of inlining decision for beta-contraction phase *)
Definition St : Set := (nat * (cps.PM nat))%type.
(* 0 -> Do not inline, 1 -> uncurried function, 2 -> continuation of uncurried function *)

(* Maps (arity+1) to the right fun_tag *)
Definition arity_map : Set := cps.PM fun_tag.
Definition local_map : Set := cps.PM bool.
 
(* The state for this includes 
   1 - a boolean for tracking whether or not a reduction happens
   2 - Map recording the (new) fun_tag associated to each arity
   3 - local map from var to if function has already been uncurried
   4 - Map for uncurried functions for a version of inlining *)
Definition S_misc : Set := (bool * arity_map * local_map * St * comp_data). 

Definition delay_t {A} (e : univD A) : Set := unit.

Definition R_C {A} (C : exp_c A exp_univ_exp) : Set := unit.
Definition R_e {A} (e : univD A) : Set := unit.

Definition S {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set :=
  {x | fresher_than x (used_vars ![C ⟦ e ⟧])}.

Instance Delayed_delay_t : Delayed (@delay_t).
Proof. unshelve econstructor; [intros A e _; exact e|..]; reflexivity. Defined.
Instance Preserves_R_C_R_C : Preserves_R_C _ exp_univ_exp (@R_C). Proof. constructor. Defined.
Instance Preserves_R_e_R_e : Preserves_R_e _ (@R_e). Proof. constructor. Defined.

(* We don't have to do anything to preserve a fresh variable as we move around *)
Instance Preserves_S_S : Preserves_S _ exp_univ_exp (@S). Proof. constructor; intros; assumption. Defined.

(** * Uncurrying as a guarded rewrite rule *)

Inductive uncurry_step : exp -> exp -> Prop :=
| uncurry_cps :
  forall (C : frames_t exp_univ_fundefs exp_univ_exp)
    (f f1 : var) (ft ft1 : fun_tag) (k k' : var) (kt : fun_tag) (fv fv1 : list var)
    (g g' : var) (gt : fun_tag) (gv gv1 : list var) (ge : exp) (fds : fundefs)
    (lhs rhs : fundefs) (s : Ensemble cps.var) (next_x : cps.var)
    (fp_numargs : nat) (ms : S_misc),
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
  fresh_copies s gv1 -> length gv1 = length gv /\
  fresh_copies (s :|: FromList ![gv1]) fv1 -> length fv1 = length fv /\
  ~ ![f1] \in (s :|: FromList ![gv1] :|: FromList ![fv1]) /\
  (* (3) next_x must be a fresh variable *)
  fresher_than next_x (s :|: FromList ![gv1] :|: FromList ![fv1] :|: [set ![f1]]) /\
  (* (4) misc. let bindings (needed for computation of new ms) *)
  fp_numargs = length fv + length gv -> ms = ms ->
  (* 'Irrelevant' guard *)
  When (fun (r : R_misc) (s : S_misc) =>
    let '(b, aenv, lm, s, cdata) := s in
    (* g must not have been already uncurried by an earlier pass *)
    match M.get ![g] lm with
    | Some true => true
    | _ => false
    end) ->
  (* The rewrite *)
  uncurry_step
    (C ⟦ Fcons f ft (k :: fv) (Efun (Fcons g gt gv ge Fnil) (Eapp k' kt [g'])) fds ⟧)
    (C ⟦ Put (
           let '(b, aenv, lm, s, cdata) := ms in
           (* Set flag to indicate that a rewrite was performed (used to iterate to fixed point) *)
           let b := true in
           (* Mark g as uncurried *)
           let lm := M.set ![g] true lm in
           (* Update inlining heuristic so inliner knows to inline fully saturated calls to f *)
           let s := (max (fst s) fp_numargs, (M.set ![f] 1 (M.set ![g] 2 (snd s)))) in
           (true, aenv, lm, s, cdata) : S_misc)
         (* Rewrite f as a wrapper around the uncurried f1 and recur on fds *)
         (Fcons f ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
         (Fcons f1 ft1 (gv ++ fv) ge (Rec fds))) ⟧).

(** * Uncurrying as a recursive function *)

(* Based on [get_fun_tag] from uncurry.v *)
Definition get_fun_tag (n : N) (ms : S_misc) : fun_tag * S_misc :=
  let '(b, aenv, lm, s, cdata) := ms in
  let n' := N.succ_pos n in
  match M.get n' aenv with
  | Some ft => (ft, ms)
  | None =>
    let '(mft, (cdata, tt)) := compM.runState (get_ftag n) tt (cdata, tt) in
    match mft with
    | compM.Err _ => (mk_fun_tag xH, ms) (* bogus *)
    | compM.Ret ft =>
      let ft := mk_fun_tag ft in
      (ft, (b, M.set n' ft aenv, lm, s, cdata))
    end
  end.

Lemma bool_true_false b : b = false -> b <> true. Proof. now destruct b. Qed.

Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

Definition uncurry_proto : rewriter exp_univ_exp uncurry_step R_misc S_misc (@delay_t) (@R_C) (@R_e) (@S).
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
  - intros. rename X into success, H0 into failure.
    (* Check nonlinearities *)
    destruct k as [k], k' as [k'], g as [g], g' as [g'].
    destruct (eq_var k k') eqn:Hkk'; [|exact failure].
    destruct (eq_var g g') eqn:Hgg'; [|exact failure].
    rewrite Pos.eqb_eq in Hkk', Hgg'.
    (* Check whether g has already been uncurried before *)
    destruct ms as [[[[b aenv] lm] heuristic] cdata] eqn:Hms.
    destruct (M.get g lm) as [[|]|] eqn:Huncurried; [|exact failure..].
    (* Check that {g, k} ∩ vars(ge) = ∅ *)
    destruct (occurs_in_exp g ![ge]) eqn:Hocc_g; [exact failure|]. (* TODO: avoid the conversion *)
    destruct (occurs_in_exp k ![ge]) eqn:Hocc_k; [exact failure|]. (* TODO: avoid the conversion *)
    apply bool_true_false in Hocc_g; apply bool_true_false in Hocc_k.
    rewrite occurs_in_exp_iff_used_vars in Hocc_g, Hocc_k.
    (* Generate ft1 + new misc state ms *)
    pose (fp_numargs := length fv + length gv).
    destruct (get_fun_tag (N.of_nat fp_numargs) ms) as [ft1 ms'] eqn:Hget_ft.
    specialize success with (ft1 := ft1) (ms := ms') (fp_numargs := fp_numargs).
    (* Generate f1, fv1, gv1, next_x *)
    destruct s as [next_x Hnext_x].
    clearpose Hxgv1 xgv1 (gensyms next_x gv); destruct xgv1 as [next_x0 gv1].
    clearpose Hxfv1 xfv1 (gensyms next_x0 fv); destruct xfv1 as [next_x1 fv1].
    clearpose Hf1 f1 next_x1.
    specialize success with (f1 := mk_var f1) (fv1 := fv1) (gv1 := gv1) (next_x := (next_x1 + 1)%positive).
    (* Prove that all the above code actually satisfies the side condition *)
    edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|].
    edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|].
    eapply success; repeat match goal with |- _ /\ _ => split end;
      try solve [reflexivity|eassumption|subst;reflexivity].
    + apply fresher_than_not_In; subst f1; exact Hfresh_fv.
    + apply fresher_than_Union; [|subst; simpl; intros y Hy; inversion Hy; lia].
      eapply fresher_than_monotonic; eauto; lia.
    + destruct (Maps.PTree.get _ _) as [[|]|] eqn:Hget'; [reflexivity|inversion Huncurried..].
  (* Obligation 2 of 2: explain how to maintain fresh name invariant across edit *)
  - clear; unfold Put, Rec; intros.
    (* Env is easy, because the uncurryer doesn't need it *)
    split; [exact tt|].
    (* For state, need create a fresh variable. Thankfully, we have one: next_x *)
    exists next_x; repeat match goal with H : _ /\ _ |- _ => destruct H end.
    eapply fresher_than_antimon; [|eassumption].
    rewrite used_iso, isoABA, used_app.
    subst s lhs. change (exp_of_proto ?A) with ![A].
    rewrite used_iso, isoABA, used_app.
    unfold used; simpl; unbox_newtypes.
    do 10 normalize_used_vars'; repeat normalize_sets.
    repeat rewrite strip_vars_app; repeat normalize_sets.
    intros arbitrary; repeat rewrite In_or_Iff_Union; tauto.
Defined.

Recursive Extraction uncurry_proto.
