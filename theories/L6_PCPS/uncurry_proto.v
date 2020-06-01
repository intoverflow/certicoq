(** Uncurrying written as a guarded rewrite rule *)

Require Import Coq.Strings.String Coq.Classes.Morphisms.
Require Import Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Lia.
Require Import L6.Prototype.
Require Import L6.cps_proto.
Require Import identifiers.  (* for max_var, occurs_in_exp, .. *)
Require Import AltBinNotations.
Require Import L6.Ensembles_util L6.List_util L6.cps_util L6.state.

Require Import Coq.Lists.List.
Import ListNotations.

Require L6.cps.

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
   4 - Map for uncurried functions for a version of inlining
*)
Definition S_misc : Set := (bool * arity_map * local_map * St * comp_data). 

Definition delay_t {A} (e : univD A) : Set := unit.

Definition R_C {A} (C : exp_c A exp_univ_exp) : Set := unit.
Definition R_e {A} (e : univD A) : Set := unit.

Definition fresher_than (x : cps.var) (S : Ensemble cps.var) : Prop :=
  forall y, y \in S -> (x > y)%positive.

Lemma fresher_than_not_In x S : fresher_than x S -> ~ x \in S.
Proof. intros Hfresh Hin; assert (x > x)%positive by now apply Hfresh. lia. Qed.

Lemma fresher_than_antimon x S1 S2 : S1 \subset S2 -> fresher_than x S2 -> fresher_than x S1.
Proof. intros HS12 Hfresh y Hy; apply Hfresh, HS12, Hy. Qed.

Lemma fresher_than_monotonic x y S : (y >= x -> fresher_than x S -> fresher_than y S)%positive.
Proof. intros Hxy Hfresh z Hz. assert (x > z)%positive by now apply Hfresh. lia. Qed.

Lemma fresher_than_Union x S1 S2 : fresher_than x S1 -> fresher_than x S2 -> fresher_than x (S1 :|: S2).
Proof. intros HS1 HS2 y Hy; destruct Hy as [y Hy|y Hy]; auto. Qed.

Instance Proper_fresher_than_r : Proper (Logic.eq ==> Same_set _ ==> iff) fresher_than.
Proof.
  unfold Proper, "==>", fresher_than.
  intros x y Hxy x0 y0 Hxy0; subst; split; intros Hforall dummy; now (rewrite <- Hxy0 || rewrite Hxy0).
Qed.

Definition S {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set :=
  {x | fresher_than x (used_vars ![C ⟦ e ⟧])}.

Instance Delayed_delay_t : Delayed (@delay_t).
Proof. unshelve econstructor; [intros A e _; exact e|..]; reflexivity. Defined.
Instance Preserves_R_C_R_C : Preserves_R_C _ exp_univ_exp (@R_C). Proof. constructor. Defined.
Instance Preserves_R_e_R_e : Preserves_R_e _ (@R_e). Proof. constructor. Defined.

(* We don't have to do anything to preserve a fresh variable as we move around *)
Instance Preserves_S_S : Preserves_S _ exp_univ_exp (@S). Proof. constructor; intros; assumption. Defined.

Definition fresh_copies (S : Ensemble cps.var) (l : list var) : Prop := Disjoint _ S (FromList ![l]) /\ NoDup l.

(* Uncurrying as a guarded rewrite rule *)
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
  (* (4) ft1 is the appropriate fun_tag and ms is an updated misc state. *)
  fp_numargs = length fv + length gv /\
  (True \/ let '(_, aenv, _, _) := ms in cps.M.get ![ft1] aenv <> None) -> (* TODO: proper side condition *)
  (* 'Irrelevant' guard *)
  When (fun (r : R_misc) (s : S_misc) =>
    let '(b, aenv, lm, s, cdata) := s in
    (* g must not have been already uncurried by an earlier pass *)
    match cps.M.get ![g] lm with
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
           let lm := cps.M.set ![g] true lm in
           (* Update inlining heuristic so inliner knows to inline fully saturated calls to f *)
           let s := (max (fst s) fp_numargs, (cps.M.set ![f] 1 (cps.M.set ![g] 2 (snd s)))) in
           (true, aenv, lm, s, cdata) : S_misc)
         (* Rewrite f as a wrapper around the uncurried f1 and recur on fds *)
         (Fcons f ft (k :: fv1) (Efun (Fcons g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1)) Fnil) (Eapp k kt [g]))
         (Fcons f1 ft1 (gv ++ fv) ge (Rec fds))) ⟧).

Fixpoint gensyms {A} (x : cps.var) (xs : list A) : cps.var * list var :=
  match xs with
  | [] => (x, [])
  | _ :: xs => let '(x', xs') := gensyms (1 + x)%positive xs in (x', mk_var x :: xs')
  end.

Lemma gensyms_len' {A} : forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> length xs' = length xs.
Proof.
  intros x xs; revert x; induction xs as [|x xs IHxs]; intros x0 x' xs' Hgen; [simpl in Hgen; now inv Hgen|].
  unfold gensyms in Hgen; fold @gensyms in Hgen.
  destruct (gensyms (1 + x0)%positive xs) as [x'' xs''] eqn:Hx0; inv Hgen; now simpl.
Qed.

Lemma gensyms_increasing' {A} :
  forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> 
  forall y, List.In y xs' -> (![y] >= x)%positive.
Proof.
  intros x xs; revert x; induction xs as [|x xs IHxs]; intros x0 x' xs' Hgen [y] Hy;
    [simpl in Hgen; now inv Hgen|].
  unfold gensyms in Hgen; fold @gensyms in Hgen.
  destruct (gensyms (1 + x0)%positive xs) as [x'' xs''] eqn:Hx0; inv Hgen; simpl.
  simpl in Hy; destruct Hy as [H|H]; [inversion H; simpl; lia|].
  specialize IHxs with (x := (1 + x0)%positive) (y := mk_var y).
  rewrite Hx0 in IHxs; unfold snd in IHxs.
  specialize (IHxs x'' xs'' eq_refl H); unfold isoBofA, Iso_var, un_var in IHxs; lia.
Qed.

Local Ltac mk_corollary parent := 
  intros x xs x' xs';
  pose (Hparent := parent _ x xs); clearbody Hparent; intros H;
  destruct (gensyms x xs); now inversion H.

Lemma gensyms_upper {A} x (xs : list A) :
  (fst (gensyms x xs) >= x)%positive /\
  forall y, List.In y (snd (gensyms x xs)) -> (fst (gensyms x xs) > ![y])%positive.
Proof.
  revert x; induction xs; [simpl; split; [lia|easy]|intros x; split; [|intros [y] Hy]].
  - unfold gensyms; fold @gensyms.
    destruct (gensyms _ _) as [x' xs'] eqn:Hxs'; unfold fst.
    specialize (IHxs (1 + x)%positive); rewrite Hxs' in IHxs; unfold fst in IHxs.
    destruct IHxs; lia.
  - unfold gensyms in *; fold @gensyms in *.
    destruct (gensyms _ _) as [x' xs'] eqn:Hxs'; unfold fst; unfold snd in Hy.
    specialize (IHxs (1 + x)%positive); rewrite Hxs' in IHxs; unfold fst in IHxs.
    destruct IHxs as [IHxs IHxsy].
    destruct Hy as [Hy|Hy]; [inversion Hy; simpl; lia|].
    now specialize (IHxsy (mk_var y) Hy).
Qed.

Corollary gensyms_upper1 {A} : forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> (x' >= x)%positive.
Proof. mk_corollary @gensyms_upper. Qed.

Corollary gensyms_upper2 {A} :
  forall x (xs : list A) x' xs', (x', xs') = gensyms x xs ->
  forall y, List.In y xs' -> (x' > ![y])%positive.
Proof. mk_corollary @gensyms_upper. Qed.

Lemma gensyms_NoDup {A} x (xs : list A) : NoDup (snd (gensyms x xs)).
Proof.
  revert x; induction xs; intros; [now constructor|].
  unfold gensyms; fold @gensyms.
  destruct (gensyms _ _) as [x' xs'] eqn:Hxs'; unfold snd.
  specialize (IHxs (1 + x)%positive); rewrite Hxs' in IHxs; unfold snd in IHxs.
  constructor; [|auto].
  pose (Hinc := gensyms_increasing' (1 + x)%positive xs); clearbody Hinc.
  rewrite Hxs' in Hinc; unfold snd in Hinc.
  remember (snd (gensyms (1 + x)%positive xs)) as ys; clear - Hinc.
  induction xs'; auto.
  specialize (Hinc x' (a :: xs')).
  intros [|Hin_ys]; [|apply IHxs'; auto; intros; apply Hinc; auto; now right].
  assert (Hxa : In (mk_var x) (a :: xs')) by now left.
  specialize (Hinc eq_refl (mk_var x) Hxa); unfold isoBofA, Iso_var, un_var in Hinc; lia.
Qed.

Corollary gensyms_NoDup' {A} : forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> NoDup xs'.
Proof. mk_corollary @gensyms_NoDup. Qed.

Lemma gensyms_fresher_than {A} (xs : list A) :
  forall x y S x' xs',
  fresher_than x S ->
  (y >= x)%positive ->
  (x', xs') = gensyms y xs ->
  Disjoint _ S (FromList ![xs']).
Proof.
  induction xs.
  - simpl; intros x y S x' xs' Hfresh Hyx Hgen; inversion Hgen; subst.
    simpl; normalize_sets; eauto with Ensembles_DB.
  - unfold gensyms; fold @gensyms; intros x y S x' xs' Hfresh Hyx Hgen.
    destruct (gensyms (1 + y)%positive xs) as [x'' xs''] eqn:Hxs.
    inversion Hgen; subst; simpl; normalize_sets.
    apply Union_Disjoint_r; [|eapply (IHxs (1 + y)%positive); eauto; try lia].
    + unfold fresher_than in Hfresh.
      constructor; intros arb; intros HSx; unfold Ensembles.In in HSx.
      destruct HSx as [arb HS Hx]; inversion Hx; subst.
      specialize (Hfresh _ HS); lia.
    + eapply fresher_than_monotonic; eauto; lia.
Qed.

Local Ltac show_Disjoint arb Harbx Harby :=
  let Harb := fresh "Harb" in
  constructor; intros arb Harb; unfold Ensembles.In in Harb;
  destruct Harb as [arb Harbx Harby].

Lemma gensyms_disjoint {A B} (xs : list A) (ys : list B) x0 x1 x2 xs' ys' :
  (x1, xs') = gensyms x0 xs ->
  (x2, ys') = gensyms x1 ys ->
  Disjoint _ (FromList ![xs']) (FromList ![ys']).
Proof.
  intros Hxs' Hys'; show_Disjoint arb Harbx Harby.
  unfold Ensembles.In, FromList in Harbx, Harby.
  apply (in_map mk_var) in Harbx; apply (in_map mk_var) in Harby.
  simpl in Harbx, Harby; normalize_roundtrips.
  assert (x1 > ![mk_var arb])%positive by (eapply gensyms_upper2; eassumption); simpl in *.
  assert (![mk_var arb] >= x1)%positive by (eapply gensyms_increasing'; eassumption); simpl in *.
  lia.
Qed.

Lemma gensyms_list_fresher {A} x y (ys : list A) y' ys' S :
  fresher_than x S ->
  (y >= x)%positive ->
  (y', ys') = gensyms y ys ->
  Disjoint _ S (FromList ![ys']).
Proof.
  intros Hfresh Hyx Hgen; show_Disjoint arb Harbx Harby.
  unfold Ensembles.In, FromList in Harby.
  apply (in_map mk_var) in Harby; simpl in Harby; normalize_roundtrips.
  assert (![mk_var arb] >= y)%positive by (eapply gensyms_increasing'; eauto); simpl in *.
  assert (x > arb)%positive by now apply Hfresh.
  lia.
Qed.

Lemma gensyms_spec {A} x S (xs : list A) x' xs' : 
  fresher_than x S ->
  (x', xs') = gensyms x xs ->
  fresh_copies S xs' /\ fresher_than x' (S :|: FromList ![xs']) /\ length xs' = length xs.
Proof.
  intros Hfresh Hgen; unfold fresh_copies; split; [split|split].
  - show_Disjoint arb Harbx Harby.
    unfold Ensembles.In, FromList in Harby; apply (in_map mk_var) in Harby.
    simpl in Harby; normalize_roundtrips.
    assert (x > arb)%positive by now apply Hfresh.
    assert (![mk_var arb] >= x)%positive by (eapply gensyms_increasing'; eauto).
    simpl in *; lia.
  - eapply gensyms_NoDup'; eauto.
  - intros y Hy; destruct Hy as [y Hy|y Hy].
    + assert (x > y)%positive by now apply Hfresh.
      assert (x' >= x)%positive by (eapply gensyms_upper1; eauto); lia.
    + unfold Ensembles.In, FromList in Hy; apply (in_map mk_var) in Hy.
      simpl in Hy; normalize_roundtrips.
      change y with ![mk_var y].
      eapply gensyms_upper2; eauto.
  - eapply gensyms_len'; eauto.
Qed.

Lemma bool_true_false b : b = false -> b <> true. Proof. now destruct b. Qed.

Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

(* Uncurrying as a recursive function *)
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
    destruct (cps.M.get g lm) as [[|]|] eqn:Huncurried; [|exact failure..].
    (* Check that {g, k} ∩ vars(ge) = ∅ *)
    destruct (occurs_in_exp g ![ge]) eqn:Hocc_g; [exact failure|]. (* TODO: avoid the conversion *)
    destruct (occurs_in_exp k ![ge]) eqn:Hocc_k; [exact failure|]. (* TODO: avoid the conversion *)
    apply bool_true_false in Hocc_g; apply bool_true_false in Hocc_k.
    rewrite occurs_in_exp_iff_used_vars in Hocc_g, Hocc_k.
    (* Generate ft1 + new misc state ms *)
    idtac "TODO: generate ft1 and new misc state ms".
    specialize success with (ft1 := mk_fun_tag xH). (* Until comp_data : Set, put some bogus stuff *)
    specialize success with (ms := ms).
    (* Generate f1, fv1, gv1, next_x *)
    destruct s as [next_x Hnext_x].
    clearpose Hxgv1 xgv1 (gensyms next_x gv); destruct xgv1 as [next_x0 gv1].
    clearpose Hxfv1 xfv1 (gensyms next_x0 fv); destruct xfv1 as [next_x1 fv1].
    clearpose Hf1 f1 next_x1.
    (* Prove that all the above code actually satisfies the side condition *)
    assert (next_x0 >= next_x)%positive by (eapply gensyms_upper1; eassumption).
    assert (next_x1 >= next_x0)%positive by (eapply gensyms_upper1; eassumption).
    edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|].
    edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|].
    eapply success with (f1 := mk_var f1) (fv1 := fv1) (gv1 := gv1) (next_x := (next_x1 + 1)%positive);
      repeat match goal with |- _ /\ _ => split end;
      try solve [reflexivity|eassumption|subst;reflexivity].
    + apply fresher_than_not_In; subst f1; exact Hfresh_fv.
    + apply fresher_than_Union; [|subst; simpl; intros y Hy; inversion Hy; lia].
      eapply fresher_than_monotonic; eauto; lia.
    + left; exact I. (* TODO replace with actual proof *)
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
