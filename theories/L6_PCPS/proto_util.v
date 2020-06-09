Require Import Coq.Strings.String Coq.Classes.Morphisms Coq.Relations.Relations.
Require Import Coq.PArith.BinPos Coq.Sets.Ensembles Lia.
Require Import L6.identifiers L6.Prototype L6.cps_proto.
Require Import L6.Ensembles_util.

Require Import Coq.Lists.List.
Import ListNotations.

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

Definition fresh_copies (S : Ensemble cps.var) (l : list var) : Prop := Disjoint _ S (FromList ![l]) /\ NoDup l.

Definition gensym (x : cps.var) : cps.var * var := (x + 1, [x]!)%positive.

Lemma gensym_spec x S x' y : 
  fresher_than x S ->
  (x', y) = gensym x ->
  ~ ![y] \in S /\ fresher_than x' (![y] |: S).
Proof.
  destruct y as [y]; unfold gensym; intros Hfresh Hgen; split.
  - intros Hy.
    assert (y = x) by now simpl in *.
    assert (x > y)%positive by now apply Hfresh.
    lia.
  - unfold isoAofB, Iso_var in *; assert (x' = (x + 1)%positive) by easy; assert (y = x) by easy.
    assert (x' > y)%positive by lia.
    apply fresher_than_Union; [|eapply fresher_than_monotonic; try eassumption; lia].
    simpl; intros z Hz; inversion Hz; lia.
Qed.

Fixpoint gensyms {A} (x : cps.var) (xs : list A) : cps.var * list var :=
  match xs with
  | [] => (x, [])
  | _ :: xs => let '(x', xs') := gensyms (x + 1)%positive xs in (x', mk_var x :: xs')
  end.

Lemma gensyms_len' {A} : forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> length xs' = length xs.
Proof.
  intros x xs; revert x; induction xs as [|x xs IHxs]; intros x0 x' xs' Hgen; [simpl in Hgen; now inv Hgen|].
  unfold gensyms in Hgen; fold @gensyms in Hgen.
  destruct (gensyms (x0 + 1)%positive xs) as [x'' xs''] eqn:Hx0; inv Hgen; now simpl.
Qed.

Lemma gensyms_increasing' {A} :
  forall x (xs : list A) x' xs', (x', xs') = gensyms x xs -> 
  forall y, List.In y xs' -> (![y] >= x)%positive.
Proof.
  intros x xs; revert x; induction xs as [|x xs IHxs]; intros x0 x' xs' Hgen [y] Hy;
    [simpl in Hgen; now inv Hgen|].
  unfold gensyms in Hgen; fold @gensyms in Hgen.
  destruct (gensyms (x0 + 1)%positive xs) as [x'' xs''] eqn:Hx0; inv Hgen; simpl.
  simpl in Hy; destruct Hy as [H|H]; [inversion H; simpl; lia|].
  specialize IHxs with (x := (x0 + 1)%positive) (y := mk_var y).
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
    specialize (IHxs (x + 1)%positive); rewrite Hxs' in IHxs; unfold fst in IHxs.
    destruct IHxs; lia.
  - unfold gensyms in *; fold @gensyms in *.
    destruct (gensyms _ _) as [x' xs'] eqn:Hxs'; unfold fst; unfold snd in Hy.
    specialize (IHxs (x + 1)%positive); rewrite Hxs' in IHxs; unfold fst in IHxs.
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
  specialize (IHxs (x + 1)%positive); rewrite Hxs' in IHxs; unfold snd in IHxs.
  constructor; [|auto].
  pose (Hinc := gensyms_increasing' (x + 1)%positive xs); clearbody Hinc.
  rewrite Hxs' in Hinc; unfold snd in Hinc.
  remember (snd (gensyms (x + 1)%positive xs)) as ys; clear - Hinc.
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
    destruct (gensyms (y + 1)%positive xs) as [x'' xs''] eqn:Hxs.
    inversion Hgen; subst; simpl; normalize_sets.
    apply Union_Disjoint_r; [|eapply (IHxs (y + 1)%positive); eauto; try lia].
    + unfold fresher_than in Hfresh.
      constructor; intros arb; intros HSx; unfold Ensembles.In in HSx.
      destruct HSx as [arb HS Hx]; inversion Hx; subst.
      specialize (Hfresh _ HS); lia.
    + eapply fresher_than_monotonic; eauto; lia.
Qed.

Ltac show_Disjoint arb Harbx Harby :=
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

Section RunRewriter.

Context 
  {root : exp_univ} {R : relation (univD root)}
  {R_misc S_misc : Set}
  {D : forall A, univD A -> Set} `{@Delayed exp_univ Frame_exp (@D)}
  {R_C : forall A, frames_t A root -> Set}
  {R_e : forall A, univD A -> Set}
  {St : forall A, frames_t A root -> univD A -> Set}
  `{@Preserves_R_C exp_univ Frame_exp root (@R_C)}
  `{@Preserves_S exp_univ Frame_exp root (@St)}
  (rw : rewriter root R R_misc S_misc (@D) (@R_C) (@R_e) (@St)).

Definition run_rewriter' :
  R_misc -> S_misc -> forall (e : univD root), R_C _ <[]> -> R_e _ e -> St _ <[]> e ->
  result root R S_misc (@St) <[]> e.
Proof.
  intros mr ms e r_C r_e st; unfold rewriter, rw_for in rw.
  specialize (rw lots_of_fuel mr ms _ <[]> e (delay_id _)).
  rewrite delay_id_law in rw; exact (rw r_C r_e st).
Defined.

Definition run_rewriter (mr : R_misc) (ms : S_misc) (e : univD root)
           (r_C : R_C _ <[]>) (r_e : R_e _ e) (st : St _ <[]> e) : univD root :=
  let '{| resTree := e' |} := run_rewriter' mr ms e r_C r_e st in e'.

End RunRewriter.

Definition trivial_R_C {A} (C : exp_c A exp_univ_exp) : Set := unit.
Instance Preserves_R_C_trivial_R_C : Preserves_R_C _ exp_univ_exp (@trivial_R_C). Proof. constructor. Defined.

Definition trivial_R_e {A} (e : univD A) : Set := unit.
Instance Preserves_R_e_trivial_R_e : Preserves_R_e _ (@trivial_R_e). Proof. constructor. Defined.

Definition trivial_delay_t {A} (e : univD A) : Set := unit.
Instance Delayed_trivial_delay_t : Delayed (@trivial_delay_t).
Proof. unshelve econstructor; [intros A e _; exact e|..]; reflexivity. Defined.

Definition S_fresh {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set :=
  {x | fresher_than x (used_vars ![C ⟦ e ⟧])}.

(* We don't have to do anything to preserve a fresh variable as we move around *)
Instance Preserves_S_S_fresh : Preserves_S _ exp_univ_exp (@S_fresh).
Proof. constructor; intros; assumption. Defined.
