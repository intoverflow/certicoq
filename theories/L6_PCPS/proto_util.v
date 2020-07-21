Require Import Coq.Strings.String Coq.Classes.Morphisms Coq.Relations.Relations.
Require Import Coq.PArith.BinPos Coq.Sets.Ensembles Lia.
Require Import L6.identifiers L6.Prototype L6.cps_proto.
Require Import L6.Ensembles_util L6.shrink_cps L6.map_util.

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
  {Root : exp_univ} {fueled : bool} {metric : Metric Root fueled} {Rstep : relation (univD Root)}
  {D : Set} {I_D : forall A, univD A -> D -> Prop} `{@Delayed _ Frame_exp D I_D}
  {R : Set} {I_R : forall A, frames_t A Root -> R -> Prop}
  {S : Set} {I_S : forall A, frames_t A Root -> univD A -> S -> Prop}
  `{@Preserves_R _ Frame_exp _ R I_R}
  `{@Preserves_S_dn _ Frame_exp _ S I_S}
  `{@Preserves_S_up _ Frame_exp _ S I_S}
  (rw : rewriter Root fueled metric Rstep D I_D R I_R S I_S).

Definition run_rewriter' :
  forall (e : univD Root), Param I_R (erase <[]>) -> State I_S (erase <[]>) e ->
  result Rstep I_S (erase <[]>) e.
Proof.
  intros e r s; unfold rewriter, rewriter', rw_for in rw.
  destruct fueled.
  - specialize (rw lots_of_fuel _ (erase <[]>) _ e (delay_id _)).
    rewrite delay_id_law in rw.
    specialize (rw (erase (Pos.to_nat lots_of_fuel)) _ r s); apply rw; unerase.
    unfold run_metric; destruct metric; reflexivity.
  - specialize (rw I _ (erase <[]>) _ e (delay_id _)).
    rewrite delay_id_law in rw; unshelve eapply rw;
    try lazymatch goal with
    | |- erased nat => refine (erase _)
    | |- Param _ _ => assumption
    | |- State _ _ _ => assumption
    end;
    try lazymatch goal with
    | |- e_ok (erase _) => apply erase_ok
    | |- «_» => unerase; reflexivity
    end.
Defined.

Definition run_rewriter (e : univD Root)
           (r : Param I_R (erase <[]>)) (s : State I_S (erase <[]>) e) : univD Root :=
  let '{| resTree := e' |} := run_rewriter' e r s in e'.

End RunRewriter.

Definition I_S_fresh {A} (C : exp_c A exp_univ_exp) (e : univD A) (x : cps.var) : Prop :=
  fresher_than x (used_vars ![C ⟦ e ⟧]).

(* We don't have to do anything to preserve a fresh variable as we move around *)
Instance Preserves_S_dn_S_fresh : Preserves_S_dn (@I_S_fresh).
Proof. unfold Preserves_S_dn; intros A B C C_ok f x s; exact s. Defined.
Instance Preserves_S_up_S_fresh : Preserves_S_up (@I_S_fresh).
Proof. unfold Preserves_S_up; intros A B C C_ok f x s; exact s. Defined.
Extraction Inline Preserves_S_dn_S_fresh Preserves_S_up_S_fresh.

(* Compute an initial fresh variable *)
Definition initial_fresh (e : exp) : State (@I_S_fresh) (erase <[]>) e.
Proof.
  exists (1 + max_var ![e] 1)%positive; unerase; unfold I_S_fresh.
  change (![ <[]> ⟦ ?e ⟧ ]) with ![e]; unfold fresher_than.
  intros y Hy; enough (y <= max_var ![e] 1)%positive by lia.
  destruct Hy; [now apply bound_var_leq_max_var|now apply occurs_free_leq_max_var].
Defined.

(* Some passes assume unique bindings *)
Definition I_S_uniq {A} (C : exp_c A exp_univ_exp) (e : univD A) (_ : unit) : Prop :=
  unique_bindings ![C ⟦ e ⟧].
Instance Preserves_S_dn_S_uniq : Preserves_S_dn (@I_S_uniq).
Proof. unfold Preserves_S_dn; intros A B C C_ok f x s; exact s. Defined.
Instance Preserves_S_up_S_uniq : Preserves_S_up (@I_S_uniq).
Proof. unfold Preserves_S_up; intros A B C C_ok f x s; exact s. Defined.
Extraction Inline Preserves_S_dn_S_uniq Preserves_S_up_S_uniq.

(* Additional facts about variables *)

Fixpoint bound_var_ces (ces : list (cps.ctor_tag * cps.exp)) :=
  match ces with
  | [] => Empty_set _
  | (c, e) :: ces => bound_var e :|: bound_var_ces ces
  end.

Lemma bound_var_Ecase x ces : bound_var (cps.Ecase x ces) <--> bound_var_ces ces.
Proof.
  induction ces as [|[c e] ces IHces].
  - rewrite bound_var_Ecase_nil; now cbn.
  - rewrite bound_var_Ecase_cons; cbn; rewrite IHces; eauto with Ensembles_DB.
Qed.

Fixpoint used_vars_ces (ces : list (cps.ctor_tag * cps.exp)) :=
  match ces with
  | [] => Empty_set _
  | (c, e) :: ces => used_vars e :|: used_vars_ces ces
  end.

Lemma used_vars_Ecase x ces : used_vars (cps.Ecase x ces) <--> x |: used_vars_ces ces.
Proof.
  induction ces as [|[c e] ces IHces].
  - rewrite used_vars_Ecase_nil; cbn; now normalize_sets.
  - rewrite used_vars_Ecase_cons; cbn; rewrite IHces; eauto with Ensembles_DB.
Qed.

(* Renaming *)

Definition r_map : Set := M.tree cps.var.

Definition fun_name : fundef -> var := fun '(Ffun f _ _ _) => f.

Definition apply_r' (σ : r_map) (x : var) : var := [apply_r σ ![x]]!.
Definition apply_r_list' σ (xs : list var) := map (apply_r' σ) xs.

(* Assume UB(e) and dom(σ) ∩ BV(e) = ran(σ) ∩ BV(e) = ∅ *)
Fixpoint rename_all' (σ:r_map) (e:exp) : exp :=
  match e with
  | Econstr x t ys e' => Econstr x t (apply_r_list' σ ys) (rename_all' σ e')
  | Eprim x f ys e' => Eprim x f (apply_r_list' σ ys) (rename_all' σ e')
  | Eletapp x f ft ys e' => Eletapp x (apply_r' σ f) ft (apply_r_list' σ ys)
                                    (rename_all' σ e')
  | Eproj v t n y e' => Eproj v t n (apply_r' σ y) (rename_all' σ e')
  | Ecase v cl =>
    Ecase (apply_r' σ v) (List.map (fun (p:ctor_tag*exp) => let (k, e) := p in
                                                          (k, rename_all' σ e)) cl)
  | Efun fl e' =>
    let fs := map fun_name fl in
    let rename_all_fun' σ fd :=
      let 'Ffun v' t ys e := fd in
      Ffun v' t ys (rename_all' σ e)
    in
    let fl' := map (rename_all_fun' σ) fl in
    Efun fl' (rename_all' σ e')
  | Eapp f t ys =>
    Eapp (apply_r' σ f) t (apply_r_list' σ ys)
  | Ehalt v => Ehalt (apply_r' σ v)
  end.

Fixpoint rename_all_bv σ e : bound_var ![e] <--> bound_var ![rename_all' σ e].
Proof.
  destruct e; unbox_newtypes; cbn; repeat normalize_bound_var; eauto with Ensembles_DB.
  Guarded.
  - induction ces as [|[[c] e] ces IHces]; cbn; repeat normalize_bound_var; eauto with Ensembles_DB.
    Guarded.
  - induction fds as [|[[f] [ft] xs e_body] fds IHfds]; cbn; [eauto with Ensembles_DB|].
    Guarded.
    change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *; repeat normalize_bound_var.
    rewrite <- (rename_all_bv σ e_body). Guarded.
    repeat rewrite <- Union_assoc.
    rewrite IHfds; clear rename_all_bv; eauto with Ensembles_DB.
Qed.

Lemma rename_all_bv_fds σ fds :
  bound_var_fundefs ![fds] <-->
  bound_var_fundefs ![map (fun '(Ffun f ft xs e) => Ffun f ft xs (rename_all' σ e)) fds].
Proof.
  assert (Hbundle : forall fds x, bound_var_fundefs ![fds] <--> bound_var ![Efun fds (Ehalt x)]). {
    intros fds' [x]; cbn; repeat normalize_bound_var; eauto with Ensembles_DB. }
  rewrite (Hbundle _ (mk_var 1)), (Hbundle _ (apply_r' σ (mk_var 1))).
  change (Efun (map ?f fds) (Ehalt (apply_r' σ (mk_var 1))))
    with (rename_all' σ (Efun fds (Ehalt (mk_var 1)))).
  apply rename_all_bv.
Qed.

Fixpoint rename_all_uniq σ e : unique_bindings ![e] -> unique_bindings ![rename_all' σ e].
Proof.
  destruct e; unbox_newtypes; cbn; try solve [
    intros Huniq; inv Huniq; constructor; auto;
    change (~ bound_var ?e ?x) with (~ x \in bound_var e); now rewrite <- rename_all_bv].
  - change (ces_of_proto' exp_of_proto) with ces_of_proto in *.
    induction ces as [|[c e] ces IHces]; [constructor|unbox_newtypes; cbn].
    intros Huniq; inv Huniq; constructor; auto. Guarded.
    match goal with
    | |- Disjoint _ _ (bound_var (cps.Ecase ?e (ces_of_proto (map ?g ?ces)))) =>
      change (bound_var (cps.Ecase ?e (ces_of_proto (map g ces))))
       with (bound_var ![rename_all' σ (Ecase (mk_var x) ces)])
    end.
    repeat rewrite <- rename_all_bv; cbn.
    now rewrite bound_var_Ecase in *.
    Guarded.
  - change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.
    intros Huniq; inv Huniq; constructor; auto. 2: {
      now rewrite <- rename_all_bv, <- rename_all_bv_fds. }
    induction fds as [|[f ft xs e_body] fds IHfds]; [constructor|unbox_newtypes; cbn in *].
    inv H2; constructor; 
    change (~ bound_var ?e ?x) with (~ x \in bound_var e) in *;
    change (~ bound_var_fundefs ?fds ?x) with (~ x \in bound_var_fundefs fds) in *;
    try solve [auto|try rewrite <- rename_all_bv; try rewrite <- rename_all_bv_fds; easy].
    apply IHfds; auto.
    eapply Disjoint_Included_r; eauto.
    repeat normalize_bound_var; eauto with Ensembles_DB.
Qed.

Definition image'' σ : Ensemble cps.var := fun y => exists x, M.get x σ = Some y.

Lemma apply_r_vars σ x : [set apply_r σ x] \subset x |: image'' σ.
Proof.
  unfold apply_r.
  destruct (cps.M.get x σ) as [y|] eqn:Hget; [|eauto with Ensembles_DB].
  intros arb Harb; inv Harb; right; unfold image'', Ensembles.In; now exists x.
Qed.
  
Lemma apply_r_list_vars σ xs :
  FromList ![apply_r_list' σ xs] \subset FromList ![xs] :|: image'' σ.
Proof.
  induction xs as [|x xs IHxs]; [eauto with Ensembles_DB|unbox_newtypes; cbn in *].
  repeat normalize_sets.
  apply Union_Included.
  - eapply Included_trans; [apply apply_r_vars|]; eauto with Ensembles_DB.
  - eapply Included_trans; [apply IHxs|]; eauto with Ensembles_DB.
Qed.

Fixpoint rename_all_used σ e {struct e} :
  used_vars ![rename_all' σ e] \subset used_vars ![e] :|: image'' σ.
Proof.
  destruct e; unbox_newtypes; cbn in *; repeat normalize_used_vars.
  Ltac solve_easy_rename_used IH :=
    lazymatch goal with
    | |- _ :|: _ \subset _ => apply Union_Included; solve_easy_rename_used IH
    | |- [set apply_r _ _] \subset _ =>
      clear IH; eapply Included_trans; [apply apply_r_vars|]; eauto with Ensembles_DB
    | |- FromList (strip_vars (apply_r_list' _ _)) \subset _ =>
      clear IH; eapply Included_trans; [apply apply_r_list_vars|]; eauto with Ensembles_DB
    | |- used_vars _ \subset _ => eapply Included_trans; [apply IH|]; eauto with Ensembles_DB
    | |- _ => solve [eauto with Ensembles_DB]
    end.
  all: try solve [solve_easy_rename_used rename_all_used]. Guarded.
  - rewrite used_vars_Ecase; apply Union_Included; [solve_easy_rename_used rename_all_used|].
    change (ces_of_proto' exp_of_proto) with ces_of_proto; induction ces as [|[[c] e] ces IHces]; cbn;
    [eauto with Ensembles_DB|].
    repeat normalize_used_vars.
    apply Union_Included; [solve_easy_rename_used rename_all_used|].
    eapply Included_trans; [apply IHces|]; eauto with Ensembles_DB.
  - change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto.
    apply Union_Included; [|solve_easy_rename_used rename_all_used].
    induction fds as [|[[f] [ft] xs e_body] fds IHfds]; cbn; [eauto with Ensembles_DB|].
    repeat normalize_used_vars.
    apply Union_Included; [solve_easy_rename_used rename_all_used|].
    eapply Included_trans; [apply IHfds|]; eauto with Ensembles_DB.
Qed.

Lemma empty_image : image'' (M.empty _) <--> Empty_set _.
Proof.
  unfold image'', Ensembles.In; split; intros x Hx; inv Hx.
  now rewrite M.gempty in H.
Qed.

Lemma set_lists_image'' xs ys σ σ' :
  set_lists xs ys σ = Some σ' ->
  image'' σ' \subset image'' σ :|: FromList ys.
Proof.
  revert ys σ σ'; induction xs as [|x xs IHxs]; destruct ys as [|y ys]; try solve [inversion 1].
  - inversion 1; eauto with Ensembles_DB.
  - intros σ σ' Hset; cbn in Hset.
    destruct (set_lists xs ys σ) as [σ''|] eqn:Hσ''; inv Hset.
    specialize (IHxs ys σ σ'' Hσ'').
    intros arb [x' Hx']; specialize (IHxs arb); unfold Ensembles.In, image'' in *.
    unfold apply_r in Hx'; change cps.M.get with M.get in *; change map_util.M.set with M.set in *.
    destruct (Pos.eq_dec x' x) as [Heq|Hne]; [subst x'; rewrite M.gss in Hx'|rewrite M.gso in Hx' by auto].
    + right; subst; now left.
    + destruct IHxs as [Hσ|Hin_ys]; [eexists; eassumption|left|right; right]; auto.
Qed.

Lemma fresher_than_Empty_set x : fresher_than x (Empty_set _).
Proof. intros y []. Qed.

(* Some passes maintain map of known functions *)

Definition fun_map : Set := M.tree (fun_tag * list var * exp).

Fixpoint add_fundefs (fds : fundefs) (ρ : fun_map) : fun_map :=
  match fds with
  | Ffun f ft xs e :: fds => M.set ![f] (ft, xs, e) (add_fundefs fds ρ)
  | [] => ρ
  end.

Fixpoint add_fundefs_Some f ft xs e ρ fds {struct fds} :
  M.get f (add_fundefs fds ρ) = Some (ft, xs, e) ->
  In (Ffun (mk_var f) ft xs e) fds \/ M.get f ρ = Some (ft, xs, e).
Proof.
  destruct fds as [|[[g] gt ys e'] fds]; [now right|cbn; intros Hget].
  destruct (Pos.eq_dec f g); [subst; rewrite M.gss in Hget; now inv Hget|].
  rewrite M.gso in Hget by auto.
  specialize (add_fundefs_Some _ _ _ _ ρ fds Hget).
  now destruct add_fundefs_Some as [Hin|Hin].
Qed.
