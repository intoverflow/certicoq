Require Import Coq.Strings.String.
Require Import Coq.Sets.Ensembles Coq.ZArith.ZArith.
Require Import L6.Ensembles_util L6.map_util L6.List_util.
Require Import L6.state L6.alpha_conv L6.identifiers L6.functions L6.shrink_cps.
Require Import L6.Prototype.
Require Import L6.cps_proto L6.proto_util.

Require Import Lia.

Require Import Coq.Lists.List.
Import ListNotations.

Unset Strict Unquote Universe Mode.

(** * Shrink rewrites *)

(* Known functions *)

(* The function definition f(xs) = e_body (with fun tag ft) is known at C⟦e⟧ if
   f was defined in an earlier bundle.
   (Contrast this with the definition for inlining, which also allows inlining of
    functions within the same bundle) *)
Definition known_function {A} (f : var) (ft : fun_tag) (xs : list var) (e_body : exp)
          (C : exp_c A exp_univ_exp) : Prop :=
  (exists D fds E, C = D >:: Efun1 fds >++ E /\ List.In (Ffun f ft xs e_body) fds).

(* Known constructor values *)

(* (x ↦ Con c ys) ∈ C *)
Definition known_ctor {A} x c ys (C : exp_c A exp_univ_exp) : Prop :=
  exists D E, C = D >:: Econstr3 x c ys >++ E.

(* Occurrence counts *)

Definition count_var (x_in x : var) : nat := if (![x_in] =? ![x])%positive then 1 else 0.
Definition total : list nat -> nat := fold_right plus 0.
Definition count_vars x_in (xs : list var) : nat := total (map (count_var x_in) xs).
Definition count_ces' (count_exp : var -> exp -> nat) x_in (ces : list (ctor_tag * _)) : nat :=
  total (map (fun '(_, e) => count_exp x_in e) ces).
Definition count_fds' (count_exp : var -> exp -> nat) x_in (fds : list fundef) : nat :=
  total (map (fun '(Ffun _ _ _ e) => count_exp x_in e) fds).
Fixpoint count_exp x_in e {struct e} : nat :=
  match e with
  | Econstr x c ys e => count_vars x_in ys + count_exp x_in e
  | Ecase x ces => count_var x_in x + count_ces' count_exp x_in ces
  | Eproj x c n y e => count_var x_in y + count_exp x_in e
  | Eletapp x f ft ys e => count_var x_in f + count_vars x_in ys + count_exp x_in e
  | Efun fds e => count_fds' count_exp x_in fds + count_exp x_in e
  | Eapp f ft xs => count_var x_in f + count_vars x_in xs
  | Eprim x p ys e => count_vars x_in ys + count_exp x_in e
  | Ehalt x => count_var x_in x
  end.
Definition count_ces := count_ces' count_exp.
Definition count_fds := count_fds' count_exp.

Inductive shrink_step : exp -> exp -> Prop :=
(* Case folding *)
| shrink_cfold : forall (C : frames_t exp_univ_exp _) x c ys e ces,
  known_ctor x c ys C /\ In (c, e) ces ->
  shrink_step (C ⟦ Ecase x ces ⟧) (C ⟦ Rec e ⟧)
(* Projection folding *)
| shrink_pfold : forall (C : frames_t exp_univ_exp _) x c ys y y' t n e,
  known_ctor x c ys C /\ nthN ys n = Some y' ->
  shrink_step (C ⟦ Eproj y t n x e ⟧) (C ⟦ Rec (rename_all' (M.set ![y] ![y'] (M.empty _)) e) ⟧)
(* Dead variable elimination *)
| shrink_dead_constr1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys e,
  ~ ![x] \in occurs_free ![e] ->
  shrink_step (C ⟦ Econstr x c ys e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_constr2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys e,
  ~ ![x] \in occurs_free ![e] ->
  BottomUp (shrink_step (C ⟦ Econstr x c ys e ⟧) (C ⟦ e ⟧))
| shrink_dead_proj1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x t n y e,
  ~ ![x] \in occurs_free ![e] ->
  shrink_step (C ⟦ Eproj x t n y e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_proj2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x t n y e,
  ~ ![x] \in occurs_free ![e] ->
  BottomUp (shrink_step (C ⟦ Eproj x t n y e ⟧) (C ⟦ e ⟧))
| shrink_dead_prim1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x p ys e,
  ~ ![x] \in occurs_free ![e] ->
  shrink_step (C ⟦ Eprim x p ys e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_prim2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x p ys e,
  ~ ![x] \in occurs_free ![e] ->
  BottomUp (shrink_step (C ⟦ Eprim x p ys e ⟧) (C ⟦ e ⟧))
| shrink_dead_fun1 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f ft xs e fds,
  count_exp f (C ⟦ Ffun f ft xs e :: fds ⟧) = 0 ->
  shrink_step (C ⟦ Ffun f ft xs e :: fds ⟧) (C ⟦ Rec fds ⟧)
| shrink_dead_fun2 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f ft xs e fds,
  count_exp f (C ⟦ Ffun f ft xs e :: fds ⟧) = 0 ->
  BottomUp (shrink_step (C ⟦ Ffun f ft xs e :: fds ⟧) (C ⟦ fds ⟧))
| shrink_dead_funs : forall (C : frames_t exp_univ_exp exp_univ_exp) e,
  BottomUp (shrink_step (C ⟦ Efun [] e ⟧) (C ⟦ e ⟧))
(* Inlining *)
| shrink_inline : forall (C : frames_t exp_univ_exp exp_univ_exp) f ft ft' xs ys e σ,
  known_function f ft' xs e C /\
  count_exp f (C ⟦ Eapp f ft ys ⟧) = 1 ->
  set_lists ![xs] ![ys] (M.empty _) = Some σ ->
  shrink_step (C ⟦ Eapp f ft ys ⟧) (C ⟦ Rec (rename_all' σ e) ⟧).

(** * Known functions *)

Definition R_fns {A} (C : exp_c A exp_univ_exp) : Set := {
  ρ : fun_map |
  forall f ft xs e_body, M.get ![f] ρ = Some (ft, xs, e_body) ->
  known_function f ft xs e_body C }.

Instance Preserves_R_fns : Preserves_R _ exp_univ_exp (@R_fns).
Proof.
  intros A B fs f [ρ Hρ]; destruct f; lazymatch goal with
  | |- R_fns (fs >:: Efun1 ?fds') => rename fds' into fds
  | _ =>
    exists ρ; intros f' ft' xs' e_body' Hget'; specialize (Hρ f' ft' xs' e_body' Hget');
    destruct Hρ as [D [fds [E [Hctx Hin]]]];
    match goal with |- known_function _ _ _ _ (_ >:: ?f) => exists D, fds, (E >:: f); now subst fs end
  end.
  exists (add_fundefs fds ρ); intros [f] ft xs e_body Hget; cbn in *.
  apply add_fundefs_Some in Hget; destruct Hget as [|Hnotin]; [now exists fs, fds, <[]>|].
  specialize (Hρ (mk_var f) ft xs e_body Hnotin); destruct Hρ as [D [fds' [E [Hctx Hin]]]].
  exists D, fds', (E >:: Efun1 fds); now subst fs.
Defined.

(** * Known constructors *)

Definition ctx_map := M.tree (ctor_tag * list var).
Definition R_ctors {A} (C : exp_c A exp_univ_exp) : Set := {
  ρ : ctx_map |
  forall x c ys, M.get ![x] ρ = Some (c, ys) -> known_ctor x c ys C }.

Instance Preserves_R_ctors : Preserves_R _ exp_univ_exp (@R_ctors).
Proof.
  intros A B fs f [ρ Hρ]; destruct f; lazymatch goal with
  | |- R_ctors (fs >:: Econstr3 ?x' ?c' ?ys') => rename x' into x, c' into c, ys' into ys
  | _ =>
    exists ρ; intros x' c' ys' Hget'; specialize (Hρ x' c' ys' Hget');
    destruct Hρ as [D [E Hctx]];
    match goal with |- known_ctor _ _ _ (_ >:: ?f) => exists D, (E >:: f); now subst fs end
  end.
  destruct x as [x]; exists (M.set x (c, ys) ρ); intros [x'] c' ys' Hget'; cbn in *.
  destruct (Pos.eq_dec x' x); [subst; rewrite M.gss in Hget'; inv Hget'; now exists fs, <[]>|].
  rewrite M.gso in Hget' by auto; destruct (Hρ (mk_var x') c' ys' Hget') as [D [E Hctx]].
  exists D, (E >:: Econstr3 (mk_var x) c ys); now subst fs.
Defined.

(** * Occurrence counts *)

Definition c_map : Set := M.tree positive.

Definition census_var (x : var) (δ : c_map) : c_map :=
  let x := ![x] in
  match M.get x δ with
  | Some n => M.set x (n + 1)%positive δ
  | None => M.set x 1%positive δ
  end.
Definition census_list {A} (census : A -> c_map -> c_map) (xs : list A) (δ : c_map) :=
  fold_right census δ xs.
Definition census_vars := census_list census_var.
Definition census_ces' (census_exp : exp -> c_map -> c_map) : list (ctor_tag * _) -> _ -> _ :=
  census_list (fun '(c, e) δ => census_exp e δ).
Definition census_fds' (census_exp : exp -> c_map -> c_map) :=
  census_list (fun '(Ffun f ft xs e) δ => census_exp e δ).
Fixpoint census_exp (e : exp) (δ : c_map) {struct e} : c_map :=
  match e with
  | Econstr x c ys e => census_vars ys (census_exp e δ)
  | Ecase x ces => census_var x (census_ces' census_exp ces δ)
  | Eproj x c n y e => census_var y (census_exp e δ)
  | Eletapp x f ft ys e => census_var f (census_vars ys (census_exp e δ))
  | Efun fds e => census_fds' census_exp fds (census_exp e δ)
  | Eapp f ft xs => census_var f (census_vars xs δ)
  | Eprim x p ys e => census_vars ys (census_exp e δ)
  | Ehalt x => census_var x δ
  end.
Definition census_ces := census_ces' census_exp.
Definition census_fds := census_fds' census_exp.

(* [census] computes occurrence counts *)

Definition census_count (x : var) δ :=
  match M.get ![x] δ with
  | Some n => Pos.to_nat n
  | None => 0
  end.

Lemma census_var_corresp x_in x n δ δ' :
  δ' = census_var x_in δ ->
  census_count x δ = n ->
  census_count x δ' = n + count_var x x_in.
Proof.
  intros Hmk Hold; unbox_newtypes; unfold census_count, census_var, count_var in *; cbn in *.
  destruct (Pos.eqb_spec x x_in).
  - subst. destruct (M.get x_in δ); rewrite M.gss; zify; lia.
  - destruct (M.get x_in δ); subst; rewrite M.gso by auto; destruct (M.get x δ); zify; lia.
Qed.

Fixpoint census_vars_corresp xs x n δ δ' :
  δ' = census_vars xs δ ->
  census_count x δ = n ->
  census_count x δ' = n + count_vars x xs.
Proof.
  destruct xs as [|x' xs].
  - inversion 1; subst; cbn; zify; lia.
  - cbn.
    change (fold_right census_var δ xs) with (census_vars xs δ).
    change (total (map (count_var x) xs)) with (count_vars x xs).
    remember (census_vars xs δ) as δ'' eqn:Hδ''.
    intros Hδ' Hx.
    specialize (census_vars_corresp xs x n δ δ'' Hδ'' Hx).
    eapply census_var_corresp in Hδ'; eauto; lia.
Qed.

Ltac collapse_primes :=
  change (count_ces' count_exp) with count_ces in *;
  change (count_fds' count_exp) with count_fds in *;
  change (census_ces' census_exp) with census_ces in *;
  change (census_fds' census_exp) with census_fds in *;
  (* TODO: move to proto_util? *)
  change (ces_of_proto' exp_of_proto) with ces_of_proto in *;
  change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.

Fixpoint census_exp_corresp' x n e δ δ' {struct e} :
  δ' = census_exp e δ ->
  census_count x δ = n ->
  census_count x δ' = n + count_exp x e.
Proof.
  destruct e; cbn; collapse_primes; try solve [
    remember (census_exp e δ) as δ0 eqn:Hδ0;
    intros Hδ' Hn; specialize (census_exp_corresp' x n e δ δ0 Hδ0 Hn);
    (eapply census_vars_corresp in Hδ' + eapply census_var_corresp in Hδ');
    eauto; lia]. Guarded.
  - remember (census_ces ces δ) as δ0 eqn:Hδ0; intros Hδ' Hn.
    enough (Hces : forall x n δ δ',
             δ' = census_ces ces δ ->
             census_count x δ = n ->
             census_count x δ' = n + count_ces x ces).
    { specialize (Hces x n δ δ0 Hδ0 Hn); eapply census_var_corresp in Hδ'; eauto; lia. }
    clear - census_exp_corresp'.
    induction ces as [|[c e] ces IHces]; [intros; cbn in *; subst; lia|cbn].
    intros x n δ δ' Hδ' Hn.
    change (fold_right _ _ _) with (census_ces ces δ) in *|-.
    change (total _) with (count_ces x ces).
    remember (census_ces ces δ) as δ0 eqn:Hδ0.
    eapply IHces in Hδ0; eauto.
    eapply census_exp_corresp' in Hδ'; eauto; lia. Guarded.
  - remember (census_exp e δ) as δ0 eqn:Hδ0.
    intros Hδ' Hn; specialize (census_exp_corresp' x n e δ δ0 Hδ0 Hn).
    remember (census_vars ys δ0) as δ1 eqn:Hδ1.
    eapply census_vars_corresp in Hδ1; eauto.
    eapply census_var_corresp in Hδ'; eauto; lia.
  - remember (census_exp e δ) as δ0 eqn:Hδ0; intros Hδ' Hn.
    enough (Hfds : forall x n δ δ',
             δ' = census_fds fds δ ->
             census_count x δ = n ->
             census_count x δ' = n + count_fds x fds).
    { eapply census_exp_corresp' in Hδ0; eauto; specialize (Hfds x _ δ0 δ' Hδ' Hδ0); lia. }
    clear - census_exp_corresp'.
    induction fds as [|[f ft xs e] fds IHfds]; [intros; cbn in *; subst; lia|cbn].
    intros x n δ δ' Hδ' Hn.
    change (fold_right _ _ _) with (census_fds fds δ) in *|-.
    change (total _) with (count_fds x fds).
    remember (census_fds fds δ) as δ0 eqn:Hδ0.
    eapply IHfds in Hδ0; eauto.
    eapply census_exp_corresp' in Hδ'; eauto; lia. Guarded.
  - remember (census_vars xs δ) as δ0 eqn:Hδ0; intros Hδ' Hn.
    eapply census_vars_corresp in Hδ0; eauto.
    eapply census_var_corresp in Hδ'; eauto; lia.
  - intros Hδ' Hn; eapply census_var_corresp in Hδ'; eauto; lia.
Qed.

Corollary census_exp_corresp e δ :
  δ = census_exp e (M.empty _) ->
  forall x, census_count x δ = count_exp x e.
Proof.
  intros Hδ x; change (count_exp x e) with (0 + count_exp x e).
  eapply census_exp_corresp'; eauto; unfold census_count; unbox_newtypes; cbn; now rewrite M.gempty.
Qed.

(* Count = 0 --> dead variable *)

Lemma plus_zero_and n m : n + m = 0 -> n = 0 /\ m = 0. Proof. lia. Qed.

Lemma not_In_Setminus' {A} (S1 S2 : Ensemble A) x : ~ x \in S1 -> ~ x \in (S1 \\ S2).
Proof. rewrite not_In_Setminus; tauto. Qed.

Lemma count_dead_var x y : count_var x y = 0 -> ~ ![x] \in [set ![y]].
Proof.
  unbox_newtypes; unfold count_var; cbn; destruct (Pos.eqb_spec x y); inversion 1; now inversion 1.
Qed.

Fixpoint count_dead_vars x xs :
  count_vars x xs = 0 -> ~ ![x] \in FromList ![xs].
Proof.
  destruct xs as [|x' xs]; [intros; inversion 1|unbox_newtypes; cbn in *].
  change (total _) with (count_vars (mk_var x) xs).
  intros H; apply plus_zero_and in H; destruct H as [Hx Hxs].
  intros [Heq|Hin]; [subst; unfold count_var in Hx; now rewrite Pos.eqb_refl in Hx|].
  now apply (count_dead_vars (mk_var x) xs Hxs).
Qed.

Fixpoint count_dead_exp x e :
  count_exp x e = 0 -> ~ ![x] \in occurs_free ![e].
Proof.
  destruct e; unbox_newtypes; cbn in *; collapse_primes; repeat normalize_occurs_free; intros H;
    repeat match goal with
    | H : _ + _ = 0 |- _ => apply plus_zero_and in H; destruct H
    | H : count_var _ _ = 0 |- _ => apply count_dead_var in H; cbn in *
    | H : count_vars _ _ = 0 |- _ => apply count_dead_vars in H; cbn in *
    | H : count_exp ?x ?e = 0 |- _ => apply (count_dead_exp x e) in H; cbn in *
    | |- ~ _ \in (_ :|: _) => rewrite Union_demorgan; split
    | |- ~ x \in (_ \\ _) => apply not_In_Setminus'
    end; auto.
  - induction ces as [|[[c] e] ces IHces]; cbn; [inversion 1; subst; now contradiction H|].
    change (total _) with (count_ces (mk_var x) ces); normalize_occurs_free; rewrite !Union_demorgan.
    rename H0 into Hcount; cbn in Hcount; change (total _) with (count_ces (mk_var x) ces) in Hcount.
    apply plus_zero_and in Hcount; destruct Hcount as [He Hces]; split; [|split]; auto.
    now apply count_dead_exp in He. Guarded.
  - induction fds as [|[[f] [ft] xs e_body] fds IHfds]; cbn; [inversion 1; subst; now contradiction H|].
    change (total _) with (count_fds (mk_var x) fds); normalize_occurs_free; rewrite !Union_demorgan.
    rename H into Hcount; cbn in Hcount; change (total _) with (count_fds (mk_var x) fds) in Hcount.
    apply plus_zero_and in Hcount; destruct Hcount as [He Hfds]; split; apply not_In_Setminus'; auto.
    now apply count_dead_exp in He. Guarded.
Qed.

(** * Shrink inlined functions *)

Definition b_map := M.tree bool.

Check getd.
Definition drop_fns_ces' (drop_fns : b_map -> exp -> exp) θ (ces : list (ctor_tag * exp)) :=
  map (fun '(c, e) => (c, drop_fns θ e)) ces.
Definition drop_fns_fds' (drop_fns : b_map -> exp -> exp) θ fds :=
  fold_right
    (fun '(Ffun f ft xs e) fds =>
      if getd false ![f] θ
      then Ffun f ft xs (drop_fns θ e) :: fds
      else fds)
    [] fds.
Fixpoint drop_fns θ e {struct e} :=
  match e with
  | Econstr x c ys e => Econstr x c ys (drop_fns θ e)
  | Ecase x ces => Ecase x (drop_fns_ces' drop_fns θ ces)
  | Eproj x c n y e => Eproj x c n y (drop_fns θ e)
  | Eletapp x f ft ys e => Eletapp x f ft ys (drop_fns θ e)
  | Efun fds e => Efun (drop_fns_fds' drop_fns θ fds) (drop_fns θ e)
  | Eapp f ft xs => Eapp f ft xs
  | Eprim x p ys e => Eprim x p ys (drop_fns θ e)
  | Ehalt x => Ehalt x
  end.
Definition drop_fns_ces := drop_fns_ces' drop_fns.
Definition drop_fns_fds := drop_fns_fds' drop_fns.

Ltac collapse_primes' :=
  change (count_ces' count_exp) with count_ces in *;
  change (count_fds' count_exp) with count_fds in *;
  change (census_ces' census_exp) with census_ces in *;
  change (census_fds' census_exp) with census_fds in *;
  change (drop_fns_ces' drop_fns) with drop_fns_ces in *;
  change (drop_fns_fds' drop_fns) with drop_fns_fds in *;
  (* TODO: move to proto_util? *)
  change (ces_of_proto' exp_of_proto) with ces_of_proto in *;
  change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.

(** * State variable *)

Definition S_shrink {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := {
  '(δ, θ) : c_map * b_map | 
  (* The program being transformed, after all dead functions in θ have been eliminated *)
  let P := drop_fns θ (C ⟦ e ⟧) in
  (* The program has unique bindings only after dead functions have been dropped *)
  unique_bindings ![P] /\
  (* Though function bodies are copied for inlining, bound vars and free vars still disjoint
     even before dropping dead fns *)
  Disjoint _ (bound_var ![C ⟦ e ⟧]) (occurs_free ![C ⟦ e ⟧]) /\
  (* δ holds valid occurrence counts *)
  (forall x, census_count x δ = count_exp x P) /\
  (* θ only holds dead functions *)
  (forall f, if getd false ![f] θ then count_exp f (C ⟦ e ⟧) = 0 else True) }.

Instance Preserves_S_shrink : Preserves_S _ exp_univ_exp (@S_shrink).
Proof. constructor; intros A B fs f x δ; exact δ. Defined.

Definition R_shrink : forall {A}, exp_c A exp_univ_exp -> Set := R_prod (@R_fns) (@R_ctors).

(** * Delayed renaming *)

(* TODO: move to proto_util *)
Definition domain' (σ : r_map) := domain (fun x => M.get x σ).

(* TODO: move to proto_util *)
Lemma empty_domain' : domain' (M.empty _) <--> Empty_set _.
Proof.
  split; unfold domain', domain; [|inversion 1].
  intros x [y Hxy]; now rewrite M.gempty in Hxy.
Qed.

Definition bound {A} : univD A -> Ensemble cps.var :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(_, e) => bound_var ![e]
  | exp_univ_list_prod_ctor_tag_exp => fun ces => bound_var_ces ![ces]
  | exp_univ_fundef => fun '(Ffun (mk_var x) _ xs e) => x |: FromList ![xs] :|: bound_var ![e]
  | exp_univ_list_fundef => fun fds => bound_var_fundefs ![fds]
  | exp_univ_exp => fun e => bound_var ![e]
  | exp_univ_var => fun _ => Empty_set _
  | exp_univ_fun_tag => fun _ => Empty_set _
  | exp_univ_ctor_tag => fun _ => Empty_set _
  | exp_univ_prim => fun _ => Empty_set _
  | exp_univ_N => fun _ => Empty_set _
  | exp_univ_list_var => fun _ => Empty_set _
  end.

Definition D_rename {A} (e : univD A) : Set := {
  σ : r_map | 
  Disjoint _ (domain' σ) (bound e) /\ 
  Disjoint _ (image'' σ) (bound e) }.

Definition rename {A} (σ : r_map) : univD A -> univD A :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(c, e) => (c, rename_all' σ e)
  | exp_univ_list_prod_ctor_tag_exp => fun ces => map (fun '(c, e) => (c, rename_all' σ e)) ces
  | exp_univ_fundef => fun '(Ffun f ft xs e) => Ffun f ft xs (rename_all' σ e)
  | exp_univ_list_fundef => fun fds => map (fun '(Ffun f ft xs e) => Ffun f ft xs (rename_all' σ e)) fds
  | exp_univ_exp => fun e => rename_all' σ e
  | exp_univ_var => fun x => apply_r' σ x
  | exp_univ_fun_tag => fun ft => ft
  | exp_univ_ctor_tag => fun c => c
  | exp_univ_prim => fun p => p
  | exp_univ_N => fun n => n
  | exp_univ_list_var => fun xs => apply_r_list' σ xs
  end.

(* TODO: move to proto_util *)
Lemma apply_r'_id x : apply_r' (M.empty _) x = x.
Proof. unbox_newtypes; unfold apply_r', apply_r; cbn; now rewrite M.gempty. Qed.

Fixpoint apply_r_list'_id xs {struct xs} : apply_r_list' (M.empty _) xs = xs.
Proof.
  destruct xs as [|x xs]; [reflexivity|cbn].
  change (map _ xs) with (apply_r_list' (M.empty _) xs).
  rewrite apply_r_empty, apply_r_list'_id; now unbox_newtypes.
Qed.

(* TODO: move to proto_util *)
Fixpoint rename_all_id e {struct e} : rename_all' (M.empty _) e = e.
Proof.
  destruct e; unbox_newtypes; cbn; try now rewrite ?apply_r_list'_id, ?apply_r'_id, ?rename_all_id, ?apply_r_empty.
  Guarded.
  - rewrite apply_r_empty; f_equal; induction ces as [|[c e] ces IHces]; [reflexivity|cbn].
    now rewrite IHces, rename_all_id.
  - rewrite rename_all_id; f_equal; induction fds as [|[f ft xs e_body] fds IHfds]; [reflexivity|cbn].
    now rewrite IHfds, rename_all_id.
Qed.

Instance Delayed_D_rename : Delayed (@D_rename).
Proof.
  unshelve econstructor.
  - intros A e [σ Hσ]; exact (rename σ e).
  - intros A e; exists (M.empty _); rewrite empty_domain', empty_image; eauto with Ensembles_DB.
  - cbn; intros; destruct A; cbn in *; unbox_newtypes;
      repeat match goal with |- context [let '_ := ?e in _] => destruct e end;
      rewrite ?apply_r_empty, ?apply_r'_id, ?apply_r_list'_id, ?rename_all_id; auto;
      apply MCList.map_id_f; intros []; cbn; now rewrite rename_all_id.
Defined.

(** * Functional definition *)

Fixpoint find_case (c : ctor_tag) (ces : list (ctor_tag * exp)) : option exp :=
  match ces with
  | [] => None
  | (c', e) :: ces => if ![c] =? ![c'] then Some e else find_case c ces
  end%positive.

Fixpoint find_case_In c e ces : find_case c ces = Some e -> In (c, e) ces.
Proof.
  destruct ces as [|[c' e'] ces IHces]; [inversion 1|unbox_newtypes; cbn].
  destruct (Pos.eqb_spec c c'); intros Heq; inv Heq; [now left|right; auto].
Qed.

Definition rw_inline' : rewriter exp_univ_exp shrink_step (@D_rename) (@R_shrink) (@S_shrink).
Proof.
  mk_rw; try lazymatch goal with |- ExtraVars _ -> _ => clear | |- ConstrDelay _ -> _ => clear end.
  - (* Case folding *) intros _ R C x ces d r s success failure.
    destruct r as [ρ1 [ρ2 Hρ]] eqn:Hr.
    destruct d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    pose (x0 := apply_r' σ x); specialize success with (x0 := x0).
    destruct (M.get ![x0] ρ2) as [[c ys]|] eqn:Hctor; [|cond_failure].
    pose (Hρ' := Hρ x0 c ys Hctor); specialize success with (c := c) (ys := ys).
    destruct (find_case c ces) as [e|] eqn:Hfind; [|cond_failure]; apply find_case_In in Hfind.
    specialize success with (e := e) (e0 := @rename exp_univ_exp σ e).
    specialize success with (ces0 := @rename exp_univ_list_prod_ctor_tag_exp σ ces).
    cond_success success; unshelve eapply success.
    + exists σ; clear - Hfind Hσ; destruct x as [x]; cbn in *; destruct Hσ as [Hdom Hran].
      rewrite bound_var_Ecase in *; collapse_primes'.
      (* TODO: hoist *)
      assert (In_ces_bound : forall c e ces, In (c, e) ces -> bound_var ![e] \subset bound_var_ces ![ces]). {
        clear; induction ces as [|[[c'] e'] ces IHces]; [inversion 1|].
        destruct 1 as [Heq|Hne]; [inv Heq|]; cbn; eauto with Ensembles_DB. }
      split; (eapply Disjoint_Included_r; [eapply In_ces_bound; eauto|]; eauto).
    + split; auto; apply in_map with (f := @rename exp_univ_prod_ctor_tag_exp σ) in Hfind; now cbn in Hfind.
    + reflexivity. + reflexivity. + exact r.
    + destruct s as [[δ θ] Hs] eqn:Hs_eq; unshelve eexists; [refine (_, θ)|].
      * (* properly update counts *) admit.
      * split; [|split; [|split]].
        -- (* UB(θ(C[σ(Ecase x ces)])) ==> UB(θ(C[σ(e)])) because (c, e) ∈ ces *)
           admit.
        -- (* BV(C[σ(e)]) ⊆ BV(C[σ(Ecase x ces)]) and ditto for FV
              And already have BV(C[σ(Ecase x es)]) # FV(C[σ(Ecase x ces)]) *)
           admit.
        -- admit.
        -- destruct Hs as [Huniq [Hdis [Hδ Hθ]]].
           (* |C[σ(e)]|f = |C|f + |σ(e)|f
                ≤ |C|f + |σ(Ecase x ces)|f (because e ∈ ces)
                = |C[σ(Ecase x ces)]|f
                = 0 (by Hθ) *)
           admit.
  - (* Projection folding *) intros _ R C y t n x e d r s success failure.
    destruct r as [ρ1 [ρ2 Hρ]] eqn:Hr.
    destruct d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    pose (x0 := apply_r' σ x); specialize success with (x0 := x0).
    destruct (M.get ![x0] ρ2) as [[c ys]|] eqn:Hctor; [|cond_failure].
    pose (Hρ' := Hρ x0 c ys Hctor); specialize success with (c := c) (ys := ys).
    destruct (nthN ys n) as [y'|] eqn:Hy'; [|cond_failure].
    specialize success with (y0 := y) (t0 := t) (n0 := n) (y' := y').
    specialize success with (e0 := @rename exp_univ_exp σ e).
    cond_success success; unshelve eapply success.
    + exists σ; clear - Hσ; unbox_newtypes; cbn in *; destruct Hσ as [Hdom Hran].
      repeat normalize_bound_var_in_ctx.
      split; (eapply Disjoint_Included_r; [|eassumption]; eauto with Ensembles_DB).
    + split; auto; apply in_map with (f := @rename exp_univ_prod_ctor_tag_exp σ) in Hfind; now cbn in Hfind.
    + reflexivity. + reflexivity. + exact r.
    + destruct s as [[δ θ] Hs] eqn:Hs_eq; unshelve eexists; [refine (_, θ)|].
      * (* properly update counts *) admit.
      * split; [|split; [|split]].
        -- (* TODO: there should be a more direct proof using
                Θ(C[σ(Eproj y t n x e)])
                  = θ(C)[θ(σ(Eproj y t n x e))] 
                  = θ(C)[Eproj y t n (σ(x)) (θ(σ(e)))]
                because Hs gives UB(θ(C[σ(Eproj y t n x e)])) *)
           (* UB(θ(C[σ(e)[y'/y]])) ⟸ UB(θ(C)) ∧ UB(θ(σ(e)[y'/y])) ∧ BV(θ(C)) # BV(θ(σ(e)[y'/y]))
                UB(θ(C)) by assumption
                UB(θ(σ(e)[y'/y])) ⟸ UB(θ(σ(e))) because {y', y} # BV(θ(σ(e)))
                  y ∉ BV(θ(σ(e))) ⟸ y ∈ BV(σ(Eproj y t n x e)) ∧ UB(σ(EProj y t n x e))
                  y' ∉ BV(θ(σ(e))) ⟸
                    If y' ∈ BVstem(C) then y' ∈ BVstem(θ(C))
                      (Can only drop dead variables, but y' ∈ ys and (x ↦ (c, ys)) ∈ C so y' can't be dead)
                      ⟹ y' ∉ BV(θ(σ(e))) because UB
                    If y' ∉ BVstem(C) then y' ∈ ys ∧ (x ↦ (c, ys)) ∈ C ⟹ y' ∈ FV(θ(C))
                      ⟹ y' ∉ BV(θ(σ(e))) because FV(θ(C[σ(e)])) # BV(θ(C[σ(e)]))
                BV(θ(C)) # BV(θ(σ(e)[y'/y]))
                  ⟺ BV(θ(C)) # BV(θ(σ(e))) because {y, y'} # BV(θ(σ(e)))
                  ⟸ BV(θ(C)) # BV(θ(σ(Eproj y t n x e)))
                  ⟸ UB(θ(C[σ(Eproj y t n x e)])) *)
           admit.
        -- admit. (* TODO *)
        -- admit. (* TODO *)
        -- destruct Hs as [Huniq [Hdis [Hδ Hθ]]].
           (* f ≠ y' because y' is used somewhere in C and so can't be dead
              f ≠ y because θ contains only function bindings and y isn't a function binding
                TODO: need to add this or some other property to θ
              Then
                |C[σ(e)[y'/y]]|f = |C|f + |σ(e)[y'/y]|f
                  = |C|f + |σ(e)|f (because f ∉ {y, y'})
                  ≤ |C|f + |σ(Eproj y t n x e)|f
                  = |C[σ(Eproj y t n x e)]|f
                  = 0 (by Hθ) *)
           admit.
  - (* Top down dead constr *) intros _ R C x c ys e d r s success failure.
    destruct s as [[δ θ] [Huniq [Hdis [Hδ Hθ]]]] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    destruct (M.get ![x] δ) eqn:Hcount; [cond_failure|].
    specialize success with (x0 := x) (c0 := c) (ys0 := apply_r_list' σ ys).
    specialize success with (e0 := @rename exp_univ_exp σ e); cond_success success; unshelve eapply success.
    + exists σ. admit. (* easy *)
    + (* δ(x) = |θ(C[σ(Econstr x c ys e)])|x = 0
         TODO: Hδ isn't strong enough: what if x occurs free in one of the dropped functions?
           This seems tricky to fix. *)
      admit.
    + reflexivity. + reflexivity. + exact r.
    + unshelve eexists; [refine (_, θ)|].
      * (* update counts properly *)
        admit.
      * split; [|split; [|split]].
        -- (* Follows from Huniq because θ(C[σ(Econstr x c ys e)]) = θ(C)[Econstr x c (σ(ys)) (θ(σ(e)))] *)
           admit.
    pose (x0 := apply_r' σ x); specialize success with (x0 := x0).
    admit.
  - (* Bottom up dead constr *) intros _ R C x c ys e r s success failure.
    admit.
  - (* Top down dead proj *) intros _ R C x t n y e d r s success failure.
    admit.
  - (* Bottom up dead proj *) intros _ R C x t n y e r s success failure.
    admit.
  - (* Top down dead prim *) intros _ R C x p ys e d r s success failure.
    admit.
  - (* Bottom up dead prim *) intros _ R C x p ys e r s success failure.
    admit.
  - (* Top down dead fun *) intros _ R C f ft xs e fds d r s success failure.
    admit.
  - (* Bottom up dead fun *) intros _ R C f ft xs e fds r s success failure.
    admit.
  - (* Top down dead bundle *) intros _ R C e r s success failure.
    admit.
  - (* Shrink inlining (CPS) *) intros _ R C f ft ys d r s success failure.
    admit.
  - (* Rename a pair *) intros _ R c e d k.
    admit.
  - (* Rename empty list *) intros _ R d k.
    admit.
  - (* Rename cons case arms *) intros _ R [c e] ces d k.
    admit.
  - (* Rename function definition *) intros _ R f ft xs e d k.
    admit.
  - (* Rename empty list *) intros _ R d k.
    admit.
  - (* Rename cons function definitions *) intros _ R fd fds d k.
    admit.
  - (* Rename constr binding *) intros _ R x c ys e d k.
    admit.
  - (* Rename case expression *) intros _ R x ces d k.
    admit.
  - (* Rename proj binding *) intros _ R x t n y e d k.
    admit.
  - (* Rename letapp *) intros _ R x f ft ys e d k.
    admit.
  - (* Rename bundle definition *) intros _ R fds e d k.
    admit.
  - (* Rename cps app *) intros _ R f ft ys d k.
    admit.
  - (* Rename prim binding *) intros _ R x p ys e d k.
    admit.
  - (* Rename halt *) intros _ R x d k.
    admit.
  - (* Fuse renaming for proj folding *) destruct d0 as [σ Hσ] eqn:Hσ_eq; rewrite <- Hσ_eq in *.
    unshelve eexists; [exists (M.set ![y] ![y'] σ)|unbox_newtypes; cbn; subst d0].
    + admit.
    + admit.
  - (* Fuse renaming for inlining *) destruct d0 as [σ' Hσ'] eqn:Hσ'_eq; rewrite <- Hσ'_eq in *.
    destruct (set_lists ![xs] ![ys] σ') as [σ''|] eqn:Hσ''.
    2: { exfalso. apply set_lists_length_eq in H25.
         apply set_lists_length3 with (rho := σ') in H25.
         destruct H25 as [σ'' Hσ''']; congruence. }
    unshelve eexists; [exists σ''|unbox_newtypes; cbn; subst d0].
    + admit.
    + admit.
Admitted.
