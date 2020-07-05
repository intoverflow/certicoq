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
  count_exp x e = 0 ->
  shrink_step (C ⟦ Econstr x c ys e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_constr2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys e,
  count_exp x e = 0 ->
  BottomUp (shrink_step (C ⟦ Econstr x c ys e ⟧) (C ⟦ e ⟧))
| shrink_dead_proj1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x t n y e,
  count_exp x e = 0 ->
  shrink_step (C ⟦ Eproj x t n y e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_proj2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x t n y e,
  count_exp x e = 0 ->
  BottomUp (shrink_step (C ⟦ Eproj x t n y e ⟧) (C ⟦ e ⟧))
| shrink_dead_prim1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x p ys e,
  count_exp x e = 0 ->
  shrink_step (C ⟦ Eprim x p ys e ⟧) (C ⟦ Rec e ⟧)
| shrink_dead_prim2 : forall (C : frames_t exp_univ_exp exp_univ_exp) x p ys e,
  count_exp x e = 0 ->
  BottomUp (shrink_step (C ⟦ Eprim x p ys e ⟧) (C ⟦ e ⟧))
| shrink_dead_fun1 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f ft xs e fds,
  count_exp f (C ⟦ Ffun f ft xs e :: fds ⟧) = 0 ->
  shrink_step (C ⟦ Ffun f ft xs e :: fds ⟧) (C ⟦ Rec fds ⟧)
| shrink_dead_fun2 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f ft xs e fds,
  count_exp f (C ⟦ Ffun f ft xs e :: fds ⟧) = 0 ->
  BottomUp (shrink_step (C ⟦ Ffun f ft xs e :: fds ⟧) (C ⟦ fds ⟧))
| shrink_dead_funs : forall (C : frames_t exp_univ_exp exp_univ_exp) e,
  BottomUp (shrink_step (C ⟦ Efun [] e ⟧) (C ⟦ e ⟧)).

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

Ltac collapse_primes' :=
  change (count_ces' count_exp) with count_ces in *;
  change (count_fds' count_exp) with count_fds in *;
  change (census_ces' census_exp) with census_ces in *;
  change (census_fds' census_exp) with census_fds in *;
  (* TODO: move to proto_util? *)
  change (ces_of_proto' exp_of_proto) with ces_of_proto in *;
  change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.

(** * State variable *)

Definition S_shrink {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := {
  δ : c_map |
  (* The program being transformed *)
  let P := C ⟦ e ⟧ in
  (* The program has well-behaved bindings *)
  unique_bindings ![P] /\ Disjoint _ (bound_var ![P]) (occurs_free ![P]) /\
  (* δ holds valid occurrence counts *)
  (forall x, census_count x δ = count_exp x P) }.

Instance Preserves_S_shrink : Preserves_S _ exp_univ_exp (@S_shrink).
Proof. constructor; intros A B fs f x δ; exact δ. Defined.

Definition R_shrink : forall {A}, exp_c A exp_univ_exp -> Set := @R_ctors.

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

Definition rw_shrink' : rewriter exp_univ_exp shrink_step (@D_rename) (@R_shrink) (@S_shrink).
Proof.
  mk_rw; try lazymatch goal with |- ExtraVars _ -> _ => clear | |- ConstrDelay _ -> _ => clear end.
  - (* Case folding *) intros _ R C x ces d r s success failure.
    destruct r as [ρ Hρ] eqn:Hr, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    pose (x0 := apply_r' σ x); specialize success with (x0 := x0).
    destruct (M.get ![x0] ρ) as [[c ys]|] eqn:Hctor; [|cond_failure].
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
    + destruct s as [δ Hs] eqn:Hs_eq; unshelve eexists.
      * (* Update counts *) admit.
      * split; [|split].
        -- (* UB(C[σ(Ecase x ces)]) ==> UB(C[σ(e)]) because (c, e) ∈ ces *)
           admit.
        -- (* BV(C[σ(e)]) ⊆ BV(C[σ(Ecase x ces)]) and ditto for FV
              And already have BV(C[σ(Ecase x es)]) # FV(C[σ(Ecase x ces)]) *)
           admit.
        -- admit.
  - (* Projection folding *) intros _ R C y t n x e d r s success failure.
    destruct r as [ρ Hρ] eqn:Hr, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    pose (x0 := apply_r' σ x); specialize success with (x0 := x0).
    destruct (M.get ![x0] ρ) as [[c ys]|] eqn:Hctor; [|cond_failure].
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
    + destruct s as [δ Hs] eqn:Hs_eq; unshelve eexists; [|split; [|split]].
      * (* Update counts *) admit.
      * (* UB(C[(σe)[y'/y]])
              ⟸ UB(C[σe]) (y ∉ BV(e))
              ⟸ UB(C[Eproj y t n (σx) (σe)])
              ⟸ UB(C[σ(Eproj y t n x e)]) *)
        admit.
      * (* BV(C[(σe)[y'/y]])
             ⊆ BV(C[σe]) because y ∉ BV(σe)
             ⊆ BV(C[σ(Eproj y t n x e)])
           FV(C[(σe)[y'/y]])
             = FV(C) ∪ (FV((σe)[y'/y]) \ BVstem(C))
             = FV(C) ∪ (((FV(σe) \ {y}) ∪ {y'}) \ BVstem(C))
             = FV(C) ∪ (FV(σe) \ {y} \ BVstem(C)) ∪ ({y'} \ BVstem(C))
             ⊆ FV(C) ∪ (FV(σe) \ {y} \ BVstem(C)) ∪ FV(C) (by lemma)
             ⊆ FV(C) ∪ (({σx} ∪ (FV(σe) \ {y})) \ BVstem(C))
             = FV(C) ∪ (FV(Eproj y t n (σx) (σe)) \ BVstem(C))
             = FV(C) ∪ (FV(σ(Eproj y t n x e)) \ BVstem(C))
             = FV(C[σ(Eproj y t n x e)])
           Lemma:
             (x ↦ (c, ys)) ∈ C ⟹ y ∈ ys ⟹ {y} \ BVstem(C) ⊆ FV(C) *)
        admit.
      * admit. (* TODO *)
  - (* Top down dead constr *) intros _ R C x c ys e d r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    destruct (M.get ![x] δ) eqn:Hcount; [cond_failure|].
    specialize success with (x0 := x) (c0 := c) (ys0 := apply_r_list' σ ys).
    specialize success with (e0 := @rename exp_univ_exp σ e); cond_success success; unshelve eapply success.
    + exists σ. (* Follows from BV(e) ⊆ BV(Econstr x c ys e) *)
      admit.
    + (* Follows from Hcount *)
      admit.
    + reflexivity. + reflexivity. + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
         admit.
      * (* BV(C[σe]) ⊆ BV(C[σ(Econstr x c ys e)])
           FV(C[σe])
             = FV(C) ∪ (FV(σe) \ BVstem(C))
             = FV(C) ∪ (FV(σe) \ {x} \ BVstem(C)) (because x is dead)
             ⊆ FV(C) ∪ ((σ ys ∪ FV(σe)) \ {x} \ BVstem(C))
             = FV(C) ∪ (FV(σ(Econstr x c ys e)) \ BVstem(C))
             = FV(C[σ(Econstr x c ys e)]) *)
        admit.
      * admit.
  - (* Bottom up dead constr *) intros _ R C x c ys e r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, (M.get ![x] δ) eqn:Hcount; [cond_failure|].
    cond_success success; unshelve eapply success.
    + (* Follows from Hcount *) admit.
    + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
        admit.
      * (* BV(C[e]) ⊆ BV(C[Econstr x c ys e])
           FV(C[e]) ⊆ FV(C[Econstr x c ys e]) because x dead *)
        admit.
      * admit.
  - (* Top down dead proj *) intros _ R C x t n y e d r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    destruct (M.get ![x] δ) eqn:Hcount; [cond_failure|].
    specialize success with (x0 := x) (t0 := t) (n0 := n) (y0 := apply_r' σ y).
    specialize success with (e0 := @rename exp_univ_exp σ e); cond_success success; unshelve eapply success.
    + exists σ. (* Follows from BV(e) ⊆ BV(Eproj x c ys e) *)
      admit.
    + (* Follows from Hcount *)
      admit.
    + reflexivity. + reflexivity. + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
        admit.
      * (* BV(C[σe]) ⊆ BV(C[σ(Eproj x t n y e)])
           FV(C[σe]) = FV(C[σe]) \\ {x} (because x is dead)
                     ⊆ FV(C[σ(Eproj x t n y e)]) *)
        admit.
      * admit.
  - (* Bottom up dead proj *) intros _ R C x t n y e r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, (M.get ![x] δ) eqn:Hcount; [cond_failure|].
    cond_success success; unshelve eapply success.
    + (* Follows from Hcount *) admit.
    + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
        admit.
      * (* BV(C[e]) ⊆ BV(C[Eproj x t n y e])
           FV(C[e]) ⊆ FV(C[Eproj x t n y e]) because x dead *)
        admit.
      * admit.
  - (* Top down dead prim *) intros _ R C x p ys e d r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    destruct (M.get ![x] δ) eqn:Hcount; [cond_failure|].
    specialize success with (x0 := x) (p0 := p) (ys0 := apply_r_list' σ ys).
    specialize success with (e0 := @rename exp_univ_exp σ e); cond_success success; unshelve eapply success.
    + exists σ. (* Follows from BV(e) ⊆ BV(Eprim x p ys e) *)
      admit.
    + (* Follows from Hcount *)
      admit.
    + reflexivity. + reflexivity. + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
         admit.
      * (* BV(C[σe]) ⊆ BV(C[σ(Eprim x p ys e)])
           FV(C[σe]) = FV(C[σe]) \\ {x} (because x is dead)
                     ⊆ FV(C[σ(Eprim x p ys e)]) *)
        admit.
      * admit.
  - (* Bottom up dead prim *) intros _ R C x p ys e r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, (M.get ![x] δ) eqn:Hcount; [cond_failure|].
    cond_success success; unshelve eapply success.
    + (* Follows from Hcount *) admit.
    + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
        admit.
      * (* BV(C[e]) ⊆ BV(C[Eprim x p ys e])
           FV(C[e]) ⊆ FV(C[Eprim x p ys e]) because x dead *)
        admit.
      * admit.
  - (* Top down dead fun *) intros _ R C f ft xs e fds d r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    destruct (M.get ![f] δ) eqn:Hcount; [cond_failure|].
    specialize success with (f0 := f) (ft0 := ft) (xs0 := xs).
    specialize success with (e0 := @rename exp_univ_exp σ e) (fds0 := @rename exp_univ_list_fundef σ fds).
    cond_success success; unshelve eapply success.
    + exists σ. (* Follows from BV(fds) ⊆ BV(Ffun f ft xs e ∷ fds) *)
      admit.
    + (* Follows from Hcount *)
      admit.
    + reflexivity. + reflexivity. + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
        admit.
      * (* BV(C[σ fds]) ⊆ BV(C[σ(Ffun f ft xs e ∷ fds)])
           FV(C[σ fds]) ⊆ FV(C[σ(Ffun f ft xs e ∷ fds)]) because f dead *)
        admit.
      * admit.
  - (* Bottom up dead fun *) intros _ R C f ft xs e fds r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs, (M.get ![f] δ) eqn:Hcount; [cond_failure|].
    cond_success success; unshelve eapply success.
    + (* Follows from Hcount *) admit.
    + exact r.
    + unshelve eexists; [|split; [|split]].
      * (* Update counts *)
        admit.
      * (* Follows from Huniq *)
        admit.
      * (* BV(C[e]) ⊆ BV(C[Ffun f ft xs e ∷ fds])
           FV(C[e]) ⊆ FV(C[Ffun f ft xs e ∷ fds]) because f dead *)
        admit.
      * admit.
  - (* Top down dead bundle *) intros _ R C e r s success failure.
    destruct s as [δ [Huniq [Hdis Hδ]]] eqn:Hs.
    cond_success success; unshelve eapply success; [exact r|exists δ; split; [|split]].
    + (* Follows from Huniq *)
      admit.
    + clear - Hdis. rewrite !app_exp_c_eq, !isoBAB, !bound_var_app_ctx in *.
      (* TODO: hoist *)
      assert (occurs_free_Efun_nil : forall e, occurs_free (cps.Efun cps.Fnil e) <--> occurs_free e). {
        intros; split; repeat (normalize_occurs_free || normalize_sets); eauto with Ensembles_DB. }
      (* TODO: hoist *)
      assert (bound_var_Efun_nil : forall e, bound_var (cps.Efun cps.Fnil e) <--> bound_var e). {
        intros; split; repeat (normalize_bound_var || normalize_sets); eauto with Ensembles_DB. }
      rewrite occurs_free_exp_ctx; [|rewrite <- occurs_free_Efun_nil at 1; reflexivity].
      rewrite <- bound_var_Efun_nil; apply Hdis.
    + (* ∀ x, |C[Efun [] e]|x = |C[e]|x *) admit.
  Ltac unfold_delayD := unfold delayD, Delayed_D_rename in *.
  Ltac solve_delayD :=
    unbox_newtypes; cbn in *; repeat normalize_bound_var_in_ctx;
    eauto with Ensembles_DB.
  - (* Rename a pair *) intros _ R c e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k c); [exists σ; split; auto|]; reflexivity.
  - (* Rename empty list *) intros _ R [σ ?] k; cbn in *; exact (k eq_refl).
  - (* Rename cons case arms *) intros _ R [c e] ces [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply k; [exists σ; split|exists σ; split|]; [solve_delayD..|reflexivity].
  - (* Rename function definition *) intros _ R [f] [ft] xs e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k [f]! [ft]! xs); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename empty list *) intros _ R [σ ?] k; cbn in *; exact (k eq_refl).
  - (* Rename cons function definitions *) intros _ R [[f] [ft] xs e] fds [σ [Hdom Hran]] k.
    unshelve eapply k; [exists σ; split|exists σ; split|]; [..|reflexivity];
      unbox_newtypes; cbn in *; repeat normalize_bound_var_in_ctx;
      (eapply Disjoint_Included_r; [|eassumption]; eauto with Ensembles_DB).
  - (* Rename constr binding *) intros _ R x c ys e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x c (apply_r_list' σ ys)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename case expression *) intros _ R x ces [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k (apply_r' σ x)); [exists σ|]; [..|reflexivity].
    unbox_newtypes; cbn in *; rewrite !bound_var_Ecase in *; now split.
  - (* Rename proj binding *) intros _ R x t n y e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x t n (apply_r' σ y)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename letapp *) intros _ R x f ft ys e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x (apply_r' σ f) ft (apply_r_list' σ ys)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename bundle definition *) intros _ R fds e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply k; [exists σ|exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename cps app *) intros _ R f ft ys [σ [Hdom Hran]] k; unfold_delayD.
    now apply (k (apply_r' σ f) ft (apply_r_list' σ ys)).
  - (* Rename prim binding *) intros _ R x p ys e [σ [Hdom Hran]] k; unfold_delayD.
    unshelve eapply (k x p (apply_r_list' σ ys)); [exists σ|]; [solve_delayD..|reflexivity].
  - (* Rename halt *) intros _ R x [σ [Hdom Hran]] k; unfold_delayD; exact (k (apply_r' σ x) eq_refl).
  - (* Fuse renaming for proj folding *) destruct d0 as [σ Hσ] eqn:Hσ_eq; rewrite <- Hσ_eq in *.
    unshelve eexists; [exists (M.set ![y] ![y'] σ)|unbox_newtypes; cbn; subst d0].
    + (* dom(σ[y ↦ y']) = dom σ ∪ {y}
         ran(σ[y ↦ y']) ⊆ ran σ ∪ {y'}

         (dom σ ∪ {y}) # BV(e1):
           dom σ # BV(e1) by assumption
           {y} # BV(e1)
             ⟸ {y} # BV(σ e1)
             ⟸ {y} # BV(e0)
             ⟸ UB(Eproj y t n x e0)

         (ran σ ∪ {y'}) # BV(e1):
           ran σ # BV(e1) by assumption
           {y'} # BV(e1):
             y' appears in C somewhere, because y' ∈ ys and (c, ys) is known ctor value.
             If y' ∈ BV(C) then y' can't be bound elsewhere, because of UB
             If y' ∉ BV(C) then y' appears free in C and it can't be bound in e1 *)
      admit.
    + (* y ∉ dom σ ∪ ran σ because y ∈ BV(Eproj y t n x e).
         So (y ↦ y') ∘ σ = σ[y ↦ y'] *)
      admit.
Admitted.
