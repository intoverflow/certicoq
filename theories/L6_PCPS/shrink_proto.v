Require Import Coq.Strings.String.
Require Import Coq.Sets.Ensembles Coq.ZArith.ZArith.
Require Import L6.Ensembles_util L6.map_util L6.List_util.
Require Import L6.state L6.alpha_conv L6.identifiers L6.functions L6.shrink_cps L6.stemctx.
Require Import L6.Prototype.
Require Import L6.cps_proto L6.proto_util.

Require Import Lia.

Require Import Coq.Lists.List.
Import ListNotations.

Unset Strict Unquote Universe Mode.

(** * Shrink rewrites *)

(** Known constructor values *)

(* (x ↦ Con c ys) ∈ C *)
Definition known_ctor {A} x c ys (C : exp_c A exp_univ_exp) : Prop :=
  exists D E, C = D >:: Econstr3 x c ys >++ E.

(** Occurrence counts *)

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

Section Census.

Context
  (* Update to occurrence counts *)
  (upd : option positive -> option positive)
  (* Delayed renaming *)
  (σ : r_map).

Definition census_var (x : var) (δ : c_map) : c_map :=
  let x := ![apply_r' σ x] in
  match upd (M.get x δ) with
  | Some n => M.set x n δ
  | None => M.remove x δ
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

(** (census e δ)(x) = upd^(|σe|x)(δ(x)) *)

Lemma iter_fuse {A} n m (f : A -> A) x : Nat.iter n f (Nat.iter m f x) = Nat.iter (n + m) f x.
Proof.
  revert m; induction n as [|n IHn]; [reflexivity|intros; cbn].
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x); now rewrite IHn.
Qed.

Lemma census_var_corresp' x_in x δ :
  M.get ![x] (census_var x_in δ) = Nat.iter (count_var x (apply_r' σ x_in)) upd (M.get ![x] δ).
Proof.
  unbox_newtypes; unfold census_var, count_var in *; cbn in *.
  destruct (Pos.eqb_spec x (apply_r σ x_in)); cbn in *.
  - subst; destruct (upd (M.get (apply_r σ x_in) δ)) as [n|] eqn:Hn; now rewrite ?M.gss, ?M.grs.
  - destruct (upd (M.get (apply_r σ x_in) δ)) as [n'|] eqn:Hn; now rewrite ?M.gso, ?M.gro by auto.
Qed.

Fixpoint census_vars_corresp' xs x δ :
  M.get ![x] (census_vars xs δ) = Nat.iter (count_vars x (apply_r_list' σ xs)) upd (M.get ![x] δ).
Proof.
  destruct xs as [|x' xs]; [reflexivity|cbn].
  change (fold_right census_var δ xs) with (census_vars xs δ).
  change (total (map _ ?xs)) with (count_vars x xs).
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x).
  change (map (apply_r' σ) xs) with (apply_r_list' σ xs).
  change (mk_var (apply_r σ (un_var x'))) with (apply_r' σ x').
  now rewrite <- iter_fuse, <- census_vars_corresp', <- census_var_corresp'.
Qed.

(* TODO: move to proto_util *)
Definition rename_all_ces' σ ces : list (ctor_tag * exp) :=
  map (fun '(c, e) => (c, rename_all' σ e)) ces.
Definition rename_all_fds' σ fds : list fundef :=
  map (fun '(Ffun f ft xs e) => Ffun f ft xs (rename_all' σ e)) fds.

Ltac collapse_primes :=
  change (count_ces' count_exp) with count_ces in *;
  change (count_fds' count_exp) with count_fds in *;
  change (census_ces' census_exp) with census_ces in *;
  change (census_fds' census_exp) with census_fds in *;
  change (map (fun '(c, e) => (c, rename_all' ?σ e))) with (rename_all_ces' σ) in *;
  change (map (fun '(Ffun f ft xs e) => Ffun f ft xs (rename_all' ?σ e))) with (rename_all_fds' σ) in *;
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x);
  change (mk_var (apply_r ?σ (un_var ?x))) with (apply_r' σ x);
  change (total (map (fun '(_, e) => count_exp ?x e) ?ces)) with (count_ces x ces) in *;
  change (total (map (fun '(Ffun _ _ _ e) => count_exp ?x e) ?fds)) with (count_fds x fds) in *;
  (* TODO: move to proto_util? *)
  change (ces_of_proto' exp_of_proto) with ces_of_proto in *;
  change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.

Fixpoint census_exp_corresp' e x δ {struct e} :
  M.get ![x] (census_exp e δ) = Nat.iter (count_exp x (rename_all' σ e)) upd (M.get ![x] δ).
Proof.
  destruct e; cbn; collapse_primes; try solve [
    now rewrite <- ?iter_fuse, <- ?census_exp_corresp', <- ?census_vars_corresp', <- ?census_var_corresp'].
  - enough (Hces : forall x δ,
             let count := count_ces x (rename_all_ces' σ ces) in
             M.get ![x] (census_ces ces δ) = Nat.iter count upd (M.get ![x] δ)).
    { now rewrite <- iter_fuse, <- Hces, <- census_var_corresp'. }
    clear - census_exp_corresp'.
    induction ces as [|[c e] ces IHces]; [reflexivity|cbn; intros x δ; collapse_primes].
    now rewrite <- iter_fuse, <- IHces, <- census_exp_corresp'.
  - enough (Hfds : forall x δ,
             let count := count_fds x (rename_all_fds' σ fds) in
             M.get ![x] (census_fds fds δ) = Nat.iter count upd (M.get ![x] δ)).
    { now rewrite <- iter_fuse, <- census_exp_corresp', <- Hfds. } 
    clear - census_exp_corresp'.
    induction fds as [|[f ft xs e] fds IHfds]; [reflexivity|cbn; intros x δ; collapse_primes].
    now rewrite <- iter_fuse, <- IHfds, <- census_exp_corresp'.
Qed.

Lemma census_ces_corresp' ces : forall x δ,
  M.get ![x] (census_ces ces δ) = Nat.iter (count_ces x (rename_all_ces' σ ces)) upd (M.get ![x] δ).
Proof.
  induction ces as [|[c e] ces IHces]; [reflexivity|cbn; intros x δ; collapse_primes].
  now rewrite <- iter_fuse, <- IHces, <- census_exp_corresp'.
Qed.

End Census.

Ltac collapse_primes :=
  change (count_ces' count_exp) with count_ces in *;
  change (count_fds' count_exp) with count_fds in *;
  change (map (fun '(c, e) => (c, rename_all' ?σ e))) with (rename_all_ces' σ) in *;
  change (map (fun '(Ffun f ft xs e) => Ffun f ft xs (rename_all' ?σ e))) with (rename_all_fds' σ) in *;
  change (nat_rect _ ?x (fun _ => ?f) ?n) with (Nat.iter n f x);
  change (mk_var (apply_r ?σ (un_var ?x))) with (apply_r' σ x);
  change (total (map (fun '(_, e) => count_exp ?x e) ?ces)) with (count_ces x ces) in *;
  change (total (map (fun '(Ffun _ _ _ e) => count_exp ?x e) ?fds)) with (count_fds x fds) in *;
  change (map (apply_r' ?σ) ?xs) with (apply_r_list' σ xs) in *;
  change (total (map (count_var ?x) ?xs)) with (count_vars x xs) in *;
  (* TODO: move to proto_util? *)
  change (ces_of_proto' exp_of_proto) with ces_of_proto in *;
  change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.

(** Some convenient specializations *)

Definition succ_upd n :=
  match n with
  | Some n => Some (Pos.succ n)
  | None => Some 1
  end%positive.

Definition pred_upd n :=
  match n with
  | Some 1 | None => None
  | Some n => Some (Pos.pred n)
  end%positive.

Notation census_exp_succ := (census_exp succ_upd).
Notation census_exp_pred := (census_exp pred_upd).
Notation census_ces_succ := (census_ces succ_upd).
Notation census_ces_pred := (census_ces pred_upd).

Definition nat_of_count n :=
  match n with
  | Some n => Pos.to_nat n
  | None => 0
  end.

Lemma nat_of_count_succ_upd n : nat_of_count (succ_upd n) = S (nat_of_count n).
Proof. destruct n as [n|]; cbn; zify; lia. Qed.

Lemma nat_of_count_iter_succ_upd n c : nat_of_count (Nat.iter n succ_upd c) = n + nat_of_count c.
Proof.
  induction n as [|n IHn]; [reflexivity|unfold Nat.iter in *; cbn].
  now rewrite nat_of_count_succ_upd, IHn.
Qed.

Lemma nat_of_count_pred_upd n : nat_of_count (pred_upd n) = nat_of_count n - 1.
Proof.
  destruct n; cbn; [|auto].
  destruct (Pos.eq_dec p 1)%positive; subst; [reflexivity|].
  match goal with
  | |- nat_of_count ?e = _ =>
    assert (Heqn : e = Some (Pos.pred p)) by (now destruct p)
  end.
  rewrite Heqn; cbn; lia.
Qed.

Lemma nat_of_count_iter_pred_upd n c : nat_of_count (Nat.iter n pred_upd c) = nat_of_count c - n.
Proof.
  induction n as [|n IHn]; [cbn; lia|unfold Nat.iter in *; cbn].
  now rewrite nat_of_count_pred_upd, IHn.
Qed.

Definition get_count (x : var) δ := nat_of_count (M.get ![x] δ).

Lemma census_exp_succ_corresp e x σ δ :
  get_count x (census_exp_succ σ e δ) = count_exp x (rename_all' σ e) + get_count x δ.
Proof. unfold get_count; now rewrite census_exp_corresp', nat_of_count_iter_succ_upd. Qed.

Lemma census_exp_pred_corresp e x σ δ :
  get_count x (census_exp_pred σ e δ) = get_count x δ - count_exp x (rename_all' σ e).
Proof. unfold get_count; now rewrite census_exp_corresp', nat_of_count_iter_pred_upd. Qed.

Lemma census_ces_pred_corresp ces x σ δ :
  get_count x (census_ces_pred σ ces δ) = get_count x δ - count_ces x (rename_all_ces' σ ces).
Proof. unfold get_count; now rewrite census_ces_corresp', nat_of_count_iter_pred_upd. Qed.

(** * Occurrence counts for one-hole contexts *)

Definition count_frame {A B} (x_in : var) (f : exp_frame_t A B) : nat. refine(
  match f with
  | pair_ctor_tag_exp0 e => count_exp x_in e
  | pair_ctor_tag_exp1 c => 0
  | cons_prod_ctor_tag_exp0 ces => count_ces x_in ces
  | cons_prod_ctor_tag_exp1 (_, e) => count_exp x_in e
  | Ffun0 ft xs e => count_exp x_in e
  | Ffun1 f xs e => count_exp x_in e
  | Ffun2 f ft e => count_exp x_in e
  | Ffun3 f ft xs => 0
  | cons_fundef0 fds => count_fds x_in fds
  | cons_fundef1 (Ffun f ft xs e) => count_exp x_in e
  | Econstr0 c ys e => count_vars x_in ys + count_exp x_in e
  | Econstr1 x ys e => count_vars x_in ys + count_exp x_in e
  | Econstr2 x c e => count_exp x_in e
  | Econstr3 x c ys => count_vars x_in ys
  | Ecase0 ces => count_ces x_in ces
  | Ecase1 x => count_var x_in x
  | Eproj0 c n y e => count_var x_in y + count_exp x_in e
  | Eproj1 x n y e => count_var x_in y + count_exp x_in e
  | Eproj2 x c y e => count_var x_in y + count_exp x_in e
  | Eproj3 x c n e => count_exp x_in e
  | Eproj4 x c n y => count_var x_in y
  | Eletapp0 f ft ys e => count_var x_in f + count_vars x_in ys + count_exp x_in e
  | Eletapp1 x ft ys e => count_vars x_in ys + count_exp x_in e
  | Eletapp2 x f ys e => count_var x_in f + count_vars x_in ys + count_exp x_in e
  | Eletapp3 x f ft e => count_var x_in f + count_exp x_in e
  | Eletapp4 x f ft ys => count_var x_in f + count_vars x_in ys
  | Efun0 e => count_exp x_in e
  | Efun1 fds => count_fds x_in fds
  | Eapp0 ft xs => count_vars x_in xs
  | Eapp1 f xs => count_var x_in f + count_vars x_in xs
  | Eapp2 f ft => count_var x_in f
  | Eprim0 p ys e => count_vars x_in ys + count_exp x_in e
  | Eprim1 x ys e => count_vars x_in ys + count_exp x_in e
  | Eprim2 x p e => count_exp x_in e
  | Eprim3 x p ys => count_vars x_in ys
  | Ehalt0 => 0
  end).
Defined.

Fixpoint count_ctx {A B} (x_in : var) (C : exp_c A B) {struct C} : nat :=
  match C with
  | <[]> => 0
  | C >:: f => count_ctx x_in C + count_frame x_in f
  end.

Definition count {A} x : univD A -> nat :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(_, e) => count_exp x e
  | exp_univ_list_prod_ctor_tag_exp => fun ces => count_ces x ces
  | exp_univ_fundef => fun '(Ffun _ _ _ e) => count_exp x e
  | exp_univ_list_fundef => fun fds => count_fds x fds
  | exp_univ_exp => fun e => count_exp x e
  | exp_univ_var => fun y => count_var x y
  | exp_univ_fun_tag => fun _ => 0
  | exp_univ_ctor_tag => fun _ => 0
  | exp_univ_prim => fun _ => 0
  | exp_univ_N => fun _ => 0
  | exp_univ_list_var => fun xs => count_vars x xs
  end.

(* TODO: Merge with uncurry_proto and move to util *)
Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

Lemma count_frame_app A B (f : exp_frame_t A B) e x :
  match A with
  | exp_univ_var
  | exp_univ_fun_tag
  | exp_univ_ctor_tag
  | exp_univ_prim
  | exp_univ_N
  | exp_univ_list_var => True
  | _ => count x (frameD f e) = count_frame x f + count x e
  end.
Proof.
  clearpose HA' A' A; clearpose HB' B' B.
  destruct A', f; try solve [discriminate|exact I];
  destruct B'; try solve [discriminate|reflexivity].
  - destruct e as [c e]; cbn. change (total _) with (count_ces x l); lia.
  - destruct e as [f ft xs e]; cbn; change (total _) with (count_fds x l); lia.
  - cbn; change (count_fds' count_exp) with count_fds; lia.
Qed.

Lemma count_ctx_app' : forall n A B (C : exp_c A B) e x,
  frames_len C = n ->
  match A with
  | exp_univ_var
  | exp_univ_fun_tag
  | exp_univ_ctor_tag
  | exp_univ_prim
  | exp_univ_N
  | exp_univ_list_var => True
  | _ => count x (C ⟦ e ⟧) = count_ctx x C + count x e
  end.
Proof.
  induction n as [n IHn] using lt_wf_ind; intros A B C e x Hlen.
  clearpose HA' A' A; clearpose HB' B' B.
  destruct C as [|A AB B f C]; [subst; cbn; now destruct A|].
  clearpose HAB' AB' AB.
  destruct A', f; try solve [discriminate|exact I]; destruct AB'; try discriminate;
  cbn in Hlen; rewrite framesD_cons; assert (Hlt : frames_len C < n) by (cbn; lia);
  specialize IHn with (m := frames_len C) (C := C) (x := x);
  specialize (IHn Hlt); lazy iota in IHn; rewrite IHn by reflexivity;
  match type of HA' with ?T = _ => rewrite (@count_frame_app T) end; cbn; lia.
Qed.

Corollary count_ctx_app : forall (C : exp_c exp_univ_exp exp_univ_exp) e x,
  count_exp x (C ⟦ e ⟧) = count_ctx x C + count x e.
Proof. intros; now apply (@count_ctx_app' (frames_len C) exp_univ_exp exp_univ_exp). Qed.

Corollary count_ctx_fds_app : forall (C : exp_c exp_univ_list_fundef exp_univ_exp) fds x,
  count_exp x (C ⟦ fds ⟧) = count_ctx x C + count x fds.
Proof. intros; now apply (@count_ctx_app' (frames_len C) exp_univ_list_fundef exp_univ_exp). Qed.

(** * State variable *)

Definition S_shrink {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := {
  δ : c_map |
  (* The program being transformed *)
  let P := C ⟦ e ⟧ in
  (* The program has well-behaved bindings *)
  unique_bindings ![P] /\ Disjoint _ (bound_var ![P]) (occurs_free ![P]) /\
  (* δ holds valid occurrence counts *)
  (forall x, get_count x δ = count_exp x P) }.

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

(* TODO: move to proto_util *)
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

(** Case folding helpers *)

Fixpoint find_case (c : ctor_tag) (ces : list (ctor_tag * exp)) : option exp :=
  match ces with
  | [] => None
  | (c', e) :: ces => if ![c] =? ![c'] then Some e else find_case c ces
  end%positive.

Lemma find_case_spec c e ces :
  find_case c ces = Some e -> exists ces1 ces2,
  ~ In c (map fst ces1) /\ ces = ces1 ++ (c, e) :: ces2.
Proof.
  induction ces as [|[c' e'] ces IHces]; [inversion 1|unbox_newtypes; cbn].
  destruct (Pos.eqb_spec c c'); intros Heq; [inv Heq|].
  - exists [], ces; split; auto.
  - destruct (IHces Heq) as [ces1 [ces2 [Hnotin Hces12]]].
    exists ((mk_ctor_tag c', e') :: ces1), ces2; cbn; subst ces; split; auto.
    intros [Heq'|Hin]; [now inv Heq'|auto].
Qed.

Lemma find_case_In c e ces : find_case c ces = Some e -> In (c, e) ces.
Proof.
  intros H; destruct (find_case_spec c e ces H) as [ces1 [ces2 [Hnotin Hces]]]; subst ces.
  apply in_or_app; right; now left.
Qed.

Fixpoint census_case_pred σ (c : ctor_tag) (ces : list (ctor_tag * exp)) δ :=
  match ces with
  | [] => δ
  | (c', e) :: ces =>
    if (![c] =? ![c'])%positive
    then census_ces pred_upd σ ces δ
    else census_case_pred σ c ces (census_exp_pred σ e δ)
  end.

Lemma total_cons x xs : total (x :: xs) = x + total xs. Proof. reflexivity. Qed.
Lemma total_app xs ys : total (xs ++ ys) = total xs + total ys.
Proof. induction xs as [|x xs IHxs]; cbn; auto; rewrite IHxs; lia. Qed.

(* TODO: move to proto_util *)
Lemma In_ces_bound : forall c e ces, In (c, e) ces -> bound_var ![e] \subset bound_var_ces ![ces].
Proof.
  induction ces as [|[[c'] e'] ces IHces]; [inversion 1|].
  destruct 1 as [Heq|Hne]; [inv Heq|]; cbn; eauto with Ensembles_DB.
Qed.

Fixpoint census_case_pred_spec n σ x δ ces ces1 c e ces2 {struct ces1} :
  ~ In c (map fst ces1) ->
  ces = ces1 ++ (c, e) :: ces2 ->
  get_count x δ = n + count_ces x (rename_all_ces' σ ces) ->
  get_count x (census_case_pred σ c ces δ) = n + count_exp x (rename_all' σ e).
Proof.
  destruct ces1 as [|[c' e'] ces1]; intros Hin Heq Hget; cbn in Heq; subst ces.
  - unfold census_case_pred; fold census_case_pred. rewrite Pos.eqb_refl.
    cbn in Hget; collapse_primes; rewrite census_ces_pred_corresp, Hget; lia.
  - unfold count_ces, count_ces', rename_all_ces' in Hget.
    repeat rewrite ?total_cons, ?total_app, ?map_cons, ?map_app in *; collapse_primes.
    unfold census_case_pred; fold census_case_pred.
    destruct (Pos.eqb_spec ![c] ![c']) as [Hc|Hc].
    { unbox_newtypes; cbn in Hc; inv Hc; contradiction Hin; now left. }
    rewrite census_case_pred_spec with (n := n) (ces1 := ces1) (e := e) (ces2 := ces2); auto.
    + now cbn in Hin.
    + unfold count_ces, count_ces', rename_all_ces'.
      repeat rewrite ?total_cons, ?total_app, ?map_cons, ?map_app in *; collapse_primes.
      rewrite census_exp_pred_corresp, Hget; lia.
Qed.

Notation census_var_pred := (census_var pred_upd).
Lemma census_var_pred_corresp x_in x σ δ :
  get_count x (census_var_pred σ x_in δ) = get_count x δ - count_var x (apply_r' σ x_in).
Proof. unfold get_count; now rewrite census_var_corresp', nat_of_count_iter_pred_upd. Qed.

Notation census_vars_pred := (census_vars pred_upd).
Lemma census_vars_pred_corresp xs x σ δ :
  get_count x (census_vars_pred σ xs δ) = get_count x δ - count_vars x (apply_r_list' σ xs).
Proof. unfold get_count; now rewrite census_vars_corresp', nat_of_count_iter_pred_upd. Qed.

(** Proj folding helpers *)

(* Substitute y for x in δ *)
Definition census_subst (y x : var) (δ : c_map) :=
  let x := ![x] in
  let y := ![y] in
  match M.get x δ with
  | None => δ
  | Some n =>
    match M.get y δ with
    | None => M.set y n (M.remove x δ)
    | Some m => M.set y (n + m)%positive (M.remove x δ)
    end
  end.

(* TODO: move to Ensembles_util or identifiers *)
Lemma occurs_free_Efun_nil : forall e, occurs_free (cps.Efun cps.Fnil e) <--> occurs_free e.
Proof. intros; split; repeat (normalize_occurs_free || normalize_sets); eauto with Ensembles_DB. Qed.

Lemma bound_var_Efun_nil : forall e, bound_var (cps.Efun cps.Fnil e) <--> bound_var e.
Proof. intros; split; repeat (normalize_bound_var || normalize_sets); eauto with Ensembles_DB. Qed.

Lemma census_subst_dom : forall (y x : var) (δ : c_map),
  x <> y ->
  get_count x (census_subst y x δ) = 0.
Proof.
  clear; intros y x δ Hne; unfold get_count, census_subst.
  destruct (M.get ![x] δ) as [x'|] eqn:Hgetx; [|now rewrite Hgetx].
  destruct (M.get ![y] δ) as [y'|] eqn:Hgety;
   (rewrite M.gso by now (unbox_newtypes; cbn)); now rewrite M.grs.
Qed.

Lemma census_subst_ran : forall (y x : var) (δ : c_map),
  x <> y ->
  get_count y (census_subst y x δ) = get_count x δ + get_count y δ.
Proof.
  clear; intros y x δ Hne; unfold get_count, census_subst.
  destruct (M.get ![x] δ) as [x'|] eqn:Hgetx; [|reflexivity].
  destruct (M.get ![y] δ) as [y'|] eqn:Hgety;
  rewrite M.gss; cbn; lia.
Qed.

Lemma census_subst_neither : forall (z y x : var) (δ : c_map),
  x <> y -> z <> x -> z <> y ->
  get_count z (census_subst y x δ) = get_count z δ.
Proof.
  clear; intros z y x δ Hne Hz1 Hz2; unfold get_count, census_subst.
  destruct (M.get ![x] δ) as [x'|] eqn:Hgetx; [|reflexivity].
  destruct (M.get ![y] δ) as [y'|] eqn:Hgety;
    rewrite M.gso by (unbox_newtypes; now cbn); now rewrite M.gro by (unbox_newtypes; now cbn).
Qed.

Lemma count_var_subst_dom : forall (y x : var) (x_in : var),
  x <> y -> count_var x (apply_r' (M.set ![x] ![y] (M.empty _)) x_in) = 0.
Proof.
  clear; intros y x x_in Hne; unfold apply_r', apply_r, count_var; unbox_newtypes; cbn.
  (assert (x <> y) by congruence); destruct (Pos.eq_dec x_in x).
  - subst; rewrite M.gss; now destruct (Pos.eqb_spec x y).
  - rewrite M.gso by auto; rewrite M.gempty. now destruct (Pos.eqb_spec x x_in).
Qed.

Lemma count_vars_subst_dom : forall (xs : list var) (y x : var),
  x <> y -> count_vars x (apply_r_list' (M.set ![x] ![y] (M.empty _)) xs) = 0. 
Proof.
  clear; induction xs as [|x xs IHxs]; [reflexivity|cbn; intros; collapse_primes].
  rewrite count_var_subst_dom by auto; rewrite IHxs by auto; auto.
Qed.

Fixpoint count_exp_subst_dom (y x : var) (e : exp) {struct e} :
  x <> y ->
  count_exp x (rename_all' (M.set ![x] ![y] (M.empty _)) e) = 0.
Proof.
  intros Hne; destruct e; cbn; collapse_primes; repeat first
    [rewrite count_exp_subst_dom by auto
    |rewrite count_var_subst_dom by auto
    |rewrite count_vars_subst_dom by auto]; auto.
  - induction ces as [|[c e] ces IHces]; cbn in *; auto; collapse_primes.
    now rewrite IHces, count_exp_subst_dom by auto.
  - clear e; rewrite Nat.add_0_r; induction fds as [|[f ft xs e] fds IHfds]; cbn in *; auto; collapse_primes.
    now rewrite IHfds, count_exp_subst_dom by auto.
Qed.

Lemma count_var_subst_ran : forall (y x : var) (x_in : var),
  x <> y -> count_var y (apply_r' (M.set ![x] ![y] (M.empty _)) x_in) = count_var x x_in + count_var y x_in.
Proof.
  clear; intros y x x_in Hne; unfold apply_r', apply_r, count_var; unbox_newtypes; cbn.
  (assert (x <> y) by congruence); destruct (Pos.eq_dec x_in x).
  - subst; rewrite M.gss; cbn.
    destruct (Pos.eqb_spec y y), (Pos.eqb_spec x x), (Pos.eqb_spec y x); subst; auto; congruence.
  - rewrite M.gso by auto; rewrite M.gempty.
    destruct (Pos.eqb_spec y x_in), (Pos.eqb_spec x x_in); subst; auto; congruence.
Qed.

Lemma count_vars_subst_ran : forall (xs : list var) (y x : var),
  x <> y -> count_vars y (apply_r_list' (M.set ![x] ![y] (M.empty _)) xs) = count_vars x xs + count_vars y xs.
Proof.
  clear; induction xs as [|x xs IHxs]; [reflexivity|cbn; intros; collapse_primes].
  rewrite count_var_subst_ran by auto; rewrite IHxs by auto; lia.
Qed.

Fixpoint count_exp_subst_ran (y x : var) (e : exp) {struct e} :
  x <> y -> count_exp y (rename_all' (M.set ![x] ![y] (M.empty _)) e) = count_exp x e + count_exp y e.
Proof.
  intros Hne; destruct e; cbn; collapse_primes; repeat first
    [rewrite count_exp_subst_ran by auto
    |rewrite count_var_subst_ran by auto
    |rewrite count_vars_subst_ran by auto]; auto; try lia.
  - enough (Hces :
      count_ces y (rename_all_ces' (@M.set cps.var (un_var x) (un_var y) (M.empty cps.var)) ces) =
      count_ces x ces + count_ces y ces) by lia.
    induction ces as [|[c e] ces IHces]; cbn in *; auto; collapse_primes.
    now rewrite IHces, count_exp_subst_ran by auto.
  - enough (Hfds :
      count_fds y (rename_all_fds' (@M.set cps.var (un_var x) (un_var y) (M.empty cps.var)) fds) =
      count_fds x fds + count_fds y fds) by lia.
    clear e; induction fds as [|[f ft xs e] fds IHfds]; cbn in *; auto; collapse_primes.
    now rewrite IHfds, count_exp_subst_ran by auto.
Qed.

Lemma count_var_subst_neither : forall (z y x : var) (x_in : var),
  x <> y -> z <> x -> z <> y ->
  count_var z (apply_r' (M.set ![x] ![y] (M.empty _)) x_in) = count_var z x_in.
Proof.
  clear; intros z y x x_in Hne Hz1 Hz2; unfold apply_r', apply_r, count_var; unbox_newtypes; cbn.
  destruct (Pos.eq_dec x_in x).
  - subst; rewrite M.gss; cbn; destruct (Pos.eqb_spec z y), (Pos.eqb_spec z x); subst; auto; congruence.
  - rewrite M.gso by auto; now rewrite M.gempty.
Qed.

Lemma count_vars_subst_neither : forall (xs : list var) (z y x : var),
  x <> y -> z <> x -> z <> y ->
  count_vars z (apply_r_list' (M.set ![x] ![y] (M.empty _)) xs) = count_vars z xs.
Proof.
  clear; induction xs as [|x xs IHxs]; [reflexivity|cbn; intros; collapse_primes].
  rewrite count_var_subst_neither by auto; rewrite IHxs by auto; lia.
Qed.

Fixpoint count_exp_subst_neither (z y x : var) (e : exp) {struct e} :
  x <> y -> z <> x -> z <> y ->
  count_exp z (rename_all' (M.set ![x] ![y] (M.empty _)) e) = count_exp z e.
Proof.
  intros Hne Hz1 Hz2; destruct e; cbn; collapse_primes; repeat first
    [rewrite count_exp_subst_neither by auto
    |rewrite count_var_subst_neither by auto
    |rewrite count_vars_subst_neither by auto]; auto; try lia.
  - f_equal; induction ces as [|[c e] ces IHces]; cbn in *; auto; collapse_primes.
  - f_equal; clear e; induction fds as [|[f ft xs e] fds IHfds]; cbn in *; auto; collapse_primes.
Qed.

(* TODO: move to proto_util *)
Lemma var_eq_dec : forall x y : var, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Lemma count_var_neq : forall (x y : var), x <> y -> count_var x y = 0. 
Proof. unfold count_var; intros x y Hne; unbox_newtypes; cbn; destruct (Pos.eqb_spec x y); congruence. Qed.

(*
(* Bound/free variables in contexts 
   TODO: move to cps_proto.v *)

Definition bstem_frame {A B} (f : exp_frame_t A B) : Ensemble cps.var. refine(
  match f with
  | pair_ctor_tag_exp0 e => Empty_set _
  | pair_ctor_tag_exp1 c => Empty_set _
  | cons_prod_ctor_tag_exp0 ces => Empty_set _
  | cons_prod_ctor_tag_exp1 (_, e) => Empty_set _
  | Ffun0 ft xs e => Empty_set _
  | Ffun1 f xs e => Empty_set _
  | Ffun2 f ft e => Empty_set _
  | Ffun3 f ft xs => ![f] |: FromList ![xs]
  | cons_fundef0 fds => name_in_fundefs ![fds]
  | cons_fundef1 (Ffun f ft xs e) => [set ![f]]
  | Econstr0 c ys e => Empty_set _
  | Econstr1 x ys e => Empty_set _
  | Econstr2 x c e => Empty_set _
  | Econstr3 x c ys => [set ![x]]
  | Ecase0 ces => Empty_set _
  | Ecase1 x => Empty_set _
  | Eproj0 c n y e => Empty_set _
  | Eproj1 x n y e => Empty_set _
  | Eproj2 x c y e => Empty_set _
  | Eproj3 x c n e => Empty_set _
  | Eproj4 x c n y => [set ![x]]
  | Eletapp0 f ft ys e => Empty_set _
  | Eletapp1 x ft ys e => Empty_set _
  | Eletapp2 x f ys e => Empty_set _
  | Eletapp3 x f ft e => Empty_set _
  | Eletapp4 x f ft ys => [set ![x]]
  | Efun0 e => Empty_set _
  | Efun1 fds => name_in_fundefs ![fds]
  | Eapp0 ft xs => Empty_set _
  | Eapp1 f xs => Empty_set _
  | Eapp2 f ft => Empty_set _
  | Eprim0 p ys e => Empty_set _
  | Eprim1 x ys e => Empty_set _
  | Eprim2 x p e => Empty_set _
  | Eprim3 x p ys => [set ![x]]
  | Ehalt0 => Empty_set _
  end).
Defined.

Fixpoint bstem_ctx {A B} (C : exp_c A B) : Ensemble cps.var :=
  match C with
  | <[]> => Empty_set _
  | C >:: f => bstem_ctx C :|: bstem_frame f
  end.

(* TODO: move to proto_util *)

Fixpoint occurs_free_ces (ces : list (cps.ctor_tag * cps.exp)) :=
  match ces with
  | [] => Empty_set _
  | (c, e) :: ces => occurs_free e :|: occurs_free_ces ces
  end.

Lemma occurs_free_Ecase x ces :
  occurs_free (cps.Ecase x ces) <--> x |: occurs_free_ces ces.
Proof.
  induction ces as [|[c e] ces IHces]; cbn; repeat normalize_occurs_free; [eauto with Ensembles_DB|].
  rewrite IHces; split; eauto 3 with Ensembles_DB.
Qed.

Definition free_frame {A B} (f : exp_frame_t A B) : Ensemble cps.var. refine(
  match f with
  | pair_ctor_tag_exp0 e => occurs_free ![e]
  | pair_ctor_tag_exp1 c => Empty_set _
  | cons_prod_ctor_tag_exp0 ces => occurs_free_ces ![ces]
  | cons_prod_ctor_tag_exp1 (_, e) => occurs_free ![e]
  | Ffun0 ft xs e => Empty_set _
  | Ffun1 f xs e => Empty_set _
  | Ffun2 f ft e => Empty_set _
  | Ffun3 f ft xs => Empty_set _
  | cons_fundef0 fds => occurs_free_fundefs ![fds]
  | cons_fundef1 fd => occurs_free_fundefs ![[fd]]
  | Econstr0 c ys e => Empty_set _
  | Econstr1 x ys e => Empty_set _
  | Econstr2 x c e => Empty_set _
  | Econstr3 x c ys => FromList ![ys]
  | Ecase0 ces => occurs_free_ces ![ces]
  | Ecase1 x => [set ![x]]
  | Eproj0 c n y e => Empty_set _
  | Eproj1 x n y e => Empty_set _
  | Eproj2 x c y e => Empty_set _
  | Eproj3 x c n e => Empty_set _
  | Eproj4 x c n y => [set ![y]]
  | Eletapp0 f ft ys e => Empty_set _
  | Eletapp1 x ft ys e => Empty_set _
  | Eletapp2 x f ys e => Empty_set _
  | Eletapp3 x f ft e => Empty_set _
  | Eletapp4 x f ft ys => ![f] |: FromList ![ys]
  | Efun0 e => occurs_free ![e]
  | Efun1 fds => occurs_free_fundefs ![fds]
  | Eapp0 ft xs => Empty_set _
  | Eapp1 f xs => Empty_set _
  | Eapp2 f ft => Empty_set _
  | Eprim0 p ys e => Empty_set _
  | Eprim1 x ys e => Empty_set _
  | Eprim2 x p e => Empty_set _
  | Eprim3 x p ys => FromList ![ys]
  | Ehalt0 => Empty_set _
  end).
Defined.

Fixpoint free_ctx {A B} (C : exp_c A B) : Ensemble cps.var :=
  match C with
  | <[]> => Empty_set _
  | C >:: f => free_ctx C :|: free_frame f
  end.

Definition free {A} : univD A -> Ensemble cps.var :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(_, e) => occurs_free ![e]
  | exp_univ_list_prod_ctor_tag_exp => fun ces => occurs_free_ces ![ces]
  | exp_univ_fundef => fun fd => occurs_free_fundefs ![[fd]]
  | exp_univ_list_fundef => fun fds => occurs_free_fundefs ![fds]
  | exp_univ_exp => fun e => occurs_free ![e]
  | exp_univ_var => fun x => [set ![x]]
  | exp_univ_fun_tag => fun _ => Empty_set _
  | exp_univ_ctor_tag => fun _ => Empty_set _
  | exp_univ_prim => fun _ => Empty_set _
  | exp_univ_N => fun _ => Empty_set _
  | exp_univ_list_var => fun xs => FromList ![xs]
  end.
*)

Lemma occurs_free_ctx_mut :
  (forall (c : ctx.exp_ctx) (e e' : cps.exp),
   occurs_free e \subset occurs_free e' ->
   occurs_free (ctx.app_ctx_f c e) \subset occurs_free (ctx.app_ctx_f c e')) /\
  (forall (B : ctx.fundefs_ctx) (e e' : cps.exp),
   occurs_free e \subset occurs_free e' ->
   occurs_free_fundefs (ctx.app_f_ctx_f B e) \subset occurs_free_fundefs (ctx.app_f_ctx_f B e')).
Proof.
  apply ctx.exp_fundefs_ctx_mutual_ind; intros; cbn; repeat normalize_occurs_free;
  rewrite <- ?name_in_fundefs_ctx_ctx; eauto with Ensembles_DB.
Qed.
Corollary occurs_free_exp_ctx c e e' :
  occurs_free e \subset occurs_free e' ->
  occurs_free (ctx.app_ctx_f c e) \subset occurs_free (ctx.app_ctx_f c e').
Proof. apply occurs_free_ctx_mut. Qed.
Corollary occurs_free_fundefs_ctx B e e' :
  occurs_free e \subset occurs_free e' ->
  occurs_free_fundefs (ctx.app_f_ctx_f B e) \subset occurs_free_fundefs (ctx.app_f_ctx_f B e').
Proof. apply occurs_free_ctx_mut. Qed.

Fixpoint rename_all_preserves_bound σ e {struct e} :
  bound_var ![rename_all' σ e] <--> bound_var ![e].
Proof.
  destruct e; unbox_newtypes; cbn; collapse_primes; repeat normalize_bound_var;
  rewrite ?rename_all_preserves_bound; eauto with Ensembles_DB.
  - rewrite bound_var_Ecase; collapse_primes.
    induction ces as [|[c e] ces IHces]; unbox_newtypes; cbn; repeat normalize_bound_var; eauto with Ensembles_DB.
  - enough (Hfds : bound_var_fundefs ![rename_all_fds' σ fds] <--> bound_var_fundefs ![fds]) by now rewrite Hfds.
    clear e; induction fds as [|[f ft xs e] fds IHfds]; unbox_newtypes; cbn;
      repeat normalize_bound_var; collapse_primes; eauto with Ensembles_DB.
Qed.

Definition well_scoped e := unique_bindings ![e] /\ Disjoint _ (bound_var ![e]) (occurs_free ![e]).
Definition well_scoped_fds fds :=
  unique_bindings_fundefs ![fds] /\ Disjoint _ (bound_var_fundefs ![fds]) (occurs_free_fundefs ![fds]).

Lemma stem_not_free c e :
  well_scoped [ctx.app_ctx_f c e]! ->
  Disjoint _ (bound_stem_ctx c) (occurs_free (ctx.app_ctx_f c e)).
Proof.
  intros [_ Hdis]; rewrite !isoBAB in Hdis.
  eapply Disjoint_Included_l; [|eassumption].
  rewrite bound_var_app_ctx, bound_var_stem_or_not_stem; eauto with Ensembles_DB.
Qed.

(* TODO: Move to Ensembles_util.v *)
Lemma Disjoint_Setminus_bal : forall {A} (S1 S2 S3 : Ensemble A),
  Disjoint _ (S1 \\ S3) (S2 \\ S3) ->
  Disjoint _ (S1 \\ S3) S2.
Proof.
  clear; intros A S1 S2 S3 [Hdis]; constructor; intros arb.
  intros [arb' [HS1 HS3] HS2]; clear arb.
  apply (Hdis arb'); constructor; constructor; auto.
Qed.

(* well_scoped(C[e]) ⟹ (BV(e) # vars(C)) ∧ (FV(e) ⊆ BVstem(C) ∪ FV(C[e]) *)
Lemma well_scoped_mut' :
  (forall (c : ctx.exp_ctx) (e : cps.exp),
    well_scoped [ctx.app_ctx_f c e]! ->
    Disjoint _ (bound_var e) (used_c [c]!) /\
    occurs_free e \subset bound_stem_ctx c :|: occurs_free (ctx.app_ctx_f c e)) /\
  (forall (B : ctx.fundefs_ctx) (e : cps.exp),
    well_scoped_fds [ctx.app_f_ctx_f B e]! ->
    Disjoint _ (bound_var e) (used_c [B]!) /\
    occurs_free e \subset name_in_fundefs (ctx.app_f_ctx_f B e)
                :|: bound_stem_fundefs_ctx B :|: occurs_free_fundefs (ctx.app_f_ctx_f B e)).
Proof.
  apply ctx.exp_fundefs_ctx_mutual_ind; unfold well_scoped.
  - cbn; normalize_roundtrips; intros; eauto with Ensembles_DB.
  - intros x c ys C IH e [Huniq Hdis]; specialize (IH e); rewrite !isoBAB in IH, Huniq, Hdis.
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free
                         || normalize_sets || normalize_roundtrips); intros Hdis.
    destruct IH as [IHdis IHfv]; [split; auto|split].
    { apply Disjoint_Union in Hdis; destruct Hdis as [Hdis1 Hdis2].
      apply Disjoint_commut, Disjoint_Union in Hdis2; destruct Hdis2 as [Hdis2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdis2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdis].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x t n y C IH e [Huniq Hdisj]; specialize (IH e); rewrite !isoBAB in IH, Huniq, Hdisj.
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      apply Disjoint_commut, Disjoint_Union in Hdisj2; destruct Hdisj2 as [Hdisj2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdisj2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x f ft ys C IH e [Huniq Hdisj]; specialize (IH e); rewrite !isoBAB in IH, Huniq, Hdisj.
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      apply Disjoint_commut, Disjoint_Union in Hdisj2; destruct Hdisj2 as [Hdisj2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdisj2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc, (Union_assoc [set x]), (Union_commut [set x]),
        <- Union_assoc.
      do 2 apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x p ys C IH e [Huniq Hdisj]; specialize (IH e); rewrite !isoBAB in IH, Huniq, Hdisj.
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      apply Disjoint_commut, Disjoint_Union in Hdisj2; destruct Hdisj2 as [Hdisj2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdisj2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x ces1 ct C IH ces2 e [Huniq Hdisj]; specialize (IH e); rewrite !isoBAB in IH, Huniq, Hdisj.
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { admit. }
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj2]]; eauto with Ensembles_DB. }
    + admit.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|]; eauto with Ensembles_DB.
  - intros fds C IH e [Huniq Hdisj]; specialize (IH e); rewrite !isoBAB in IH, Huniq, Hdisj.
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { now inv Huniq. }
    { inv Huniq. eapply Disjoint_Included_r;
                   [apply Included_Union_Setminus with (s2 := name_in_fundefs fds); eauto with Decidable_DB|].
      apply Union_Disjoint_r;
        [eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]|]; eauto with Ensembles_DB.
      eapply Disjoint_Included_r; [apply name_in_fundefs_bound_var_fundefs|]; auto. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * inv Huniq. rewrite bound_var_app_ctx in H3; eauto with Ensembles_DB.
      * eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
        rewrite bound_var_app_ctx; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      rewrite (Union_commut (name_in_fundefs _)), <- Union_assoc.
      rewrite (Union_assoc (name_in_fundefs _)), (Union_commut (name_in_fundefs _)), <- Union_assoc.
      do 2 apply Included_Union_preserv_r; rewrite Union_commut.
      apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros C IH e1 e [Huniq Hdisj]; specialize (IH e); rewrite !isoBAB in Huniq, Hdisj.
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free || normalize_roundtrips
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { cbn; normalize_roundtrips; now inv Huniq. }
    { cbn; normalize_roundtrips.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * inv Huniq. rewrite bound_var_app_f_ctx in H3; eauto with Ensembles_DB.
      * rewrite bound_var_app_f_ctx in *.
        (* FV(e1) ⊆ (FV(e1)\names(C[e])) ∪ names(C[e])
             BV(e) # (FV(e1)\names(C[e])) by Hdisj
             BV(e) # names(C[e]) by UB(Efun (C[e]) e1) *)
        admit.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      apply Union_Included; eauto with Ensembles_DB.
      rewrite name_in_fundefs_ctx_ctx; eauto with Ensembles_DB.
  - intros f ft xs C IH fds e [Huniq Hdisj]. specialize (IH e); cbn in *; normalize_roundtrips.
    rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free || normalize_roundtrips
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { now inv Huniq. }
    { inv Huniq. change (~ ?S ?x) with (~ x \in S) in *.
      erewrite <- (Setminus_Disjoint (bound_var (ctx.app_ctx_f C e)));
        [|eapply Disjoint_Included_r; [apply name_in_fundefs_bound_var_fundefs|]; apply H8].
      erewrite <- (Setminus_Disjoint (bound_var (ctx.app_ctx_f C e))); [|apply H6].
      erewrite <- (Setminus_Disjoint (bound_var (ctx.app_ctx_f C e))); [|apply Disjoint_Singleton_r, H4].
      rewrite !Setminus_Union.
      apply Disjoint_Setminus_bal.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r; [|apply Union_Disjoint_r]|apply IHdisj].
      * admit.
      * inv Huniq. change (~ ?S ?x) with (~ x \in S) in *. rewrite bound_var_app_ctx, Union_demorgan in H4.
        apply Disjoint_Singleton_In; eauto with Decidable_DB; easy.
      * inv Huniq; rewrite bound_var_app_ctx in *. now apply Disjoint_Union_r in H6.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      eapply Included_trans with (s2 :=
        (f |: FromList xs :|: name_in_fundefs fds) :|: 
        (occurs_free (ctx.app_ctx_f C e) \\ (f |: (FromList xs :|: name_in_fundefs fds)))).
      2: eauto with Ensembles_DB.
      rewrite Union_commut, <- !Union_assoc.
      apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros f ft xs e C IH e0 [Huniq Hdisj]; specialize (IH e0); rewrite !isoBAB in Hdisj, Huniq.
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free || normalize_roundtrips
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { cbn; normalize_roundtrips; now inv Huniq. }
    { inv Huniq; cbn in *; normalize_roundtrips. change (~ ?S ?x) with (~ x \in S) in *.
      erewrite <- (Setminus_Disjoint (bound_var_fundefs (ctx.app_f_ctx_f C e0)));
        [|eapply Disjoint_Included_r; [apply name_in_fundefs_bound_var_fundefs|]; apply H8].
      erewrite <- (Setminus_Disjoint (bound_var_fundefs (ctx.app_f_ctx_f C e0))); [|apply H6].
      erewrite <- (Setminus_Disjoint (bound_var_fundefs (ctx.app_f_ctx_f C e0))); [|apply Disjoint_Singleton_r, H4].
      rewrite !Setminus_Union.
      apply Disjoint_Setminus_bal.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    { cbn; normalize_roundtrips.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * inv Huniq. rewrite bound_var_app_f_ctx in H3; eauto with Ensembles_DB.
      * rewrite bound_var_app_f_ctx in *.
        (* FV(e1) ⊆ (FV(e1)\names(C[e])) ∪ names(C[e])
             BV(e) # (FV(e1)\names(C[e])) by Hdisj
             BV(e) # names(C[e]) by UB(Efun (C[e]) e1) *)
        admit.
    + normalize_bound_stem_ctx'; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      apply Union_Included; eauto with Ensembles_DB.
      rewrite name_in_fundefs_ctx_ctx; eauto with Ensembles_DB.
      apply 
      SearchAbout Setminus iff.
      apply Union_Included; eauto with Ensembles_DB.
      rewrite name_in_fundefs_ctx_ctx; eauto with Ensembles_DB.

Lemma known_ctor_in_used_c {A} x c ys (C : exp_c A _) : known_ctor x c ys C -> ![x] \in used_c C.
Proof.
  SearchAbout bound_var ctx.app_ctx_f.
SearchAbout used_vars ctx.app_ctx_f.
(** Shrink rewriter *)

Definition rw_shrink' : rewriter exp_univ_exp shrink_step (@D_rename) (@R_shrink) (@S_shrink).
Proof.
  mk_rw; try lazymatch goal with |- ExtraVars _ -> _ => clear | |- ConstrDelay _ -> _ => clear end.
  - (* Case folding *) intros _ R C x ces d r s success failure.
    destruct r as [ρ Hρ] eqn:Hr, d as [σ Hσ] eqn:Hd; unfold delayD, Delayed_D_rename in *.
    pose (x0 := apply_r' σ x); specialize success with (x0 := x0).
    destruct (M.get ![x0] ρ) as [[c ys]|] eqn:Hctor; [|cond_failure].
    pose (Hρ' := Hρ x0 c ys Hctor); specialize success with (c := c) (ys := ys).
    destruct (find_case c ces) as [e|] eqn:Hfind; [|cond_failure]; apply find_case_spec in Hfind.
    specialize success with (e := e) (e0 := @rename exp_univ_exp σ e).
    specialize success with (ces0 := @rename exp_univ_list_prod_ctor_tag_exp σ ces).
    cond_success success; unshelve eapply success.
    + exists σ; clear - Hfind Hσ; destruct x as [x]; cbn in *; destruct Hσ as [Hdom Hran].
      rewrite bound_var_Ecase in *.
      assert (In (c, e) ces). { 
        destruct Hfind as [ces1 [ces2 [Hnotin Hces]]]; subst ces.
        apply in_or_app; right; now left. }
      split; (eapply Disjoint_Included_r; [eapply In_ces_bound; eauto|]; eauto).
    + split; auto.
      destruct Hfind as [ces1 [ces2 [Hnotin Hces]]].
      assert (Hfind' : In (c, e) ces) by (subst ces; apply in_or_app; right; now left).
      apply in_map with (f := @rename exp_univ_prod_ctor_tag_exp σ) in Hfind'; now cbn in Hfind'.
    + reflexivity. + reflexivity. + exact r.
    + destruct s as [δ Hs] eqn:Hs_eq; unshelve eexists; [|split; [|split]].
      * (* Update counts *) exact (census_case_pred σ c ces (census_var pred_upd σ x δ)).
      * (* UB(C[σ(Ecase x ces)]) ==> UB(C[σ(e)]) because (c, e) ∈ ces *)
        admit.
      * (* BV(C[σ(e)]) ⊆ BV(C[σ(Ecase x ces)]) and ditto for FV
            And already have BV(C[σ(Ecase x es)]) # FV(C[σ(Ecase x ces)]) *)
        admit.
      * intros arb; rewrite count_ctx_app; unfold count, rename.
        destruct Hfind as [ces1 [ces2 [Hnotin Hces]]].
        eapply census_case_pred_spec; eauto.
        rewrite census_var_pred_corresp.
        destruct Hs as [Huniq [Hdis Hδ]]; rewrite Hδ, count_ctx_app; cbn; collapse_primes; lia.
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
      * (* Update counts *)
        exact (census_var_pred σ x (census_subst y' y δ)).
      * (* UB(C[(σe)[y'/y]])
              ⟸ UB(C[σe]) (BV((σe)[y'/y]) = BV(σe) by rename_all_preserves_bound)
              ⟸ UB(C[Eproj y t n (σx) (σe)])
              ⟸ UB(C[σ(Eproj y t n x e)]) *)
        admit.
      * (* BV(C[(σe)[y'/y]])
             = BV(C) ∪ BV((σe)[y'/y]) (bound_var_app_ctx)
             = BV(C) ∪ BV(σe) (rename_all_preserves_bound)
             ⊆ BV(C) ∪ BV(σ(Eproj y t n x e))
           FV(C[(σe)[y'/y]]) ⊆ FV(C[σ(proj y t n x e)])
             y' ∈ vars(C)
               FV(C) ⊆ FV(C[σ(Eproj y t n x e)])
               BV(C) = BVstem(C) ∪ BVnotstem(C)
             FV((σe)[y'/y]) ⊆ FV(σe) ∪ {y'}
             = FV(C[(σe)[y'/y]]) (TODO: use occurs_free_exp_ctx)
             = FV(C) ∪ (FV((σe)[y'/y]) \ BVstem(C))
             = FV(C) ∪ (((FV(σe) \ {y}) ∪ {y'}) \ BVstem(C))
             = FV(C) ∪ (FV(σe) \ {y} \ BVstem(C)) ∪ ({y'} \ BVstem(C))
             ⊆ FV(C) ∪ (FV(σe) \ {y} \ BVstem(C)) ∪ FV(C) (by lemma)
             ⊆ FV(C) ∪ (({σx} ∪ (FV(σe) \ {y})) \ BVstem(C))
             = FV(C) ∪ (FV(Eproj y t n (σx) (σe)) \ BVstem(C))
             = FV(C) ∪ (FV(σ(Eproj y t n x e)) \ BVstem(C))
             = FV(C[σ(Eproj y t n x e)])
           Lemma:
             (x ↦ (c, ys)) ∈ C ⟹ y ∈ ys ⟹ {y} ⊆ FV(C) ∪ BVstem(C) *)
        admit.
      * intros arb; rewrite count_ctx_app, census_var_pred_corresp.
        assert (Hneq : y <> y'). {
          admit. (* Follows from lemma that y' ⊆ FV(C) ∪ BVstem(C) and UB + FV#BV *) }
        assert (Hy_notin_C : count_ctx y C = 0). { 
          admit. (* Need lemma: UB(C[e]) ∧ (FV(C[e]) # BV(C[e])) ⟹ BV(e) # vars(C) *) }
        unfold count, Rec, rename.
        destruct Hs as [Huniq [Hdis Hδ]].
        destruct (var_eq_dec arb y); [|destruct (var_eq_dec arb y')].
        -- subst arb; rewrite census_subst_dom, count_exp_subst_dom, Hy_notin_C by auto; lia.
        -- subst arb; rewrite census_subst_ran, count_exp_subst_ran by auto.
           rewrite !Hδ, !count_ctx_app, Hy_notin_C; cbn; collapse_primes.
           assert (Hyx : y <> apply_r' σ x). {
             (* σ(x) occurs free, y occurs bound *)
             (* TODO: lemma:
                  UB(C[e]) ∧ (FV(C[e]) # BV(C[e])) ⟹
                  UB(e) ∧ (FV(e) # BV(e)) *)
             admit. }
           rewrite count_var_neq at 1 by auto; lia.
        -- rewrite census_subst_neither, count_exp_subst_neither, Hδ, count_ctx_app by auto.
           cbn; collapse_primes; lia.
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
