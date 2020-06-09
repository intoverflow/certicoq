(*
Require Import Common.compM Common.Pipeline_utils L6.cps.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String.
Import ListNotations.
Require Import identifiers.
Require Import L6.state L6.freshen L6.cps_util L6.cps_show L6.ctx L6.uncurry L6.shrink_cps.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Coq.Program.Wf.
Require Import Program.
(* Require Import Template.monad_utils. *)
Require Import Coq.Structures.OrdersEx.

Import MonadNotation.
Open Scope monad_scope. *)

Require Import Coq.Sets.Ensembles Coq.ZArith.ZArith.
Require Import L6.Ensembles_util L6.map_util.
Require Import L6.state L6.alpha_conv L6.identifiers L6.functions L6.shrink_cps.
Require Import L6.Prototype.
Require Import L6.cps_proto L6.proto_util.

Require Import Lia.

Require Import Coq.Lists.List.
Import ListNotations.

(** * Inlining heuristics *)

(* Rather than parameterizing by [St] as in inline.v, the heuristic is
   represented as a record of closures (like an OOP class). This is to allow the heuristic to
   stay in Set, which is necessary to get along with the MetaCoq in Prototype.v.

   We also don't pass in the renaming [r_map]. *)
CoInductive InlineHeuristic : Set := {
  (* Update inlining decision and functions declaration.
     First state is used for the body of the program, second for the function definitions *)
  update_funDef : fundefs -> InlineHeuristic * InlineHeuristic;
  (* Update inlining decisions when converting a function within a bundle *)
  update_inFun : var -> fun_tag -> list var -> exp -> InlineHeuristic;
  (* Return inlining decision on function application *)
  decide_App : var -> fun_tag -> list var -> bool;
  (* Update heuristic on function application *)
  update_App : var -> fun_tag -> list var -> InlineHeuristic;
  (* Return inlining decision on let bound function application *)
  decide_letApp : var -> fun_tag -> list var -> bool;
  (* Update heuristic on let bound function application *)
  update_letApp : var -> fun_tag -> list var -> InlineHeuristic }.

CoFixpoint CombineInlineHeuristic (deci: bool -> bool -> bool) (IH1 IH2 : InlineHeuristic) : InlineHeuristic := {| 
  update_funDef fds :=
    let (IH11, IH12) := IH1.(update_funDef) fds in
    let (IH21, IH22) := IH2.(update_funDef) fds in
    (CombineInlineHeuristic deci IH11 IH21, CombineInlineHeuristic deci IH12 IH22);
  update_inFun f ft xs e :=
    let IH1' := IH1.(update_inFun) f ft xs e in
    let IH2' := IH2.(update_inFun) f ft xs e in
    CombineInlineHeuristic deci IH1' IH2';
  decide_App f ft ys :=
    let b1 := IH1.(decide_App) f ft ys in
    let b2 := IH2.(decide_App) f ft ys in
    deci b1 b2;
  update_App f ft ys :=
    let IH1' := IH1.(update_App) f ft ys in
    let IH2' := IH2.(update_App) f ft ys in
    CombineInlineHeuristic deci IH1' IH2';
  decide_letApp f ft ys :=
    let b1 := IH1.(decide_App) f ft ys in
    let b2 := IH2.(decide_App) f ft ys in
    deci b1 b2;
  update_letApp f ft ys :=
    let IH1' := IH1.(update_App) f ft ys in
    let IH2' := IH2.(update_App) f ft ys in
    CombineInlineHeuristic deci IH1' IH2' |}.

Definition PostUncurryIH : M.t nat -> InlineHeuristic :=
  cofix IH s := {|
    (* at the start, uncurry shell (i.e. not the outermost) all maps to 1 *)
    (* 0 -> Do not inline, 1 -> uncurried function, 2 -> continuation of uncurried function *)
    update_funDef fds := let IH' := IH s in (IH', IH');
    update_inFun f ft xs e := IH s;
    decide_App f ft ys :=
      match (M.get ![f] s, ys) with
      | (Some 1, _::_) => true
      | (Some 2, _) => true
      | _ => false
      end;
    update_App f ft ys :=
      match (M.get ![f] s, ys) with
      | (Some 1, k::ys') => IH (M.set ![f] 0 (M.set ![k] 2 s))
      | _ => IH s
      end;
    decide_letApp f t ys := false;
    update_letApp f t ys := IH s |}.

Definition InlineSmallIH (bound : nat) : M.t bool -> InlineHeuristic :=
  cofix IH s := {|
    (* Add small, [todo: non-recursive] functions to s *)
    update_funDef fds :=
      let fix upd fds s := 
        match fds with
        | Ffun f ft xs e :: fdc' =>
          if (Init.Nat.ltb (term_size ![e]) bound)
          then upd fdc' (M.set ![f] true s)
          else upd fdc' s
        | Fnil => s
        end
      in
      let IH' := IH (upd fds s) in
      (IH', IH');
    update_inFun f ft xs e := IH (M.remove ![f] s);
    decide_App f ft ys :=
      match M.get ![f] s with
      | Some true => true
      | _ => false
      end;
    update_App f ft ys :=
      match M.get ![f] s with
      | Some true => IH (M.remove ![f] s)
      | _ => IH s
      end;
    decide_letApp f ft ys := false;
    update_letApp f ft ys := IH s |}.

Open Scope positive.

Fixpoint find_uncurried (fds : fundefs) (s:M.t bool) : M.t bool :=
  match fds with
  | Ffun f t (k::xs) (Efun [Ffun h _ _ _] (Eapp k' _ [h'])) :: fds' =>
    let s' := M.set ![f] true s in
        (* if andb (h =? h') (k =? k') then M.set f true s else s in *)
    find_uncurried fds' s'
  | _ => s
  end.

Definition InlineUncurried : M.t bool -> InlineHeuristic :=
  cofix IH s := {|
    update_funDef fds := let IH' := IH (find_uncurried fds s) in (IH', IH');
    update_inFun f ft xs e := IH (M.remove ![f] s);
    decide_App f ft ys :=
      match M.get ![f] s with
      | Some true => true
      | _ => false
      end;
    update_App f ft ys := IH s;
    decide_letApp f ft ys := false;
    update_letApp f ft ys := IH s |}.

Fixpoint find_uncurried_pats_anf (fds : fundefs) (s:M.t bool) : M.t bool :=
  match fds with
  | Ffun f t xs (Efun [Ffun h ht ys e] (Ehalt h')) :: fds' =>
    let s' :=
      if ((![h] =? ![h']) && negb (occurs_in_exp ![f] ![Efun [Ffun h ht ys e] (Ehalt h')]))%bool
      then M.set ![f] true s else s
    in
    find_uncurried fds' s'
  | Ffun f t xs (Eapp f' t' xs') :: fds' =>
    let s' := if (occurs_in_exp ![f] ![Eapp f' t' xs']) then s else M.set ![f] true s in
    find_uncurried fds' s'
  | _ => s
  end.

(* Inlines functions based on patterns found in the code *)
Definition InineUncurriedPatsAnf : M.t bool -> InlineHeuristic :=
  cofix IH s := {|
    update_funDef fds :=
      let IH' := IH (find_uncurried fds s) in
      (IH', IH');
    update_inFun f ft xs e := IH (M.remove ![f] s);
    decide_App f ft ys :=
      match M.get ![f] s with
      | Some true => true
      | _ => false
      end;
    update_App f ft ys := IH s;
    decide_letApp f ft ys :=
      match M.get ![f] s with
      | Some true => true
      | _ => false
      end;
    update_letApp f ft ys := IH s |}.

Definition InlinedUncurriedMarkedAnf : M.t nat -> InlineHeuristic :=
  cofix IH s := {|
    (* at the start, uncurry shell (i.e. not the outermost) all maps to 1 *)
    (* 0 -> Do not inline, 1 -> uncurried function, 2 -> continuation of uncurried function *)
    update_funDef fds := let IH' := IH s in (IH', IH');
    update_inFun f ft xs e := IH s;
    decide_App f ft ys :=
      match M.get ![f] s with
      | Some 1%nat => true
      | Some 2%nat => true
      | _ => false
      end;
    update_App f ft ys :=
      match M.get ![f] s with
      | Some 1%nat => IH (M.set ![f] 0%nat s)
      | Some 2%nat => IH (M.set ![f] 0%nat s)
      | _ => IH s
      end;
    decide_letApp f ft ys :=
      match M.get ![f] s with
      | Some 1%nat => true
      | Some 2%nat => true
      | _ => false
      end;
    update_letApp f ft ys := IH s |}.

Definition InlineSmallOrUncurried (bound : nat) (s1 : M.t bool) (s2 : M.t nat) : InlineHeuristic :=
  CombineInlineHeuristic orb (InlineSmallIH bound s1) (PostUncurryIH s2).

(** * Freshening + substituting formals for actuals *)

Definition r_map : Set := M.tree cps.var.

Definition fun_name : fundef -> var := fun '(Ffun f _ _ _) => f.

Definition freshen_fd' (freshen_exp : positive -> r_map -> exp -> positive * exp)
           (next : positive) (σ : r_map) (fd : fundef) : positive * fundef :=
  let 'Ffun f ft xs e := fd in
  let f := [apply_r σ ![f]]! in
  let '(next, xs') := gensyms next xs in
  match set_lists ![xs] ![xs'] σ with
  | Some σ =>
    let '(next, e) := freshen_exp next σ e in
    (next, Ffun f ft xs' e)
  | None => (* unreachable *) (next, inhabitant)
  end.

Definition freshen_fds' (freshen_exp : positive -> r_map -> exp -> positive * exp)
  : positive -> r_map -> list fundef -> positive * list fundef :=
  fix go next σ fds :=
    match fds with
    | [] => (next, [])
    | fd :: fds =>
      let '(next, fd) := freshen_fd' freshen_exp next σ fd in
      let '(next, fds) := go next σ fds in
      (next, fd :: fds)
    end.

Definition freshen_ce' (freshen_exp : positive -> r_map -> exp -> positive * exp)
           (next : positive) (σ : r_map) : ctor_tag * exp -> positive * (ctor_tag * exp) :=
  fun '(c, e) => let '(next, e) := freshen_exp next σ e in (next, (c, e)).

Definition freshen_ces' (freshen_exp : positive -> r_map -> exp -> positive * exp)
  : positive -> r_map -> list (ctor_tag * exp) -> positive * list (ctor_tag * exp) :=
  fix go next σ ces :=
    match ces with
    | [] => (next, [])
    | ce :: ces =>
      let '(next, ce) := freshen_ce' freshen_exp next σ ce in
      let '(next, ces) := go next σ ces in
      (next, ce :: ces)
    end.

Fixpoint freshen_exp (next : positive) (σ : r_map) (e : exp) {struct e} : positive * exp.
Proof.
- refine (
  match e with
  | Econstr x c ys e =>
    let '(next, x') := gensym next in
    let ys := [apply_r_list σ ![ys]]! in
    let '(next, e) := freshen_exp next (M.set ![x] ![x'] σ) e in
    (next, Econstr x' c ys e)
  | Ecase x ces =>
    let x := [apply_r σ ![x]]! in
    let '(next, ces) := freshen_ces' freshen_exp next σ ces in
    (next, Ecase x ces)
  | Eproj x c n y e =>
    let '(next, x') := gensym next in
    let y := [apply_r σ ![y]]! in
    let '(next, e) := freshen_exp next (M.set ![x] ![x'] σ) e in
    (next, Eproj x' c n y e)
  | Eletapp x f ft ys e =>
    let '(next, x') := gensym next in
    let f := [apply_r σ ![f]]! in
    let ys := [apply_r_list σ ![ys]]! in
    let '(next, e) := freshen_exp next (M.set ![x] ![x'] σ) e in
    (next, Eletapp x' f ft ys e)
  | Efun fds e =>
    let fs := map fun_name fds in
    let '(next, fs') := gensyms next fs in
    match set_lists ![fs] ![fs'] σ with
    | Some σ =>
      let '(next, fds) := freshen_fds' freshen_exp next σ fds in
      let '(next, e) := freshen_exp next σ e in
      (next, Efun fds e)
    | None => (* unreachable *) (next, Efun [] e)
    end
  | Eapp f ft xs =>
    let f := [apply_r σ ![f]]! in
    let xs := [apply_r_list σ ![xs]]! in
    (next, Eapp f ft xs)
  | Eprim x p ys e =>
    let '(next, x') := gensym next in
    let ys := [apply_r_list σ ![ys]]! in 
    let '(next, e) := freshen_exp next (M.set ![x] ![x'] σ) e in
    (next, Eprim x' p ys e)
  | Ehalt x =>
    let x := [apply_r σ ![x]]! in
    (next, Ehalt x)
  end).
Defined.
Definition freshen_fd := freshen_fd' freshen_exp.
Definition freshen_fds := freshen_fds' freshen_exp.
Definition freshen_ce := freshen_ce' freshen_exp.
Definition freshen_ces := freshen_ces' freshen_exp.

Lemma Union_fresher_than x S1 S2 :
  fresher_than x (S1 :|: S2) -> fresher_than x S1 /\ fresher_than x S2.
Proof. split; intros y Hy; now apply H. Qed.

Lemma fold_used_vars e : occurs_free e :|: bound_var e <--> used_vars e.
Proof. rewrite Union_commut; reflexivity. Qed.

Lemma apply_r_set x y σ : f_eq ((apply_r σ) {x ~> y}) (apply_r (M.set x y σ)).
Proof.
  unfold f_eq, extend, apply_r; cbn; intros x'.
  destruct (Pos.eq_dec x x'); [subst|].
  - now rewrite Coqlib.peq_true, M.gss.
  - now rewrite Coqlib.peq_false, M.gso.
Qed.

Lemma apply_r_set_lists xs ys σ σ' :
  set_lists xs ys σ = Some σ' ->
  f_eq ((apply_r σ) <{xs ~> ys}>) (apply_r σ').
Proof.
  revert ys σ σ'; induction xs as [|x xs IHxs]; intros ys σ σ'; destruct ys; cbn; try congruence.
  destruct (set_lists xs ys σ) eqn:Hrec; try congruence; inversion 1.
  now rewrite (IHxs _ _ _ Hrec), apply_r_set.
Qed.

Lemma fresher_than_Singleton x y : x > y -> fresher_than x [set y].
Proof. intros Hxy z Hz; now inv Hz. Qed.

Lemma fresher_than_FromList x ys : (forall y, In y ys -> x > y) <-> fresher_than x (FromList ys).
Proof. reflexivity. Qed.

Lemma fresher_than_map (f : cps.var -> cps.var) x ys :
  (forall y, In y ys -> x > f y) -> fresher_than x (FromList (map f ys)).
Proof.
  unfold fresher_than, FromList, Ensembles.In.
  intros Hys y Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [y' [Hy' Hin]]; subst; now apply Hys.
Qed.

Lemma fresher_than_tonics S T x y :
  x >= y ->
  S \subset T ->
  fresher_than y T ->
  fresher_than x S.
Proof.
  now (intros; eapply fresher_than_monotonic;[|eapply fresher_than_antimon;[|eassumption]]; [lia|]).
Qed.

Lemma Alpha_conv_cons x1 x2 e1 e2 c1 c2 ces1 ces2 σ :
  c1 = c2 ->
  Alpha_conv e1 e2 σ ->
  Alpha_conv (cps.Ecase x1 ces1) (cps.Ecase x2 ces2) σ ->
  Alpha_conv (cps.Ecase x1 ((c1, e1) :: ces1)) (cps.Ecase x2 ((c2, e2) :: ces2)) σ.
Proof. intros Hc He Hces; inv Hces; constructor; auto. Qed.

Lemma set_lists_None_length {A} ρ xs (vs : list A) :
  set_lists xs vs ρ = None -> length xs <> length vs.
Proof.
  revert vs; induction xs as [|x xs IHxs]; destruct vs; cbn; try congruence.
  destruct (set_lists xs vs ρ) eqn:Heq; try congruence.
  (assert (length xs <> length vs) by now apply IHxs); lia.
Qed.

(* TODO: move to ensembles_util *)

Lemma Disjoint_commut {A} S1 S2 : Disjoint A S1 S2 -> Disjoint A S2 S1.
Proof. eauto with Ensembles_DB. Qed.

Lemma Disjoint_Union {A} S1 S2 S3 :
  Disjoint A S1 (S2 :|: S3) -> Disjoint A S1 S2 /\ Disjoint A S1 S3.
Proof. eauto with Ensembles_DB. Qed.

Local Ltac normalize_images :=
  repeat (repeat normalize_used_vars;
    repeat rewrite used_vars_Eletapp in *;
    repeat (rewrite image_Union || rewrite <- FromList_map_image_FromList);
    repeat match goal with
    | H : fresher_than _ (_ :|: _) |- _ =>
      apply Union_fresher_than in H;
      destruct H
    end;
    repeat match goal with
    | H : context [image _ [set _]] |- _ => rewrite image_Singleton in H
    | H : context [image _ (_ :|: _)] |- _ => rewrite image_Union in H
    | H : context [image _ (FromList _)] |- _ => rewrite <- FromList_map_image_FromList in H
    end;
    repeat match goal with 
    | H : Disjoint _ (_ :|: _) _ |- _ => apply Disjoint_commut in H
    | H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H; destruct H
    end;
    repeat normalize_used_vars).

Fixpoint set_lists_In_corresp {A} x xs (ys : list A) ρ ρ' {struct xs} :
  set_lists xs ys ρ = Some ρ' ->
  In x xs -> exists y, M.get x ρ' = Some y /\ In y ys.
Proof.
  destruct xs as [|x' xs'], ys as [|y' ys']; cbn; try easy.
  destruct (set_lists xs' ys' ρ) as [ρ0|] eqn:Hρ; [|congruence].
  intros Heq; inv Heq; intros Hin.
  destruct (Pos.eq_dec x x'); [subst|].
  - rewrite M.gss; now eexists.
  - rewrite M.gso by auto; destruct Hin; [easy|].
    specialize (set_lists_In_corresp _ x xs' ys' ρ ρ0).
    destruct set_lists_In_corresp as [y [Hy Hin]]; auto.
    now eexists.
Qed.

Fixpoint set_NoDup_inj xs xs' σ σ' {struct xs} :
  NoDup xs' ->
  set_lists xs xs' σ = Some σ' ->
  injective_subdomain (FromList xs) (apply_r σ').
Proof.
  destruct xs as [|x xs], xs' as [|x' xs']; unbox_newtypes; cbn; try congruence.
  - intros; rewrite FromList_nil; apply injective_subdomain_Empty_set.
  - intros Hdup.
    destruct (set_lists _ _ _) as [σ0|] eqn:Hσ; [|congruence]; intros Heq; inv Heq.
    intros y y' Hy Hy' Heq.
    destruct (Pos.eq_dec y x).
    + subst; unfold apply_r at 1 in Heq; rewrite M.gss in Heq.
      destruct (Pos.eq_dec x y'); [auto|].
      unfold apply_r in Heq; rewrite M.gso in Heq by auto.
      destruct Hy' as [?|Hy']; [easy|].
      edestruct (set_lists_In_corresp y' xs _ σ σ0 Hσ) as [v [Hv Hin]]; auto.
      rewrite Hv in Heq; subst; now inv Hdup.
    + unfold apply_r at 1 in Heq; rewrite M.gso in Heq by auto.
      match type of Heq with ?lhs = _ => change lhs with (apply_r σ0 y) in Heq end.
      destruct (Pos.eq_dec x y'); [subst|].
      * unfold apply_r at 2 in Heq; rewrite M.gss in Heq.
        destruct Hy as [?|Hy]; [easy|].
        edestruct (set_lists_In_corresp y xs _ σ σ0 Hσ) as [v [Hv Hin]]; auto.
        unfold apply_r in Heq; rewrite Hv in Heq; now inv Hdup.
      * destruct Hy; [easy|]; destruct Hy'; [easy|].
        unfold apply_r at 2 in Heq; rewrite M.gso in Heq by auto.
        match type of Heq with _ = ?rhs => change rhs with (apply_r σ0 y') in Heq end.
        inv Hdup; eapply (set_NoDup_inj xs xs' σ σ0); auto.
Qed.

Lemma NoDup_var (xs : list var) : NoDup xs -> NoDup ![xs].
Proof.
  induction xs; [constructor|unbox_newtypes; cbn in *; intros HND; inv HND].
  constructor; auto.
  intros Hin; apply in_map with (f := mk_var) in Hin; now normalize_roundtrips.
Qed.

Fixpoint set_gensyms_inj next next' xs xs' σ σ' {struct xs} :
  fresher_than next (FromList ![xs]) ->
  (next', xs') = gensyms next xs ->
  set_lists ![xs] ![xs'] σ = Some σ' ->
  construct_lst_injection (apply_r σ) ![xs] ![xs'] (apply_r σ').
Proof.
  destruct xs as [|x xs], xs' as [|x' xs']; unbox_newtypes; cbn; try congruence.
  - intros Hfresh Heq1 Heq2; inv Heq1; inv Heq2; constructor.
  - destruct (gensyms (next + 1) xs) as [next0 xs0] eqn:Hgen; symmetry in Hgen.
    intros Hfresh Heq; inv Heq.
    destruct (set_lists _ _ _) as [σ0|] eqn:Hσ; [|congruence]; intros Heq; inv Heq.
    assert (Heq : (apply_r (@map_util.M.set cps.M.elt x next σ0)) = (apply_r σ0) {x ~> next}). {
      apply FunctionalExtensionality.functional_extensionality.
      intros; now rewrite apply_r_set. }
    rewrite Heq; constructor.
    + normalize_sets; normalize_images.
      specialize (set_gensyms_inj (next + 1) next0 xs xs0 σ σ0).
      eapply set_gensyms_inj; auto; eapply fresher_than_monotonic; eauto; lia.
    + unfold cps.var in *; rewrite <- Heq.
      apply (set_NoDup_inj (x :: strip_vars xs) (next :: strip_vars xs0) σ); [|cbn; now rewrite Hσ].
      edestruct @gensyms_spec as [[? Hdup] [? ?]]; try exact Hgen;
        [eapply fresher_than_monotonic; [|eassumption]; lia|].
      constructor; auto; [|now apply NoDup_var].
      intros Hin.
      enough (![mk_var next] >= next + 1) by (cbn in *; lia).
      eapply gensyms_increasing'; eauto.
      apply in_map with (f := mk_var) in Hin; now normalize_roundtrips.
Qed.

(* TODO: delete this (it's copied from proto_util.v) *)
Ltac show_Disjoint arb Harbx Harby :=
  let Harb := fresh "Harb" in
  constructor; intros arb Harb; unfold Ensembles.In in Harb;
  destruct Harb as [arb Harbx Harby].
  
Fixpoint freshen_exp_spec next next' σ e e' {struct e} :
  fresher_than next (used_vars ![e] :|: image (apply_r σ) (used_vars ![e])) ->
  (next', e') = freshen_exp next σ e ->
  next' >= next /\
  Alpha_conv ![e] ![e'] (apply_r σ) /\
  fresher_than next' (used_vars ![e] :|: used_vars ![e']).
Proof.
  destruct e; unbox_newtypes; cbn in *;
  repeat match goal with
  | |- context [let '(_, _) := ?f ?e in _] =>
    let next' := fresh "next" with e' := fresh "e" with He := fresh "He" in
    destruct (f e) as [next' e'] eqn:He; symmetry in He
  end; intros Hfresh Heq; repeat match goal with H : (_, _) = (_, _) |- _ => inv H end;
  cbn; normalize_roundtrips.
  Local Ltac solve_easy :=
    solve [match goal with
    | H : fresher_than _ ?S |- fresher_than _ ?S =>
      eapply fresher_than_monotonic; [|exact H]; lia
    | |- fresher_than _ [set _] => eapply fresher_than_Singleton; lia
    | H : fresher_than ?x (image _ (used_vars ?e))
      |- ~ Ensembles.In _ (image _ (occurs_free ?e)) ?x =>
      apply fresher_than_not_In; eapply fresher_than_tonics;
      try exact H; [lia|]; eauto with Ensembles_DB
    | H : fresher_than ?x (used_vars ?e) |- ~ Ensembles.In _ (bound_var ?e) ?x =>
      apply fresher_than_not_In; eapply fresher_than_tonics;
      try exact H; [lia|]; eauto with Ensembles_DB
    | H : Disjoint _ _ (image _ (used_vars ?e)) |- Disjoint _ _ (image _ (occurs_free ?e)) =>
      eapply Disjoint_Included_r; [|exact H]; eauto with Ensembles_DB
    | H : Disjoint _ _ (used_vars ?e) |- Disjoint _ _ (bound_var ?e) =>
      eapply Disjoint_Included_r; [|exact H]; eauto with Ensembles_DB
    | H : Alpha_conv ?e ?e' _ |- Alpha_conv ?e ?e' (_ {_ ~> _}) => now rewrite apply_r_set
    | |- Forall2 _ ?xs (map _ ?xs) => now apply List_util.Forall2_map_r_strong
    | |- Disjoint _ _ (_ :|: _) => apply Union_Disjoint_r; solve_easy
    | |- ~ Ensembles.In _ (_ :|: _) _ => rewrite Union_demorgan; split; solve_easy
    | |- fresher_than _ (_ :|: _) => apply fresher_than_Union; solve_easy
    | |- fresher_than _ (image (apply_r (M.set _ _ _)) _) =>
      rewrite <- apply_r_set; eapply fresher_than_antimon; [apply image_extend_Included|];
      solve_easy
    end].
  Ltac easy_case IH He :=
    edestruct IH as [Hnext [Hα Hused]]; try exact He; [normalize_images; solve_easy|];
    split; [lia|split];
    [constructor; auto; try solve_easy; normalize_images; solve_easy|normalize_images; solve_easy].
  Ltac base_case := normalize_images; split; [lia|split]; [constructor; auto|]; solve_easy.
  - easy_case freshen_exp_spec He.
  - revert ces next next0 e He Hfresh; induction ces as [|[c' e'] ces IHces]; intros next next0 e He Hfresh.
    + cbn in *; inv He; cbn; split; [lia|split]; [now constructor|normalize_images; solve_easy].
    + cbn in He.
      change (freshen_ces' freshen_exp) with freshen_ces in *.
      change (ces_of_proto' exp_of_proto) with ces_of_proto in *.
      destruct (freshen_exp next σ e') as [next1 e1] eqn:He1; symmetry in He1.
      destruct (freshen_ces next1 σ ces) as [next2 ces1] eqn:Hces1; symmetry in Hces1.
      inv He; unbox_newtypes; cbn in *.
      edestruct freshen_exp_spec as [Hnext1 [Hα1 Hused1]]; try exact He1; [normalize_images; solve_easy|].
      specialize (IHces _ _ _ Hces1); destruct IHces as [Hnext2 [Hα2 Hused2]]; [normalize_images; solve_easy|].
      split; [lia|split]; [|normalize_images; solve_easy].
      apply Alpha_conv_cons; auto.
  - easy_case freshen_exp_spec He.
  - easy_case freshen_exp_spec He.
  - assert (freshen_fds_spec : forall next next' σ fds fds',
      fresher_than next (used_vars_fundefs ![fds] :|: image (apply_r σ) (used_vars_fundefs ![fds])) ->
      (next', fds') = freshen_fds next σ fds ->
      next' >= next /\
      Alpha_conv_fundefs ![fds] ![fds'] (apply_r σ) /\
      fresher_than next' (used_vars_fundefs ![fds] :|: used_vars_fundefs ![fds'])).
    { clear - freshen_exp_spec; intros next next' σ fds; revert next next' σ.
      induction fds as [|[f ft xs e] fds IHfds]; intros next next' σ fds' Hfresh Heq.
      - cbn in *; inv Heq; cbn in *; split; [lia|split]; [constructor|].
        intros x Hx; inv Hx; repeat match goal with H : Ensembles.In _ (_ cps.Fnil) _ |- _ => inv H end.
      - destruct fds' as [|[f' ft' xs' e'] fds']; unbox_newtypes; cbn in *.
        { now repeat match goal with H : context [let '(_, _) := ?e in _] |- _ => destruct e end. }
        destruct (gensyms next xs) as [next0 xs0] eqn:Hxs0; symmetry in Hxs0.
        assert (next0 >= next) by now eapply gensyms_upper1.
        edestruct @gensyms_spec as [Hcopies [Hfresh_xs0 Hlen]]; [exact Hfresh|exact Hxs0|].
        destruct (set_lists (strip_vars xs) (strip_vars xs0) σ) as [σ'|] eqn:Hsets;
          [|apply set_lists_None_length in Hsets; unfold strip_vars in Hsets;
            now repeat rewrite map_length in Hsets].
        destruct (freshen_exp next0 σ' e) as [next1 e0] eqn:Hexp; symmetry in Hexp.
        destruct (freshen_fds next1 σ fds) as [next2 fds0] eqn:Hfds; symmetry in Hfds.
        inv Heq; cbn in *.
        edestruct freshen_exp_spec as [Hnext1 [He_α He_fresh]]; try exact Hexp.
        { normalize_images; apply fresher_than_Union; [solve_easy|].
          rewrite <- apply_r_set_lists; [|exact Hsets].
          eapply fresher_than_antimon;
            [apply image_extend_lst_Included; unfold strip_vars; now repeat rewrite map_length|].
          apply fresher_than_Union; [|solve_easy].
          eapply fresher_than_antimon; [apply image_monotonic, Setminus_Included|]; solve_easy. }
        edestruct IHfds as [Hnext2 [Hfds_α Hfds_fresh]]; try exact Hfds.
        { normalize_images; apply fresher_than_Union; solve_easy. }
        normalize_images; split; [lia|split]; [|solve_easy].
        assert (Hinj : construct_lst_injection (apply_r σ) ![xs] ![xs0] (apply_r σ')). {
          eapply set_gensyms_inj; try exact Hxs0; try exact Hsets; solve_easy. }
        apply Alpha_Fcons with (f' := apply_r σ'); auto.
        destruct Hcopies as [Hdis Hdup].
        normalize_images; solve_easy. }
    rename e0 into fds'.
    assert (next0 >= next) by now eapply gensyms_upper1.
    (edestruct @gensyms_spec as [Hcopies [Hfresh_fds Hlen]]; try exact He); try exact Hfresh.
    rewrite map_length in Hlen.
    assert (Hlen' : length (strip_vars (map fun_name fds)) = length (strip_vars fds'))
      by (unfold strip_vars; now repeat rewrite map_length).
    match type of Heq with
    | (_, _) = match ?e with _ => _ end =>
      destruct e as [σ'|] eqn:Hsets; [|now apply set_lists_None_length in Hsets]
    end.
    change (freshen_fds' freshen_exp) with freshen_fds in *.
    destruct (freshen_fds next0 σ' fds) as [next1 fds1] eqn:Hfds1; symmetry in Hfds1.
    destruct (freshen_exp next1 σ' e) as [next2 e1] eqn:He1; symmetry in He1.
    inv Heq; unbox_newtypes; cbn in *.
    normalize_images.
    admit.
  - base_case.
  - easy_case freshen_exp_spec He.
  - base_case.
Qed.

(** * Inlining as a relation *)

Definition R_misc : Set := InlineHeuristic.
Definition S_misc : Set := comp_data.

Definition update_next_var (next : cps.var) (cdata : comp_data) : comp_data := 
  let '{| next_var := _; nect_ctor_tag := c; next_ind_tag := i; next_fun_tag := f;
          cenv := e; fenv := fenv; nenv := names; log := log |} := cdata
  in
  {| next_var := next; nect_ctor_tag := c;
     next_ind_tag := i; next_fun_tag := f; cenv := e; fenv := fenv;
     nenv := names; log := log |}.

(* The function definition f(xs) = e_body (with fun tag ft) is known at C⟦e⟧ if... *)
Definition known_function {A} (f : var) (ft : fun_tag) (xs : list var) (e_body : exp)
          (C : exp_c A exp_univ_exp) (e : univD A) : Prop :=
  (* ...f was defined in an earlier bundle... *)
  (exists D fds E, C = D >:: Efun1 fds >++ E /\ List.In (Ffun f ft xs e_body) fds) \/
  (* ...or f is in a bundle and we are currently inside one of the bundle's definitions... *)
  (exists D fds1 fds2 E,
    C = D >++ ctx_of_fds fds1 >:: cons_fundef0 fds2 >++ E /\
    (List.In (Ffun f ft xs e_body) (fds1 ++ fds2))) \/
  (* ...or f is in a bundle that we are currently traversing *)
  (match A return exp_c A exp_univ_exp -> univD A -> Prop with
   | exp_univ_list_fundef => fun C fds2 => exists D fds1,
     C = D >++ ctx_of_fds fds1 /\
     List.In (Ffun f ft xs e_body) (fds1 ++ fds2)
   | _ => fun _ _ => False
   end C e).

Inductive inline_step : exp -> exp -> Prop :=
(* Update heuristic at each Efun node *)
| inline_update_Efun :
  forall (C : frames_t exp_univ_exp exp_univ_exp) fds e IH IH1 IH2,
  (IH1, IH2) = IH.(update_funDef) fds ->
  When (fun (r : R_misc) (s : S_misc) => true) ->
  inline_step
    (C ⟦ Efun fds e ⟧)
    (C ⟦ Efun (Local (fun _ => IH1) (Rec fds)) (Local (fun _ => IH2) (Rec e)) ⟧)
(* Update heuristic at each Fcons node *)
| inline_update_Fcons :
  forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f ft xs e fds,
  When (fun (r : R_misc) (s : S_misc) => true) ->
  inline_step
    (C ⟦ Ffun f ft xs e :: fds ⟧)
    (C ⟦ Ffun f ft xs (Local (fun IH => IH.(update_inFun) f ft xs e) e) :: Rec fds ⟧)
(* Inlining for CPS *)
| inline_cps :
  forall (C : frames_t exp_univ_exp exp_univ_exp) f ft (xs : list var) e e' (ys : list var)
    lhs next_x next_x',
  lhs = Eapp f ft ys ->
  known_function f ft xs e C lhs ->
  fresher_than next_x (used_vars ![C ⟦ lhs ⟧]) ->
  (next_x', e') = fresh_subst_exp next_x (set_list (combine ![xs] ![ys]) (M.empty _)) e ->
  (* Only inline if the inlining heuristic decides to *)
  When (fun (IH : R_misc) (s : S_misc) => IH.(decide_App) f ft ys) ->
  inline_step
    (C ⟦ Eapp f ft ys ⟧)
    (C ⟦ (* Update inlining heuristic *)
         Local (fun IH => IH.(update_App) f ft ys)
         (* Hack: set fresh variable in cdata properly for future passes *)
         (Modify (update_next_var next_x)
         (Rec e')) ⟧).

Definition fun_map : Set := M.tree (fun_tag * list var * exp).

(* Maintain map of known functions while traversing *)
Definition S_fns {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := {
  ρ : fun_map |
  forall f ft xs e_body, M.get f ρ = Some (ft, xs, e_body) ->
  known_function [f]! ft xs e_body C e }.

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

Fixpoint remove_fundefs (fds : fundefs) (ρ : fun_map) : fun_map :=
  match fds with
  | Ffun f ft xs e :: fds => M.remove ![f] (remove_fundefs fds ρ)
  | [] => ρ
  end.

Fixpoint remove_fundefs_not_In f fds ρ :
  ~ (exists ft xs e, In (Ffun (mk_var f) ft xs e) fds) ->
  M.get f (remove_fundefs fds ρ) = M.get f ρ.
Proof.
  destruct fds as [|[[g] gt ys e'] fds]; [reflexivity|cbn; intros Hne].
  destruct (Pos.eq_dec f g); [subst; rewrite M.grs|rewrite M.gro by auto].
  - contradiction Hne; repeat eexists; intuition.
  - rewrite remove_fundefs_not_In; [reflexivity|].
    intros [ft [xs [e Hhas]]]; apply Hne; repeat eexists; eauto.
Defined.

Fixpoint remove_fundefs_In_None f ft xs e fds ρ :
  In (Ffun (mk_var f) ft xs e) fds -> M.get f (remove_fundefs fds ρ) = None.
Proof.
  destruct fds as [|[[g] gt ys e'] fds]; [now cbn|cbn].
  intros [Hhere|Hthere]; [inv Hhere; now rewrite M.grs|].
  destruct (Pos.eq_dec f g); [subst; now rewrite M.grs|rewrite M.gro by auto].
  eapply remove_fundefs_In_None; eauto.
Defined.

Fixpoint remove_fundefs_Some_not f fds ρ fd {struct fds} :
  M.get f (remove_fundefs fds ρ) = Some fd -> ~ (exists ft xs e, In (Ffun (mk_var f) ft xs e) fds).
Proof.
  destruct fds as [|[[g] gt ys e'] fds]; [intros _ [?[?[?[]]]]|cbn; intros Hget].
  destruct (Pos.eq_dec f g); [subst; now rewrite M.grs in Hget|rewrite M.gro in Hget by auto].
  specialize (remove_fundefs_Some_not f fds ρ fd Hget).
  intros [ft [xs [e [Hhere | Hthere]]]]; [intuition congruence|].
  now rewrite (remove_fundefs_In_None _ _ _ _ _ _ Hthere) in Hget.
Defined.

Corollary remove_fundefs_Some f fds ρ fd :
  M.get f (remove_fundefs fds ρ) = Some fd ->
  ~ (exists ft xs e, In (Ffun (mk_var f) ft xs e) fds) /\ M.get f ρ = Some fd.
Proof.
  intros Hget; split; [|rewrite remove_fundefs_not_In in Hget]; eauto;
  eapply remove_fundefs_Some_not; eauto.
Qed.

Ltac inv' H := inversion H; subst; inv_ex.

(* If not entering or exiting a function bundle, the set of known functions remains the same *)

Lemma known_nonbundle_dn {A B} (C : exp_c B exp_univ_exp) (fr : exp_frame_t A B)
      (e : univD A) f ft xs e_body :
  A <> exp_univ_list_fundef -> B <> exp_univ_list_fundef ->
  match fr with Efun1 _ => False | _ => True end ->
  known_function f ft xs e_body C (frameD fr e) ->
  known_function f ft xs e_body (C >:: fr) e.
Proof.
  destruct fr; try congruence; intros _ _ Hfun Hknown;
  solve [
    destruct Hknown as [[D [fds [E [HC Hfxs]]]] | [[D [fds1 [fds2 [E [HC Hfxs]]]]] | []]];
    [left|right; left]; subst C; repeat eexists;
    try match goal with |- _ /\ _ => split end; try match goal with
    | |- context [?fs >++ ?gs >:: ?g] => change (fs >++ gs >:: g) with (fs >++ (gs >:: g))
    end; try reflexivity; try assumption].
Qed.

Lemma known_nonbundle_up {A B} (C : exp_c B exp_univ_exp) (fr : exp_frame_t A B)
      (e : univD A) f ft xs e_body :
  A <> exp_univ_list_fundef -> B <> exp_univ_list_fundef ->
  match fr with Efun1 _ => False | _ => True end ->
  known_function f ft xs e_body (C >:: fr) e ->
  known_function f ft xs e_body C (frameD fr e).
Proof.
  destruct fr; try congruence; intros _ _ Hfun Hknown; try solve [inversion Hfun];
  (destruct Hknown as [[D [fds [E [HC Hfxs]]]] | [[D [fds1 [fds2 [E [HC Hfxs]]]]] | []]];
    [left|right; left];
    (destruct (frames_split' E) as [[AB [Ef [E' HE]]] | [HEeq [HEnil HElen]]];
     [subst E; inv' HC; repeat eexists; eassumption
     |try solve [inversion HEeq|inv' HEnil; inversion HC]])).
Qed.

Instance Preserves_S_S_fns : Preserves_S _ exp_univ_exp (@S_fns).
Proof.
  constructor.
  Local Ltac destruct_known' Hρ :=
    destruct Hρ as [[D[fds'[E[HC HIn]]]]|[[D[fds1[fds2[E[HC Hin]]]]]|[]]].
  Local Ltac destruct_known Hρ :=
    destruct Hρ as [[D[fds'[E[HC HIn]]]]|[[D[fds1[fds2[E[HC Hin]]]]]|[D[fds1[HC Hin]]]]].
  Local Ltac destruct_ctx' E AB fE E' HE :=
    destruct (frames_split' E) as [[AB [fE [E' HE]]]|[?[? ?]]]; [|discriminate].
  Local Ltac destruct_ctx E AB fE E' HE HEeq HEnil HElen :=
    destruct (frames_split' E) as [[AB [fE [E' HE]]]|[HEeq [HEnil HElen]]].
  (* Moving upwards *)
  - intros A B C f e [ρ Hρ]; destruct f; lazymatch goal with
    (* There are only a few cases that we care about: *)
    | |- S_fns C (frameD (Efun0 ?e') ?fds') => rename e' into e, fds' into fds
    | |- S_fns C (frameD (Efun1 ?fds') ?e') => rename e' into e, fds' into fds
    | |- S_fns C (frameD (cons_fundef0 ?fds') ?fd) => destruct fd as [[f] ft xs e_body]; rename fds' into fds
    | |- S_fns C (frameD (cons_fundef1 ?fd) ?fds') => destruct fd as [[f] ft xs e_body]; rename fds' into fds
    (* For all the others, the map should remain unchanged *)
    | _ =>
      exists ρ; intros f' ft' xs' e' Hftxse'; specialize (Hρ f' ft' xs' e' Hftxse');
      apply known_nonbundle_up; [now inversion 1..|exact I|assumption]
    end.
    (* When leaving a function definition f(xs) = e, need to add f back into the map *)
    + exists (M.set f (ft, xs, e_body) ρ); intros g gt ys e Hget.
      destruct (Pos.eq_dec g f) as [Hgf|Hgf]; [subst f; rewrite M.gss in Hget|rewrite M.gso in Hget by auto].
      * (* f is now a known function *) inv Hget; right; right; exists C, []; split; [reflexivity|now left].
      * (* All other functions are still known *)
        specialize (Hρ g gt ys e Hget); destruct_known' Hρ; [left|right].
        -- destruct_ctx' E AB fE E' HE; subst E; inv' HC; now repeat eexists.
        -- destruct_ctx E AB fE E' HE HEeq HEnil HElen; [subst E; left|right].
           ++ inv' HC; now repeat eexists.
           ++ inv' HEnil; inv' HC.
              exists D, fds1; split; [auto|]; apply in_app_or in Hin; apply in_or_app.
              now (destruct Hin; [left|right; right]).
    (* When moving upwards along a function bundle, the set of known functions remains unchanged *)
    + exists ρ; intros g gt ys e Hget; specialize (Hρ g gt ys e Hget); destruct_known Hρ.
      (* If g was defined in an earlier bundle, g is still known *)
      * destruct_ctx' E AB fE E' HE; subst E; inv' HC; left; now repeat eexists.
      (* If g was defined in a bundle and we are currently inside one of the bundle's definitions,
         g is still known *)
      * destruct_ctx' E AB fE E' HE; subst E; right; left; inv' HC; now repeat eexists.
      (* If g was defined in the bundle we are currently traversing, g is still known (though it
         may be to the right of us instead of to the left now as we are moving upwards through the
         bundle) *)
      * destruct fds1 as [|[f1 ft1 xs1 e1] fds1].
        -- destruct_ctx' D AB fD D' HD; subst D.
           inv' HC; right; right; exists D', []; split; [easy|now right].
        -- inv' HC; right; right; exists D, fds1; split; [easy|].
           apply in_app_or in Hin; apply in_or_app.
           now destruct Hin as [[Hin|Hin]|Hin]; [inv Hin; right; left|left|right; right].
    (* When moving upwards past a function bundle, the whole bundle must be deleted *)
    + exists (remove_fundefs fds ρ); intros g gt ys e_body Hget.
      apply remove_fundefs_Some in Hget; destruct Hget as [Hne Hget]; specialize (Hρ g gt ys e_body Hget).
      destruct_known Hρ.
      (* If g was defined in an earlier bundle, it's still known *)
      * destruct_ctx' E AB fE E' HE; subst E; inv' HC; left; now repeat eexists.
      (* If g was defined in a bundle and we're currently in one of its definitions, g is still known *)
      * destruct_ctx' E AB fE E' HE; subst E; right; left; inv' HC; now repeat eexists.
      (* If g was defined in the bundle we are leaving, then it can't have been in (remove_fundefs fds ρ)
         in the first place *)
      * destruct fds1 as [|fd fds1]; [|now inversion HC]; contradiction Hne; now repeat eexists.
    (* Ditto, but this time moving upwards to (Efun fds e) from e instead of from fds *)
    + exists (remove_fundefs fds ρ); intros g gt ys e_body Hget.
      apply remove_fundefs_Some in Hget; destruct Hget as [Hne Hget]; specialize (Hρ g gt ys e_body Hget).
      destruct_known' Hρ.
      * destruct_ctx E AB fE E' HE HEeq HEnil HElen.
        -- subst E; inv' HC; left; now repeat eexists.
        -- inv' HEnil; inv' HC; contradiction Hne; now repeat eexists.
      * destruct_ctx' E AB fE E' HE; subst E; right; left; inv' HC; now repeat eexists.
  (* Moving downwards *)
  - intros A B C f e [ρ Hρ]; destruct f; lazymatch goal with
    (* There are only a few cases that we care about: *)
    | |- S_fns (C >:: Efun0 ?e') ?fds' => rename e' into e, fds' into fds
    | |- S_fns (C >:: Efun1 ?fds') ?e' => rename e' into e, fds' into fds
    | |- S_fns (C >:: cons_fundef0 ?fds') ?fd => destruct fd as [[f] ft xs e_body]; rename fds' into fds
    | |- S_fns (C >:: cons_fundef1 ?fd) ?fds' => destruct fd as [[f] ft xs e_body]; rename fds' into fds
    (* For all the others, the map should remain unchanged *)
    | _ =>
      exists ρ; intros f' ft' xs' e' Hftxse'; specialize (Hρ f' ft' xs' e' Hftxse');
      apply known_nonbundle_dn; [now inversion 1..|exact I|assumption]
    end.
    Local Ltac still_known :=
      subst; change (?l >++ ?r >:: ?f) with (l >++ (r >:: f));
      (left + (right; left)); now repeat eexists.
    (* When entering a function body f(xs) = e_body, need to delete ρ(f) *)
    + exists (M.remove f ρ); intros g gt ys e Hget; destruct (Pos.eq_dec g f) as [Hgf|Hgf];
      [subst f; now rewrite M.grs in Hget|rewrite M.gro in Hget by auto]; specialize (Hρ g gt ys e Hget).
      (* If g was defined in a bundle earlier, it's still there *)
      destruct_known Hρ; [still_known..|].
      (* If g was defined in the bundle that we were traversing and g <> f, then g is still known
         but now as a function defined in an "earlier bundle" instead of as a function in the bundle
         currently being traversed *)
      right; left; exists D, fds1, fds, <[]>; split; [now subst C|].
      apply in_app_or in Hin; apply in_or_app; now destruct Hin as [Hin|[Hin|Hin]]; [left|inv Hin|right].
    (* When moving downwards along a function bundle, the set of known functions doesn't change *)
    + exists ρ; intros g gt ys e Hget; specialize (Hρ g gt ys e Hget); destruct_known Hρ; [still_known..|].
      subst C; change (?l >++ ctx_of_fds ?r >:: cons_fundef1 ?f) with (l >++ ctx_of_fds (f :: r)).
      right; right; repeat eexists; apply in_app_or in Hin; apply in_or_app.
      destruct Hin as [Hin|[Hin|Hin]]; [now (left; right)|left; left; now inv Hin|now right].
    (* When entering a function bundle fds, need to add the whole bundle to ρ *)
    + exists (add_fundefs fds ρ); intros g gt ys e_body Hget.
      (* If g ∈ fds then g is clearly in the bundle we are currently traversing *)
      apply add_fundefs_Some in Hget; destruct Hget as [Hget|Hget]; [do 2 right; eexists; now exists []|].
      (* Otherwise, g is still known *)
      specialize (Hρ _ _ _ _ Hget); destruct_known' Hρ; still_known.
    (* Ditto when entering e in (Efun fds e) *)
    + exists (add_fundefs fds ρ); intros g gt ys e_body Hget.
      (* If g ∈ fds then g is clearly defined in an 'earlier' bundle *)
      apply add_fundefs_Some in Hget; destruct Hget as [Hget|Hget]; [left; now exists C, fds, <[]>|].
      (* Otherwise, g is still known *)
      specialize (Hρ _ _ _ _ Hget); destruct_known' Hρ; still_known.
Defined.


(*
Definition rename' {A} (σ : r_map) : univD A -> univD A :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(c, e) => (c, [rename_all σ ![e]]!)
  | exp_univ_list_prod_ctor_tag_exp => fun ces => map (fun '(c, e) => (c, [rename_all σ ![e]]!)) ces
  | exp_univ_list_fundef => fun fds => [rename_all_fun σ ![fds]]!
  | exp_univ_exp => fun e => [rename_all σ ![e]]!
  | exp_univ_var => fun x => [apply_r σ ![x]]!
  | exp_univ_fun_tag => fun ft => ft
  | exp_univ_ctor_tag => fun c => c
  | exp_univ_prim => fun p => p
  | exp_univ_N => fun n => n
  | exp_univ_list_var => fun xs => [apply_r_list σ ![xs]]!
  end.
*)

(*
Definition delay_t {A} (e : univD A) : Set := {
  σ : r_map |
  Disjoint _ (range (fun x => M.get x σ)) (used e) /\
  Disjoint _ (domain (fun x => M.get x σ)) (used e) }.
Instance Delayed_delay_t : Delayed (@delay_t).
Proof.
  unshelve econstructor; [exact @run_delay_t|..].
  - intros A e; exists (M.empty _).
    assert (Hdom : domain (fun x => M.get x (M.empty cps.var)) <--> Empty_set _). {
      split; unfold domain; [intros x Hx; unfold Ensembles.In in Hx|inversion 1].
      destruct Hx as [y Hy]; now rewrite M.gempty in Hy. }
    assert (Hran : range (fun x => M.get x (M.empty cps.var)) <--> Empty_set _). {
      split; unfold codomain; [intros y Hy; unfold Ensembles.In in Hy|inversion 1].
      destruct Hy as [x Hx]; unfold apply_r in Hx; now rewrite M.gempty in Hx. }
    rewrite Hdom, Hran; eauto with Ensembles_DB.
  - destruct A; intros e; simpl in *;
      try match goal with |- (let '(_, _) := ?rhs in _) = _ => destruct rhs end;
      try match goal with |- map _ _ = _ => apply MCList.map_id_f; intros [c' e'] end;
      repeat (rewrite apply_r_empty || rewrite apply_r_list_empty);
      try rewrite <- (proj1 rename_all_empty); try rewrite <- (proj2 rename_all_empty);
      unbox_newtypes; normalize_roundtrips; try reflexivity.
Defined.
Definition run_delay_t {A} (e : univD A) (d : delay_t e) : univD A := rename' (proj1_sig d) e.

*)

Section Beta.

  Variable St:Type.
  Variable (pp_St : St -> name_env -> string).
  Variable IH : InlineHeuristic St.

  (* Construct known-functions map *)
  Fixpoint add_fundefs (fds:fundefs) (fm: fun_map) : fun_map :=
    match fds with
    | Fnil => fm
    | Fcons f t xs e fds => M.set f (t, xs, e) (add_fundefs fds fm)
    end.

  Instance OptMonad : Monad option.
  Proof.
    constructor.
    - intros X x. exact (Some x).
    - intros A B [ a | ] f.
      now eauto.
      exact None.
  Defined.

  Definition debug_st (s : St) : freshM unit :=
    nenv <- get_name_env () ;;
    log_msg (pp_St s nenv);;
    log_msg Pipeline_utils.newline.

  Fixpoint beta_contract (d : nat) {struct d} :=
    let fix beta_contract_aux (e : exp) (sig : r_map) (fm:fun_map) (s:St) {struct e} : freshM exp :=
        match e with
        | Econstr x t ys e =>
          let ys' := apply_r_list sig ys in
          e' <- beta_contract_aux e sig fm s;;
          ret (Econstr x t ys' e')
        | Ecase v cl =>
          let v' := apply_r sig v in
          cl' <- (fix beta_list (br: list (ctor_tag*exp)) : freshM (list (ctor_tag*exp)) :=
                   match br with
                   | nil => ret ( nil)
                   | (t, e)::br' =>
                     e' <- beta_contract_aux e sig fm s;;
                     br'' <- beta_list br';;
                     ret ((t, e')::br'')
                   end) cl;;
          ret (Ecase v' cl')
       | Eproj x t n y e =>
         let y' := apply_r sig y in
         e' <- beta_contract_aux e sig fm s;;
         ret (Eproj x t n y' e')
       | Eletapp x f t ys ec =>
         let f' := apply_r sig f in
         let ys' := apply_r_list sig ys in
         let (s' , inl) := update_letApp _ IH f' t ys' s in
         (match (inl, M.get f' fm, d) with
          | (true, Some (t, xs, e), S d') =>
            e' <- freshen_exp e;;
            match inline_letapp e' x with
            | Some (C, x') =>
              let sig' := set_list (combine xs ys') sig  in
              beta_contract d' (C |[ ec ]|) (M.set x (apply_r sig' x') sig') fm s'
            | None =>
              ec' <- beta_contract_aux ec sig fm s' ;;
              ret (Eletapp x f' t ys' ec')
            end
          | _ =>
            ec' <- beta_contract_aux ec sig fm s' ;;
            ret (Eletapp x f' t ys' ec')
          end)
       | Efun fds e =>
         let fm' := add_fundefs fds fm in
         let (s1, s2) := update_funDef _ IH fds sig s in
         (* debug_st s1;; *)
         fds' <- (fix beta_contract_fds (fds:fundefs) (s:St) : freshM fundefs :=
                   match fds with
                   | Fcons f t xs e fds' =>
                     let s' := update_inFun _ IH f t xs e sig s in
                     e' <- beta_contract_aux e sig fm' s' ;;
                     fds'' <- beta_contract_fds fds' s ;;
                     ret (Fcons f t xs e' fds'')
                   | Fnil => ret Fnil
                   end) fds s2 ;;
         e' <- beta_contract_aux e sig fm' s1;;
         ret (Efun fds' e')
       | Eapp f t ys =>
         let f' := apply_r sig f in
         let ys' := apply_r_list sig ys in
         let (s', inl) := update_App _ IH f' t ys' s in
         (* fstr <- get_pp_name f' ;; *)
         (* log_msg ("Application of " ++ fstr ++ " is " ++ if inl then "" else "not " ++ "inlined") ;; *)
         (match (inl, M.get f' fm, d) with
          | (true, Some (t, xs, e), S d') =>
            let sig' := set_list (combine xs ys') sig  in
            e' <- freshen_exp e;;
            beta_contract d' e' sig' fm  s'
          | _ => ret (Eapp f' t ys')
          end)
       | Eprim x t ys e =>
         let ys' := apply_r_list sig ys in
         e' <- beta_contract_aux e sig fm s;;
         ret (Eprim x t ys' e')
       | Ehalt x =>
         let x' := apply_r sig x in
         ret (Ehalt x')
        end
    in beta_contract_aux.


  (* Old fds for reference *)
  (* Function beta_contract_fds (fds:fundefs) (fcon: St -> forall e:exp, (term_size e < funs_size fds)%nat -> freshM exp)  (fdc:fundefs) (sig:r_map) (s:St) (p:  cps_util.subfds_or_eq fdc fds): freshM fundefs := *)
  (*   (match fdc as x return x = fdc -> _ with *)
  (*    | Fcons f t xs e fdc' => *)
  (*      fun Heq_fdc => *)
  (*        let s' := update_inFun _ IH f t xs e sig s in *)
  (*       e' <- fcon s' e (beta_contract_fds_1 (eq_ind_r (fun a => cps_util.subfds_or_eq a fds) p Heq_fdc));; *)
  (*       fds' <- beta_contract_fds fds fcon fdc' sig s (beta_contract_fds_2 (eq_ind_r (fun a => cps_util.subfds_or_eq a fds) p Heq_fdc));; *)
  (*        ret (Fcons f t xs e' fds') *)
  (*   | Fnil => fun _ => ret Fnil *)
  (*   end) (eq_refl fdc). *)

  Definition beta_contract_top (e:exp) (d:nat) (s:St) (c:comp_data) : error exp * comp_data :=
    let '(e', (st', _)) := run_compM (beta_contract d e (M.empty var) (M.empty _) s) c tt in
    (e', st').

End Beta.

(* d should be max argument size, perhaps passed through by uncurry *)
Definition postuncurry_contract (e:exp) (s:M.t nat) (d:nat) :=
  beta_contract_top _ PostUncurryIH e d s.

Definition inlinesmall_contract (e:exp) (bound:nat)  (d:nat) :=
  beta_contract_top _ (InlineSmallIH bound) e d (M.empty _).

Definition inline_uncurry_contract (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
  beta_contract_top _ (InlineSmallOrUncurried bound) e d (M.empty bool, s).

Definition inline_uncurry (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
  beta_contract_top _ InineUncurried e d (M.empty bool).

Set Printing All.
Print inline_uncurry.

Definition inline_uncurry_marked_anf (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
  beta_contract_top _ InlinedUncurriedMarkedAnf e d s.
