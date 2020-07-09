Require Import Coq.Sets.Ensembles Coq.ZArith.ZArith.
Require Import L6.Ensembles_util L6.map_util.
Require Import L6.state L6.alpha_conv L6.identifiers L6.functions L6.shrink_cps.
Require Import L6.Prototype.
Require Import L6.cps_proto L6.proto_util.

Require Import Lia.

Require Import Coq.Lists.List.
Import ListNotations.

Unset Strict Unquote Universe Mode.

(** * Inlining heuristics *)

(* Rather than parameterizing by [St] as in inline.v, the heuristic is
   represented as a record of closures (like an OOP class). This is to allow the heuristic to
   stay in Set, which is necessary to get along with the MetaCoq in Prototype.v.

   We also don't pass in the renaming [r_map]. *)
CoInductive InlineHeuristic : Set := {
  (* Update inlining decision before entering fds in Efun fds e. *)
  update_funDef1 : fundefs -> exp -> InlineHeuristic;
  (* Update inlining decision before entering e in Efun fds e. *)
  update_funDef2 : fundefs -> exp -> InlineHeuristic;
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
  update_funDef1 fds e :=
    let IH1 := IH1.(update_funDef1) fds e in
    let IH2 := IH2.(update_funDef1) fds e in
    (CombineInlineHeuristic deci IH1 IH2);
  update_funDef2 fds e :=
    let IH1 := IH1.(update_funDef2) fds e in
    let IH2 := IH2.(update_funDef2) fds e in
    (CombineInlineHeuristic deci IH1 IH2);
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
    update_funDef1 fds e := IH s;
    update_funDef2 fds e := IH s;
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
  let fix upd fds s := 
    match fds with
    | Ffun f ft xs e :: fdc' =>
      if (Init.Nat.ltb (term_size ![e]) bound)
      then upd fdc' (M.set ![f] true s)
      else upd fdc' s
    | Fnil => s
    end
  in
  cofix IH s := {|
    (* Add small, [todo: non-recursive] functions to s *)
    update_funDef1 fds e := IH (upd fds s);
    update_funDef2 fds e := IH (upd fds s);
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
    update_funDef1 fds e := IH (find_uncurried fds s);
    update_funDef2 fds e := IH (find_uncurried fds s);
    update_inFun f ft xs e := IH s;
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
    update_funDef1 fds e := IH (find_uncurried fds s);
    update_funDef2 fds e := IH (find_uncurried fds s);
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
    update_funDef1 fds e := IH s;
    update_funDef2 fds e := IH s;
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

Lemma set_lists_None_length {A} ρ xs (vs : list A) :
  set_lists xs vs ρ = None -> length xs <> length vs.
Proof.
  revert vs; induction xs as [|x xs IHxs]; destruct vs; cbn; try congruence.
  destruct (set_lists xs vs ρ) eqn:Heq; try congruence.
  (assert (length xs <> length vs) by now apply IHxs); lia.
Qed.

Hint Rewrite used_vars_Econstr : UsedDB.
Hint Rewrite used_vars_Eproj : UsedDB.
Hint Rewrite used_vars_Ecase : UsedDB.
Hint Rewrite used_vars_Ecase_app : UsedDB.
Hint Rewrite used_vars_Efun : UsedDB.
Hint Rewrite used_vars_Eletapp : UsedDB.
Hint Rewrite used_vars_Eapp : UsedDB.
Hint Rewrite used_vars_Eprim : UsedDB.
Hint Rewrite used_vars_Ehalt : UsedDB.
Hint Rewrite used_vars_Fcons : UsedDB.
Hint Rewrite used_vars_Fnil : UsedDB.

Hint Rewrite @image_Union : ImageDB.
Hint Rewrite @image_Singleton : ImageDB.

Lemma FromList_map_image_FromList' {A B} (l : list A) (f : A -> B) :
  image f (FromList l) <--> FromList (map f l).
Proof. now rewrite FromList_map_image_FromList. Qed.

Hint Rewrite @FromList_map_image_FromList' : ImageDB.

Lemma Singleton_fresher_than x y : fresher_than x [set y] -> x > y.
Proof. intros H; apply H; constructor. Qed.

Local Ltac normalize_images :=
  repeat (
    autorewrite with ImageDB UsedDB in *;
    try lazymatch goal with
    | H : fresher_than _ [set _] |- _ => apply Singleton_fresher_than in H
    | H : fresher_than _ (_ :|: _) |- _ => apply Union_fresher_than in H; destruct H
    | H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H; destruct H
    | H : Disjoint _ (_ :|: _) _ |- _ => apply Disjoint_commut in H
    end).

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

Lemma name_in_fundefs_FromList fds : name_in_fundefs ![fds] <--> FromList ![map fun_name fds].
Proof.
  induction fds as [|[[f] [ft] xs e] fds IHfds].
  - cbn; now rewrite FromList_nil.
  - cbn in *; normalize_sets; now rewrite IHfds.
Qed.

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
  | H : _ -> ?P |- ?P => apply H; solve_easy
  end].

Local Ltac set_lists_safe σ0 Hσ0 :=
  match goal with
  | Hlen : length _ = length _, Hset : context [match set_lists ?xs ?ys ?σ with _ => _ end] |- _ =>
    destruct (set_lists xs ys σ) as [σ0|] eqn:Hσ0;
    [|apply set_lists_None_length in Hσ0; unfold strip_vars in Hσ0; now repeat rewrite map_length in Hσ0]
  | Hlen : length _ = length _ |- context [match set_lists ?xs ?ys ?σ with _ => _ end] =>
    destruct (set_lists xs ys σ) as [σ0|] eqn:Hσ0;
    [|apply set_lists_None_length in Hσ0; unfold strip_vars in Hσ0; now repeat rewrite map_length in Hσ0]
  end.

Local Ltac do_gensyms next xs next0 xs0 Hxs0 Hgt Hlen :=
  destruct (gensyms next xs) as [next0 xs0] eqn:Hxs0; symmetry in Hxs0;
  (assert (Hgt : next0 >= next) by now eapply gensyms_upper1);
  (assert (Hlen : length xs0 = length xs) by now eapply gensyms_len').

Section FreshenInd.

Context
  (P_exp : r_map -> positive -> exp -> positive -> exp -> Prop)
  (P_ces : r_map -> positive -> list (ctor_tag * exp) -> positive -> list (ctor_tag * exp) -> Prop)
  (P_fds : r_map -> positive -> list fundef -> positive -> list fundef -> Prop).

Context
  (Hconstr : forall x c ys e σ next next' e',
    (next', e') = freshen_exp (next + 1) (M.set x next σ) e ->
    P_exp (M.set x next σ) (next + 1) e next' e' ->
    P_exp σ next (Econstr (mk_var x) c ys e)
          next' (Econstr (mk_var next) c (map mk_var (map (apply_r σ) (strip_vars ys))) e'))
  (Hces : forall σ next x ces next' ces', 
    (next', ces') = freshen_ces next σ ces ->
    P_ces σ next ces next' ces' ->
    P_exp σ next (Ecase (mk_var x) ces) next' (Ecase (mk_var (apply_r σ x)) ces'))
  (Hfds : forall next next' next'' next''' σ σ' fds fds' e e' fs',
    (next', fs') = gensyms next (map fun_name fds) ->
    set_lists (strip_vars (map fun_name fds)) (strip_vars fs') σ = Some σ' ->
    (next'', fds') = freshen_fds next' σ' fds ->
    P_fds σ' next' fds next'' fds' ->
    (next''', e') = freshen_exp next'' σ' e ->
    P_exp σ' next'' e next''' e' ->
    P_exp σ next (Efun fds e) next''' (Efun fds' e'))
  (Hproj : forall x c n y e σ next next' e',
    (next', e') = freshen_exp (next + 1) (M.set x next σ) e ->
    P_exp (M.set x next σ) (next + 1) e next' e' ->
    P_exp σ next (Eproj (mk_var x) c n (mk_var y) e) next'
          (Eproj (mk_var next) c n (mk_var (apply_r σ y)) e'))
  (Hletapp : forall x f ft ys e σ next next' e',
    (next', e') = freshen_exp (next + 1) (M.set x next σ) e ->
    P_exp (M.set x next σ) (next + 1) e next' e' ->
    P_exp σ next (Eletapp (mk_var x) (mk_var f) (mk_fun_tag ft) ys e) next'
          (Eletapp (mk_var next) (mk_var (apply_r σ f)) (mk_fun_tag ft)
                   (map mk_var (map (apply_r σ) (strip_vars ys))) e'))
  (Happ : forall f ft xs next σ,
    P_exp σ next (Eapp (mk_var f) (mk_fun_tag ft) xs) next
          (Eapp (mk_var (apply_r σ f)) (mk_fun_tag ft)
                (map mk_var (map (apply_r σ) (strip_vars xs)))))
  (Hprim : forall x p ys e σ next next' e',
    (next', e') = freshen_exp (next + 1) (M.set x next σ) e ->
    P_exp (M.set x next σ) (next + 1) e next' e' ->
    P_exp σ next (Eprim (mk_var x) (mk_prim p) ys e) next'
          (Eprim (mk_var next) (mk_prim p)
                 (map mk_var (map (apply_r σ) (strip_vars ys))) e'))
  (Hhalt : forall x next σ, P_exp σ next (Ehalt (mk_var x)) next (Ehalt (mk_var (apply_r σ x)))).

Context
  (Hfds_nil : forall next σ, P_fds σ next [] next [])
  (Hfds_cons : forall σ σ' next next' next'' next''' f ft xs xs' e e' fds fds',
    (next', xs') = gensyms next xs ->
    set_lists (strip_vars xs) (strip_vars xs') σ = Some σ' ->
    (next'', e') = freshen_exp next' σ' e ->
    P_exp σ' next' e next'' e' ->
    (next''', fds') = freshen_fds next'' σ fds ->
    P_fds σ next'' fds next''' fds' ->
    P_fds σ next (Ffun (mk_var f) ft xs e :: fds)
          next''' (Ffun (mk_var (apply_r σ f)) ft xs' e' :: fds')).

Context
  (Hces_nil : forall next σ, P_ces σ next [] next [])
  (Hces_cons : forall σ next next' next'' c e e' ces ces',
    (next', e') = freshen_exp next σ e ->
    P_exp σ next e next' e' ->
    (next'', ces') = freshen_ces next' σ ces ->
    P_ces σ next' ces next'' ces' ->
    P_ces σ next ((c, e) :: ces) next'' ((c, e') :: ces')).

Fixpoint freshen_exp_ind σ next e next' e' {struct e} :
  (next', e') = freshen_exp next σ e -> P_exp σ next e next' e'.
Proof.
  destruct e; unbox_newtypes; cbn in *; intros Heq;
    try solve [inv Heq; clear freshen_exp_ind; auto
              |destruct (freshen_exp (next + 1) _ e) as [next0 e0] eqn:He0;
               symmetry in He0; inv Heq; pose (IH := He0); clearbody IH;
               apply freshen_exp_ind in IH; clear freshen_exp_ind; auto].
  - change (freshen_ces' freshen_exp) with freshen_ces in *.
    destruct (freshen_ces next σ ces) as [next0 ces'] eqn:Hces'; symmetry in Hces'.
    inv Heq; apply Hces; auto; rename next0 into next'; clear x.
    revert next next' σ ces' Hces'; induction ces as [|[c e] ces IHces]; intros next next' σ ces' Heq.
    + inv Heq; apply Hces_nil.
    + cbn in Heq.
      destruct (freshen_exp next σ e) as [next0 e0] eqn:He0; symmetry in He0.
      pose (IH := He0); clearbody IH; apply freshen_exp_ind in IH; clear freshen_exp_ind. Guarded.
      destruct (freshen_ces next0 σ ces) as [next1 ces0] eqn:Hces0; symmetry in Hces0.
      inv Heq; eapply Hces_cons; eauto.
  - change (freshen_fds' freshen_exp) with freshen_fds in *.
    do_gensyms next (map fun_name fds) next0 xs0 Hxs0 Hge Hlen.
    rewrite map_length in Hlen; set_lists_safe σ0 Hσ0.
    destruct (freshen_fds next0 σ0 fds) as [next1 fds0] eqn:Hfds0; symmetry in Hfds0.
    destruct (freshen_exp next1 σ0 e) as [next2 e0] eqn:He0; symmetry in He0.
    pose (IH := He0); clearbody IH; apply freshen_exp_ind in IH.
    inv Heq; eapply Hfds; eauto. Guarded.
    clear - freshen_exp_ind Hfds_nil Hfds_cons Hfds0.
    revert next0 σ0 next1 fds0 Hfds0; induction fds as [|[[f] ft xs e] fds IHfds];
      intros next σ next' fds' Heq; [inv Heq; apply Hfds_nil|cbn in Heq].
    do_gensyms next xs next0 xs0 Hxs0 Hge Hlen.
    set_lists_safe σ0 Hσ0.
    destruct (freshen_exp next0 σ0 e) as [next1 e0] eqn:He0; symmetry in He0.
    pose (IH := He0); clearbody IH; apply freshen_exp_ind in IH; clear freshen_exp_ind. Guarded.
    destruct (freshen_fds next1 σ fds) as [next2 fds0] eqn:Hfds0; symmetry in Hfds0.
    pose (IH' := Hfds0); clearbody IH'; apply IHfds in IH'; inv Heq.
    eapply Hfds_cons; eauto.
Qed.

Fixpoint freshen_ces_ind σ next ces next' ces' {struct ces} :
  (next', ces') = freshen_ces next σ ces -> P_ces σ next ces next' ces'.
Proof.
  intros Heq; destruct ces as [|[c e] ces]; [inv Heq; apply Hces_nil|cbn in Heq].
  destruct (freshen_exp next σ e) as [next0 e0] eqn:He0; symmetry in He0.
  destruct (freshen_ces next0 σ ces) as [next1 ces0] eqn:Hces0; symmetry in Hces0.
  pose (IH := He0); clearbody IH; apply freshen_exp_ind in IH.
  pose (IH' := Hces0); clearbody IH'; apply freshen_ces_ind in IH'.
  inv Heq; eapply Hces_cons; eauto.
Qed.

Fixpoint freshen_fds_ind σ next fds next' fds' {struct fds} :
  (next', fds') = freshen_fds next σ fds -> P_fds σ next fds next' fds'.
Proof.
  intros Heq; destruct fds as [|[[f] ft xs e] fds]; [inv Heq; apply Hfds_nil|cbn in Heq].
  do_gensyms next xs next0 xs0 Hxs0 Hge Hlen.
  set_lists_safe σ0 Hσ0.
  destruct (freshen_exp next0 σ0 e) as [next1 e0] eqn:He0; symmetry in He0.
  destruct (freshen_fds next1 σ fds) as [next2 fds0] eqn:Hfds0; symmetry in Hfds0.
  pose (IH := He0); clearbody IH; apply freshen_exp_ind in IH.
  pose (IH' := Hfds0); clearbody IH'; apply freshen_fds_ind in IH'.
  inv Heq; eapply Hfds_cons; eauto.
Qed.

Definition exp_stmt :=
  (forall σ next e next' e', (next', e') = freshen_exp next σ e -> P_exp σ next e next' e').

Definition ces_stmt :=
  (forall σ next ces next' ces', (next', ces') = freshen_ces next σ ces -> P_ces σ next ces next' ces').

Definition fds_stmt :=
  (forall σ next fds next' fds', (next', fds') = freshen_fds next σ fds -> P_fds σ next fds next' fds').

Definition freshen_stmt := exp_stmt /\ ces_stmt /\ fds_stmt.

Lemma freshen_ind : freshen_stmt.
Proof.
  repeat split; unfold exp_stmt, ces_stmt, fds_stmt;
    [apply freshen_exp_ind|apply freshen_ces_ind|apply freshen_fds_ind].
Qed.

End FreshenInd.

Lemma freshen_increasing :
  freshen_stmt
    (fun σ next e next' e' => next' >= next)
    (fun σ next ces next' ces' => next' >= next)
    (fun σ next fds next' fds' => next' >= next).
Proof.
  apply freshen_ind; intros; try match goal with
  | H : (?next', _) = gensyms ?next _ |- _ =>
    assert (next' >= next) by now eapply gensyms_upper1
  end; lia.
Qed.

Corollary freshen_exp_increasing : exp_stmt (fun σ next e next' e' => next' >= next).
Proof. apply freshen_increasing. Qed.

Corollary freshen_ces_increasing : ces_stmt (fun σ next e next' e' => next' >= next).
Proof. apply freshen_increasing. Qed.

Corollary freshen_fds_increasing : fds_stmt (fun σ next e next' e' => next' >= next).
Proof. apply freshen_increasing. Qed.

Lemma freshen_used :
  freshen_stmt
    (fun σ next e next' e' =>
      fresher_than next (used_vars ![e] :|: image (apply_r σ) (used_vars ![e])) ->
      fresher_than next' (used_vars ![e']))
    (fun σ next ces next' ces' =>
      fresher_than next (used_vars_ces ![ces] :|: image (apply_r σ) (used_vars_ces ![ces])) ->
      fresher_than next' (used_vars_ces ![ces']))
    (fun σ next fds next' fds' =>
      (fresher_than next (used_vars_fundefs ![fds] :|: image (apply_r σ) (used_vars_fundefs ![fds])) ->
       fresher_than next' (used_vars_fundefs ![fds']))).
Proof.
  apply freshen_ind; intros; unbox_newtypes; cbn in *; normalize_roundtrips;
  try match goal with
  | H : (?next', _) = freshen_exp ?next _ _ |- _ =>
    assert (next' >= next) by now eapply freshen_exp_increasing
  end.
  Local Ltac set_lists_included :=
    match goal with
    | Hsets : set_lists _ _ ?σ = Some ?σ' |- fresher_than _ (image (apply_r ?σ') _) =>
      rewrite <- apply_r_set_lists; [|exact Hsets];
      eapply fresher_than_antimon;
        [apply image_extend_lst_Included; unfold strip_vars;
         now repeat rewrite map_length|];
      apply fresher_than_Union; [|solve_easy];
      eapply fresher_than_antimon; [apply image_monotonic, Setminus_Included|];
      solve_easy
    end.
  - normalize_images; solve_easy.
  - normalize_images.
    assert (next' >= next) by now eapply freshen_ces_increasing.
    solve_easy.
  - edestruct @gensyms_spec as [Hcopies [Hfresh Hlen]]; try exact H; [eassumption|].
    rewrite map_length in Hlen.
    assert (next'' >= next') by now eapply freshen_fds_increasing.
    assert (next''' >= next'') by now eapply freshen_exp_increasing.
    normalize_images.
    assert (fresher_than next'' (used_vars_fundefs (fundefs_of_proto fds'))). {
      apply H2; apply fresher_than_Union; [solve_easy|]; set_lists_included. }
    assert (fresher_than next''' (used_vars (exp_of_proto e'))). {
      apply H4; apply fresher_than_Union; [solve_easy|]; set_lists_included. }
    solve_easy.
  - normalize_images; solve_easy.
  - normalize_images; solve_easy.
  - normalize_images; solve_easy.
  - normalize_images; solve_easy.
  - normalize_images; solve_easy.
  - normalize_images; solve_easy.
  - edestruct @gensyms_spec as [Hcopies [Hfresh Hlen]]; try exact H; [eassumption|].
    assert (next'' >= next') by now eapply freshen_exp_increasing.
    assert (next''' >= next'') by now eapply freshen_fds_increasing.
    normalize_images.
    assert (fresher_than next''' (used_vars_fundefs (fundefs_of_proto fds'))) by solve_easy.
    assert (fresher_than next'' (used_vars (exp_of_proto e'))). {
      apply H2; apply fresher_than_Union; [solve_easy|]; set_lists_included. }
    solve_easy.
  - normalize_images; solve_easy.
  - assert (next' >= next) by now eapply freshen_exp_increasing.
    assert (next'' >=  next') by now eapply freshen_ces_increasing.
    change (ces_of_proto' exp_of_proto) with ces_of_proto in *.
    normalize_images; cbn in *; normalize_images.
    assert (fresher_than next' (used_vars (exp_of_proto e'))) by solve_easy.
    solve_easy.
Qed.

Corollary freshen_exp_used : exp_stmt (fun σ next e next' e' =>
  fresher_than next (used_vars ![e] :|: image (apply_r σ) (used_vars ![e])) ->
  fresher_than next' (used_vars ![e'])).
Proof. apply freshen_used. Qed.

Corollary freshen_ces_used : ces_stmt (fun σ next ces next' ces' =>
  fresher_than next (used_vars_ces ![ces] :|: image (apply_r σ) (used_vars_ces ![ces])) ->
  fresher_than next' (used_vars_ces ![ces'])).
Proof. apply freshen_used. Qed.

Corollary freshen_fds_used : fds_stmt (fun σ next fds next' fds' =>
  (fresher_than next (used_vars_fundefs ![fds] :|: image (apply_r σ) (used_vars_fundefs ![fds])) ->
   fresher_than next' (used_vars_fundefs ![fds']))).
Proof. apply freshen_used. Qed.

Local Ltac freshen_used_facts :=
  try match goal with
  | H : (?next', _) = gensyms ?next _ |- _ =>
    assert (next' >= next) by now eapply gensyms_upper1
  end;
  try match goal with
  | H : (?next', _) = freshen_exp ?next _ _ |- _ =>
    assert (next' >= next) by now eapply freshen_exp_increasing
  end; try match goal with
  | H : (?next', _) = freshen_ces ?next _ _ |- _ =>
    assert (next' >= next) by now eapply freshen_ces_increasing
  end; try match goal with
  | H : (?next', _) = freshen_fds ?next _ _ |- _ =>
    assert (next' >= next) by now eapply freshen_fds_increasing
  end.

Fixpoint bound_var_no_names fds :=
  match fds with
  | cps.Fnil => Empty_set _
  | cps.Fcons _ _ xs e fds => FromList xs :|: bound_var e :|: bound_var_no_names fds
  end.

Lemma bound_var_no_names_Union fds :
  bound_var_fundefs fds <--> bound_var_no_names fds :|: name_in_fundefs fds.
Proof.
  induction fds as [f ft xs e|]; [|cbn; normalize_bound_var; now normalize_sets].
  cbn; normalize_bound_var; rewrite IHfds.
  rewrite Ensemble_iff_In_iff; intros arb; repeat rewrite In_or_Iff_Union; tauto.
Qed.

Fixpoint freshen_bounded_names next next' next'' next''' fds_base fds fds' fs σ σ' {struct fds} :
   (next', fs) = gensyms next (map fun_name fds_base) ->
   set_lists ![map fun_name fds_base] ![fs] σ = Some σ' ->
   name_in_fundefs ![fds] \subset name_in_fundefs ![fds_base] ->
   next'' >= next' ->
   (next''', fds') = freshen_fds next'' σ' fds ->
   name_in_fundefs ![fds'] \subset FromList ![fs].
Proof.
  intros Hgen Hset Hsub Hge Heq; destruct fds as [|[[f] [ft] xs e] fds]; cbn in *; [now inv Heq|].
  do_gensyms next'' xs next0 xs0 Hxs0 Hge_xs Hlen.
  set_lists_safe σ0 Hσ0.
  destruct (freshen_exp next0 σ0 e) as [next1 e0] eqn:He0; symmetry in He0.
  destruct (freshen_fds next1 σ' fds) as [next2 fds0] eqn:Hfds0; symmetry in Hfds0.
  inv Heq; cbn in *.
  apply Union_Included.
  - (* f ∈ fds_base ⟹ σ'(f) ∈ strip_vars fs *)
    rewrite !name_in_fundefs_FromList in Hsub; cbn in Hsub.
    apply set_lists_In_corresp with (x := f) in Hset; [|now apply Hsub].
    destruct Hset as [y [Hget Hin]].
    apply Singleton_Included; unfold apply_r.
    change (@cps.M.get cps.M.elt) with (@M.get cps.var).
    rewrite Hget; now unfold Ensembles.In, FromList.
  - specialize (freshen_bounded_names next next' next1 next2 fds_base fds fds0 fs σ σ' Hgen Hset).
    freshen_used_facts.
    assert (next1 >= next') by lia.
    apply freshen_bounded_names; auto.
    now apply Union_Included_r in Hsub.
Qed.

(* The interval [x, z) *)
Definition interval x z : Ensemble positive := fun y => x <= y < z.

(* Facts about intervals *)

Lemma interval_lower x y : x < y -> x \in interval x y.
Proof. unfold interval, Ensembles.In; lia. Qed.

Lemma interval_lower_Singleton x y : x < y -> [set x] \subset interval x y.
Proof. intros; now apply Singleton_Included, interval_lower. Qed.

Lemma Singleton_predicate {A} (x : A) : [set x] <--> (fun y => y = x).
Proof. split; intros y; unfold Ensembles.In; now inversion 1. Qed.

Lemma Disjoint_intervals x y z w :
  (forall a, ~ (x <= a < y /\ z <= a < w)) ->
  Disjoint _ (interval x y) (interval z w).
Proof.
  intros Hforall; constructor; intros arb; intros [arb' Hl Hr].
  unfold Ensembles.In, interval in *; specialize (Hforall arb'); lia.
Qed.

Ltac solve_interval :=
  rewrite ?Singleton_predicate;
  unfold interval, Included, Ensembles.In in *; cbn in *;
  intros; lia.

Ltac easy_interval :=
  solve [apply interval_lower_Singleton; lia
        |solve_interval
        |eapply Included_trans; [eassumption|easy_interval]
        |apply Union_Included; easy_interval
        ].

(* TODO: move to lemmas about intervals *)
Lemma fresher_than_bounded x S : fresher_than x S -> S \subset interval 1 x.
Proof.
  unfold fresher_than, interval, Included, Ensembles.In; intros Hgt arb HS.
  apply Hgt in HS; lia.
Qed.

Lemma gensyms_bounded {A} x (xs : list A) x' xs' :
  (x', xs') = gensyms x xs ->
  FromList ![xs'] \subset interval x x'.
Proof.
  intros; unfold Included, FromList, Ensembles.In, interval; intros arbitrary Hxs'.
  apply in_map with (f := mk_var) in Hxs'; normalize_roundtrips.
  (assert (x' > ![mk_var arbitrary]) by (eapply gensyms_upper2; eauto)); cbn in *.
  assert (![mk_var arbitrary] >= x) by (eapply gensyms_increasing'; eauto); cbn in *.
  lia.
Qed.

Lemma freshen_bounded :
  freshen_stmt
    (fun σ next e next' e' => bound_var ![e'] \subset interval next next')
    (fun σ next ces next' ces' => bound_var_ces (ces_of_proto ces') \subset interval next next')
    (fun σ next fds next' fds' => bound_var_no_names ![fds'] \subset interval next next').
Proof.
  apply freshen_ind; intros; unbox_newtypes; cbn in *; normalize_roundtrips;
    intros; freshen_used_facts; repeat normalize_bound_var;
    try rewrite bound_var_Ecase in *.
  - (* next easy, BV(e') ⊆ [next + 1, next') *)
    easy_interval.
  - apply H0.
  - rewrite bound_var_no_names_Union.
    (* BV(fds') \ names(fds') ⊆ [next', next'')
       names(fds') ⊆ fs' ⊆ [next, next') (by freshen_bounded_names)
       BV(e') ⊆ [next'', next''') *)
    assert (name_in_fundefs ![fds'] \subset FromList ![fs']). {
      eapply (freshen_bounded_names next next' next' next'' fds fds fds');
        try lia; eauto with Ensembles_DB. }
    apply gensyms_bounded in H.
    easy_interval.
  - (* next easy, BV(e') ⊆ [next + 1, next') *) easy_interval.
  - (* next easy, BV(e') ⊆ [next + 1, next') *) easy_interval.
  - inversion 1.
  - (* next easy, BV(e') ⊆ [next + 1, next') *) easy_interval.
  - inversion 1.
  - inversion 1.
  - (* xs' ⊆ [next, next')
       BV(e') ⊆ [next', next'') 
       BV(fds') \ names(fds') ⊆ [next'', next''') *)
    apply gensyms_bounded in H.
    easy_interval.
  - inversion 1.
  - (* From IHs *) easy_interval.
Qed.

Corollary freshen_exp_bounded : forall σ next e next' e',
  (next', e') = freshen_exp next σ e -> bound_var ![e'] \subset interval next next'.
Proof. apply freshen_bounded. Qed.

Corollary freshen_ces_bounded : forall σ next ces next' ces',
  (next', ces') = freshen_ces next σ ces -> bound_var_ces ![ces'] \subset interval next next'.
Proof. apply freshen_bounded. Qed.

Corollary freshen_fds_bounded : forall σ next fds next' fds',
  (next', fds') = freshen_fds next σ fds -> bound_var_no_names ![fds'] \subset interval next next'.
Proof. apply freshen_bounded. Qed.

Fixpoint unique_bindings_ces ces :=
  match ces with
  | [] => True
  | (c, e) :: ces =>
    unique_bindings e /\ Disjoint _ (bound_var e) (bound_var_ces ces)
    /\ unique_bindings_ces ces
  end.

Lemma unique_bindings_Ecase x ces : unique_bindings (cps.Ecase x ces) <-> unique_bindings_ces ces.
Proof.
  induction ces as [|[c e] ces]; [split; constructor|split; cbn; intros H].
  - inv H; rewrite <- IHces; now rewrite bound_var_Ecase in H6.
  - destruct H as [H1 [H2 H3]].
    rewrite <- IHces in H3.
    rewrite <- (bound_var_Ecase x) in H2.
    now constructor.
Qed.

Fixpoint unique_bindings_no_names fds :=
  match fds with
  | cps.Fnil => True
  | cps.Fcons f ft xs e fds =>
    NoDup xs /\ unique_bindings e /\
    Disjoint _ (bound_var e) (FromList xs) /\
    Disjoint _ (bound_var_no_names fds) (FromList xs) /\
    Disjoint _ (bound_var e) (bound_var_no_names fds) /\
    unique_bindings_no_names fds
  end.

Fixpoint unique_names fds :=
  match fds with
  | cps.Fnil => True
  | cps.Fcons f ft xs e fds => ~ f \in name_in_fundefs fds /\ unique_names fds
  end.

Lemma Decidable_bound_var_no_names fds : Decidable (bound_var_no_names fds).
Proof. induction fds as [f ft xs e fds IHfds|]; cbn; eauto with Decidable_DB. Qed.

Hint Resolve Decidable_bound_var_no_names : Decidable_DB.

Lemma unique_bindings_fundefs_decomp fds :
  unique_bindings_fundefs fds <->
  unique_bindings_no_names fds /\
  unique_names fds /\
  Disjoint _ (name_in_fundefs fds) (bound_var_no_names fds).
Proof.
  induction fds as [f ft xs e fds IHfds|]; cbn in *.
  - split; intros H.
    + inv H.
      rewrite IHfds in H13; decompose [and] H13; clear H13.
      repeat match goal with |- _ /\ _ => split end; auto.
      * eapply Disjoint_Included_l; [|eassumption].
        rewrite bound_var_no_names_Union; eauto with Ensembles_DB.
      * eapply Disjoint_Included_r; [|eassumption].
        rewrite bound_var_no_names_Union; eauto with Ensembles_DB.
      * intros Hin; apply H6; now apply name_in_fundefs_bound_var_fundefs.
      * apply Union_Disjoint_l; repeat apply Union_Disjoint_r; eauto with Ensembles_DB.
        -- apply Disjoint_Singleton_l; intros oops; contradiction H6.
           change (f \in bound_var_fundefs fds). now rewrite bound_var_no_names_Union.
        -- eapply Disjoint_Included_l; [|eassumption].
           rewrite bound_var_no_names_Union; eauto with Ensembles_DB.
        -- apply Disjoint_commut; eapply Disjoint_Included_r; [|eassumption].
           rewrite bound_var_no_names_Union; eauto with Ensembles_DB.
    + decompose [and] H; clear H.
      repeat match goal with
      | H : context [Ensembles.In] |- _ => unfold Ensembles.In in H
      | H : Disjoint _ _ (_ :|: _) |- _ => apply Disjoint_Union in H
      | H : _ /\ _ |- _ => destruct H
      | H : Disjoint _ _ [set _] |- _ => apply Disjoint_Singleton_In in H; [|now auto with Decidable_DB]
      | H : Disjoint _ (_ :|: _) _ |- _ => apply Disjoint_commut in H
      end.
      constructor; auto; try rewrite bound_var_no_names_Union; eauto with Ensembles_DB.
      * change (~ f \in bound_var_fundefs fds).
        rewrite bound_var_no_names_Union.
        rewrite Union_demorgan; split; auto.
      * rewrite IHfds; split; [|split]; auto.
        now apply Disjoint_commut.
  - split; [intros H|constructor]; split; auto; split; eauto with Ensembles_DB.
Qed.

Fixpoint freshen_fds_names next next' next'' next''' fds_base fds fds' fs σ σ' {struct fds} :
   (next', fs) = gensyms next (map fun_name fds_base) ->
   set_lists ![map fun_name fds_base] ![fs] σ = Some σ' ->
   name_in_fundefs ![fds] \subset name_in_fundefs ![fds_base] ->
   next'' >= next' ->
   (next''', fds') = freshen_fds next'' σ' fds ->
   map fun_name fds' = [map (apply_r σ') ![map fun_name fds]]!.
Proof.
  intros Hgen Hset Hsub Hge Heq; destruct fds as [|[[f] [ft] xs e] fds]; cbn in *; [now inv Heq|].
  do_gensyms next'' xs next0 xs0 Hxs0 Hge_xs Hlen.
  set_lists_safe σ0 Hσ0.
  destruct (freshen_exp next0 σ0 e) as [next1 e0] eqn:He0; symmetry in He0.
  destruct (freshen_fds next1 σ' fds) as [next2 fds0] eqn:Hfds0; symmetry in Hfds0.
  inv Heq; cbn in *; f_equal.
  specialize (freshen_fds_names next next' next1 next2 fds_base fds fds0 fs σ σ' Hgen Hset).
  freshen_used_facts.
  apply freshen_fds_names; auto; try lia.
  now apply Union_Included_r in Hsub.
Qed.

Lemma name_in_fundefs_map fds : name_in_fundefs ![fds] <--> FromList ![map fun_name fds].
Proof.
  induction fds as [|[[f] [ft] xs e] fds IHfds]; cbn in *; [now normalize_sets|].
  rewrite IHfds; now normalize_sets.
Qed.

Lemma unique_names_NoDup fds : unique_names ![fds] <-> NoDup (map fun_name fds).
Proof.
  induction fds as [|[[f] [ft] xs e] fds IHfds]; cbn in *; [split; auto; try constructor|].
  rewrite IHfds; split.
  - intros [Hin Hdup]; constructor; auto.
    rewrite name_in_fundefs_map in Hin; intros oops; contradiction Hin.
    unfold Ensembles.In, FromList.
    now apply (in_map un_var) in oops.
  - intros Hdup; inv Hdup; split; [|auto].
    rewrite name_in_fundefs_map; intros oops; contradiction H1.
    unfold Ensembles.In, FromList in oops.
    apply (in_map mk_var) in oops; now normalize_roundtrips.
Qed.

Fixpoint injective_subdomain_In {A B} S (f : A -> B) x xs :
  injective_subdomain S f ->
  x \in S ->
  FromList xs \subset S ->
  In (f x) (map f xs) ->
  In x xs.
Proof.
  destruct xs as [|x' xs]; [inversion 4|cbn; intros Hinj Hin Hsub [Hhere|Hthere]].
  - apply Hinj in Hhere; [now left|normalize_sets; eauto with Ensembles_DB|auto].
  - eapply injective_subdomain_In in Hthere; try eassumption; [now right|normalize_sets].
    eapply Included_trans; [eauto with Ensembles_DB|eassumption].
Qed.

Fixpoint NoDup_strip (xs : list var) : NoDup xs -> NoDup ![xs].
Proof.
  destruct xs as [|[x] xs]; [constructor|cbn; intros Hdup; inv Hdup; constructor; auto].
  intros Hoops; apply in_map with (f := mk_var) in Hoops;  now normalize_roundtrips.
Qed.

Fixpoint freshen_NoDup next next' next'' fds_base fds fs σ σ' :
  (next', fs) = gensyms next (map fun_name fds_base) ->
  set_lists ![map fun_name fds_base] ![fs] σ = Some σ' ->
  name_in_fundefs ![fds] \subset name_in_fundefs ![fds_base] ->
  next'' >= next' ->
  NoDup (map fun_name fds) ->
  NoDup [map (apply_r σ') ![map fun_name fds]]!.
Proof.
  destruct fds as [|[[f] [ft] xs e] fds]; [constructor|].
  intros Hgen Hset Hsub Hge; cbn; intros Hdup; inv Hdup; constructor.
  - intros Hoops; apply in_map with (f := un_var) in Hoops; cbn in Hoops.
    change (map un_var) with strip_vars in Hoops; normalize_roundtrips.
    apply injective_subdomain_In with (S := name_in_fundefs ![fds_base]) in Hoops.
    + apply in_map with (f := mk_var) in Hoops; now normalize_roundtrips.
    + rewrite name_in_fundefs_FromList; eapply set_NoDup_inj; eauto.
      apply NoDup_strip; eapply gensyms_NoDup'; eauto.
    + cbn in Hsub; eauto with Ensembles_DB.
    + cbn in Hsub; eapply Included_trans; [|eassumption].
      rewrite name_in_fundefs_FromList; eauto with Ensembles_DB.
  - eapply freshen_NoDup; eauto.
    cbn in Hsub; eapply Included_trans; eauto with Ensembles_DB.
Qed.

Definition freshen_uniq_names next next' next'' next''' fds_base fds fds' fs σ σ' :
  (next', fs) = gensyms next (map fun_name fds_base) ->
  set_lists ![map fun_name fds_base] ![fs] σ = Some σ' ->
  name_in_fundefs ![fds] \subset name_in_fundefs ![fds_base] ->
  next'' >= next' ->
  unique_names ![fds] ->
  (next''', fds') = freshen_fds next'' σ' fds ->
  unique_names ![fds'].
Proof.
  intros Hgen Hset Hsub Hge Huniq Heq.
  rewrite unique_names_NoDup; rewrite unique_names_NoDup in Huniq.
  erewrite freshen_fds_names; eauto; cbn.
  eapply freshen_NoDup; eassumption.
Qed.

Ltac BV_oob :=
  match goal with
  | H : bound_var ?S \subset interval ?l ?r |- ~ bound_var ?S ?x =>
    let Hoops := fresh "Hoops" in intros Hoops;
    let Hoops' := fresh "Hoops" in
    (assert (Hoops' : [set x] \subset interval l r)
      by (eapply Included_trans; [|eassumption]; apply Singleton_Included, Hoops));
    rewrite ?Singleton_predicate in Hoops';
    unfold interval, Included, Ensembles.In in Hoops';
    specialize (Hoops' x); lia
  end.

Lemma freshen_uniq :
  freshen_stmt
    (fun σ next e next' e' => unique_bindings ![e] -> unique_bindings ![e'])
    (fun σ next ces next' ces' => unique_bindings_ces ![ces] -> unique_bindings_ces ![ces'])
    (fun σ next fds next' fds' =>
      unique_bindings_no_names ![fds] -> unique_bindings_no_names ![fds']).
Proof.
  apply freshen_ind; intros; unbox_newtypes; cbn in *; normalize_roundtrips.
  - repeat lazymatch goal with H : unique_bindings (_ _ _) |- _ => inv H end.
    constructor; auto.
    (* BV(e') ⊆ [next + 1, next') and next < next + 1 *)
    apply freshen_exp_bounded in H; cbn in H; BV_oob.
  - rewrite unique_bindings_Ecase in *; auto.
  - repeat lazymatch goal with H : unique_bindings (_ _ _) |- _ => inv H end.
    assert (name_in_fundefs ![fds'] \subset FromList ![fs'])
      by (eapply freshen_bounded_names; try eassumption; try lia; eauto with Ensembles_DB).
    assert (Hnext1 : next' >= next) by (eapply gensyms_upper1; eauto).
    assert (Hnext2 : next'' >= next') by (eapply freshen_fds_increasing; eassumption).
    assert (Hnext3 : next''' >= next'') by (eapply freshen_exp_increasing; eassumption).
    constructor; auto; change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.
    + rewrite unique_bindings_fundefs_decomp; split; [|split].
      * rewrite unique_bindings_fundefs_decomp in H9; intuition.
      * clear Hnext1 Hnext2 Hnext3; eapply freshen_uniq_names; eauto with Ensembles_DB; try lia.
        rewrite unique_bindings_fundefs_decomp in H9; intuition.
      * (* names(fds') ⊆ fs' ⊆ [next, next') by freshen_bounded_names 
           (BV(fds') \ names(fds')) ⊆ [next', next'') by freshen_fds_bounded *)
        eapply Disjoint_Included_l; [eassumption|].
        eapply Disjoint_Included_l; [eapply gensyms_bounded; eassumption|].
        eapply Disjoint_Included_r; [eapply freshen_fds_bounded; eassumption|].
        apply Disjoint_intervals; intros arb; lia.
    + clear H2.
      (* BV(fds') ⊆ [next, next'') and BV(e') ⊆ [next'', next''') *)
      rewrite bound_var_no_names_Union.
      eapply Disjoint_Included_l; [eapply freshen_exp_bounded; eassumption|].
      eapply Union_Disjoint_r.
      * eapply Disjoint_Included_r; [eapply freshen_fds_bounded; eassumption|].
        apply Disjoint_intervals; intros arb; lia.
      * rewrite name_in_fundefs_FromList in *.
        eapply Disjoint_Included_r. {
          eapply Included_trans; [eassumption|].
          eapply gensyms_bounded; eassumption. }
        apply Disjoint_intervals; intros arb; lia.
  - repeat lazymatch goal with H : unique_bindings (_ _ _) |- _ => inv H end.
    constructor; auto.
    (* BV(e') ⊆ [next + 1, next') and next < next + 1 *)
    apply freshen_exp_bounded in H; cbn in H; BV_oob.
  - repeat lazymatch goal with H : unique_bindings (_ _ _) |- _ => inv H end.
    constructor; auto.
    (* BV(e') ⊆ [next + 1, next') and next < next + 1 *)
    apply freshen_exp_bounded in H; cbn in H; BV_oob.
  - constructor.
  - repeat lazymatch goal with H : unique_bindings (_ _ _) |- _ => inv H end.
    constructor; auto.
    (* BV(e') ⊆ [next + 1, next') and next < next + 1 *)
    apply freshen_exp_bounded in H; cbn in H; BV_oob.
  - constructor.
  - constructor.
  - repeat lazymatch goal with H : unique_bindings_fundefs (_ _ _) |- _ => inv H end.
    assert (Hnext1 : next' >= next) by (eapply gensyms_upper1; eauto).
    assert (Hnext2 : next'' >= next') by (eapply freshen_exp_increasing; eassumption).
    assert (Hnext3 : next''' >= next'') by (eapply freshen_fds_increasing; eassumption).
    decompose [and] H5.
    repeat match goal with |- _ /\ _ => split; auto end.
    + (* xs' was gensym'd *) apply NoDup_strip; eapply gensyms_NoDup'; eauto.
    + (* BV(e') ⊆ [next', next'') and xs' ⊆ [next, next') *)
      eapply Disjoint_Included_l; [eapply freshen_exp_bounded; eassumption|].
      eapply Disjoint_Included_r; [eapply gensyms_bounded; eassumption|].
      apply Disjoint_intervals; intros arb; lia.
    + (* (BV(fds') \ names(fds')) ⊆ [next'', next''') and xs' ⊆ [next, next') *)
      eapply Disjoint_Included_l; [eapply freshen_fds_bounded; eassumption|].
      eapply Disjoint_Included_r; [eapply gensyms_bounded; eassumption|].
      apply Disjoint_intervals; intros arb; lia.
    + (* BV(e') ⊆ [next', next'') and (BV(fds') \ names(fds')) ⊆ [next'', next''') *)
      eapply Disjoint_Included_l; [eapply freshen_exp_bounded; eassumption|].
      eapply Disjoint_Included_r; [eapply freshen_fds_bounded; eassumption|].
      apply Disjoint_intervals; intros arb; lia.
  - constructor.
  - repeat lazymatch goal with H : _ /\ _ |- _ => inv H end.
    repeat lazymatch goal with |- _ /\ _ => split end; auto.
    (* BV(e') ⊆ [next, next') and BV(ces') ⊆ [next', next'') *)
    assert (next' >= next) by (eapply freshen_exp_increasing; eauto).
    assert (next'' >= next') by (eapply freshen_ces_increasing; eauto).
    eapply Disjoint_Included_l; [eapply freshen_exp_bounded; eassumption|].
    eapply Disjoint_Included_r; [eapply freshen_ces_bounded; eassumption|].
    apply Disjoint_intervals; intros arb; lia.
Qed.

Corollary freshen_exp_uniq : forall σ next e next' e',
  (next', e') = freshen_exp next σ e -> unique_bindings ![e] -> unique_bindings ![e'].
Proof. apply freshen_uniq. Qed.

Corollary freshen_ces_uniq : forall σ next ces next' ces',
  (next', ces') = freshen_ces next σ ces ->
  unique_bindings_ces ![ces] -> unique_bindings_ces ![ces'].
Proof. apply freshen_uniq. Qed.

Corollary freshen_fds_uniq : forall σ next fds next' fds',
  (next', fds') = freshen_fds next σ fds ->
  unique_bindings_no_names ![fds] -> unique_bindings_no_names ![fds'].
Proof. apply freshen_uniq. Qed.

Lemma map_ext_eq {A B} xs : forall (f g : A -> B) (Heq : forall x, In x xs -> f x = g x), map f xs = map g xs.
Proof.
  induction xs; auto; intros; cbn; (rewrite Heq by now left); f_equal; erewrite IHxs; eauto.
  intros; eapply Heq; now right.
Qed.

Fixpoint set_lists_map_apply_r xs ys σ σ' {struct xs} :
  NoDup xs ->
  set_lists xs ys σ = Some σ' ->
  map (apply_r σ') xs = ys.
Proof.
  destruct xs as [|x xs], ys as [|y ys]; unbox_newtypes; cbn; try congruence.
  destruct (set_lists _ _ _) as [σ0|] eqn:Hσ; [|congruence]; intros Hdup Heq; inv Heq; inv Hdup.
  unfold apply_r at 1; rewrite M.gss; f_equal.
  rewrite map_ext_eq with (g := apply_r σ0); [now eapply set_lists_map_apply_r|].
  intros x' Hin; assert (x <> x') by (intros Hoops; now subst); unfold apply_r; now rewrite M.gso by auto.
Qed.

Lemma Alpha_conv_cons x1 x2 e1 e2 c1 c2 ces1 ces2 σ :
  c1 = c2 ->
  Alpha_conv e1 e2 σ ->
  Alpha_conv (cps.Ecase x1 ces1) (cps.Ecase x2 ces2) σ ->
  Alpha_conv (cps.Ecase x1 ((c1, e1) :: ces1)) (cps.Ecase x2 ((c2, e2) :: ces2)) σ.
Proof. intros Hc He Hces; inv Hces; constructor; auto. Qed.

Definition Alpha_conv_ces (ces1 ces2 : list (cps.ctor_tag * cps.exp)) σ :=
  Forall2 (fun ce1 ce2 => fst ce1 = fst ce2 /\ Alpha_conv (snd ce1) (snd ce2) σ) ces1 ces2.

Fixpoint Alpha_conv_names fds1 fds2 σ :=
  match fds1, fds2 with
  | cps.Fnil, cps.Fnil => True
  | cps.Fcons f1 ft1 xs1 e1 fds1, cps.Fcons f2 ft2 xs2 e2 fds2 =>
    f2 = σ f1 /\ Alpha_conv_names fds1 fds2 σ
  | _, _ => False
  end.

Fixpoint Alpha_conv_no_names fds1 fds2 σ :=
  match fds1, fds2 with
  | cps.Fnil, cps.Fnil => True
  | cps.Fcons f1 ft1 xs1 e1 fds1, cps.Fcons f2 ft2 xs2 e2 fds2 => exists σ',
    ft1 = ft2 /\ 
    Alpha_conv_no_names fds1 fds2 σ /\
    Disjoint _ (FromList xs2) (image σ (occurs_free e1) :|: bound_var e1) /\
    construct_lst_injection σ xs1 xs2 σ' /\
    Alpha_conv e1 e2 σ'
  | _, _ => False
  end.

Fixpoint Alpha_conv_fundefs_decomp fds1 fds2 σ {struct fds1} :
  Alpha_conv_fundefs fds1 fds2 σ <->
  Alpha_conv_names fds1 fds2 σ /\ Alpha_conv_no_names fds1 fds2 σ.
Proof.
  destruct fds1 as [f1 ft1 xs1 e1 fds1|], fds2 as [f2 ft2 xs2 e2 fds2|]; cbn.
  - split; intros H.
    + inv H.
      rewrite Alpha_conv_fundefs_decomp in H12; destruct H12.
      repeat match goal with |- _ /\ _ => split; auto | |- exists _, _ => eexists; eauto end.
    + decompose [and] H; clear H; destruct H1 as [? Hex]; decompose [and] Hex; clear Hex; subst.
      econstructor; eauto.
      rewrite Alpha_conv_fundefs_decomp; split; auto.
  - split; try inversion 1; easy.
  - split; try inversion 1; easy.
  - split; try constructor; easy.
Qed.

Fixpoint freshen_Alpha_names next next' next'' next''' fds_base fds fds' fs σ σ' {struct fds} :
  (next', fs) = gensyms next (map fun_name fds_base) ->
  set_lists ![map fun_name fds_base] ![fs] σ = Some σ' ->
  name_in_fundefs ![fds] \subset name_in_fundefs ![fds_base] ->
  next'' >= next' ->
  (next''', fds') = freshen_fds next'' σ' fds ->
  Alpha_conv_names ![fds] ![fds'] (apply_r σ').
Proof.
  intros Hgen Hset Hsub Hge Heq.
  destruct fds as [|[[f] [ft] xs e] fds]; cbn in *; [now inv Heq|].
  do_gensyms next'' xs next0 xs0 Hxs0 Hge_xs Hlen.
  set_lists_safe σ0 Hσ0.
  destruct (freshen_exp next0 σ0 e) as [next1 e0] eqn:He0; symmetry in He0.
  destruct (freshen_fds next1 σ' fds) as [next2 fds0] eqn:Hfds0; symmetry in Hfds0.
  inv Heq; cbn in *; split; [auto|].
  freshen_used_facts.
  specialize (freshen_Alpha_names next next' next1 next2 fds_base fds fds0 fs σ σ' Hgen Hset).
  apply freshen_Alpha_names; auto; try lia.
  now apply Union_Included_r in Hsub.
Qed.

Lemma notin_apply_r_set x y xs σ :
  ~ In x xs ->
  map (apply_r (M.set x y σ)) xs = map (apply_r σ) xs.
Proof.
  induction xs; auto; cbn; intros Hnotin.
  apply Decidable.not_or in Hnotin.
  destruct Hnotin as [Hne Hnotin].
  rewrite IHxs; auto.
  unfold apply_r; rewrite M.gso; auto.
Qed.

Fixpoint NoDup_construct_fundefs_injection σ σ' fs fds fds' {struct fds} :
  NoDup (map fun_name fds) -> NoDup fs ->
  Disjoint _ (FromList ![map fun_name fds]) (FromList ![fs]) ->
  set_lists ![map fun_name fds] ![fs] σ = Some σ' ->
  ![map fun_name fds'] = map (apply_r σ') ![map fun_name fds] ->
  construct_fundefs_injection (apply_r σ) ![fds] ![fds'] (apply_r σ').
Proof.
  intros Hdup Hdup_fs Hdis Hset Hnames.
  assert (Hlen : length ![map fun_name fds] = length ![fs]) by now eapply set_lists_length_eq.
  assert (Hinj : injective_subdomain (name_in_fundefs ![fds]) (apply_r σ')). {
    rewrite name_in_fundefs_FromList.
    eapply set_NoDup_inj; eauto.
    now apply NoDup_var. }
  destruct fds as [|[[f] [ft] xs e] fds], fds' as [|[[f'] [ft'] xs' e'] fds']; try inv Hnames.
  - destruct fs; try inv Hlen; inv Hset; constructor.
  - destruct fs as [|[f'] fs']; try inv Hlen; cbn in *.
    match type of Hset with
    | match ?e with _ => _ end = _ =>
      destruct e as [σ0|] eqn:Hσ0; inv Hset
    end.
    assert (Heq : (apply_r (@map_util.M.set cps.M.elt f f' σ0)) = (apply_r σ0) {f ~> f'}). {
      apply FunctionalExtensionality.functional_extensionality.
      intros; now rewrite apply_r_set. }
    assert (Hf : apply_r (@map_util.M.set cps.M.elt f f' σ0) f = f') by (unfold apply_r; now rewrite M.gss).
    rewrite Hf, Heq; constructor.
    + inv Hdup; inv Hdup_fs.
      specialize (NoDup_construct_fundefs_injection σ σ0 fs' fds fds').
      apply NoDup_construct_fundefs_injection; auto.
      * repeat normalize_sets.
        apply Disjoint_Union_r in Hdis.
        apply Disjoint_Union in Hdis; now destruct Hdis.
      * (* f ∉ fds ==> σ[f ↦ f'] fds = σ fds *)
        rewrite H1.
        assert (~ In f ![map fun_name fds]). {
          intros Hin.
          apply in_map with (f := mk_var) in Hin; now normalize_roundtrips. }
        now rewrite notin_apply_r_set by auto.
    + now rewrite apply_r_set.
Qed.

Lemma set_lists_image xs ys S σ σ' :
  set_lists xs ys σ = Some σ' ->
  image (apply_r σ') S \subset FromList ys :|: image (apply_r σ) S.
Proof.
  intros Hset arb [x [HS Hσx]].
  assert (Hin : Decidable.decidable (In x xs)). {
    apply ListDec.In_decidable; unfold ListDec.decidable_eq.
    intros x' y' ; destruct (Pos.eq_dec x' y'); [left|right]; auto. }
  destruct Hin as [Hin|Hnotin].
  - eapply set_lists_In_corresp in Hin; eauto.
    destruct Hin as [y [Hget Hyin]].
    unfold apply_r in Hσx; rewrite Hget in Hσx; subst arb; now left.
  - unfold apply_r in Hσx.
    erewrite <- set_lists_not_In in Hσx; eauto.
    match type of Hσx with ?lhs = _ => change lhs with (apply_r σ x) in Hσx end.
    right; unfold Ensembles.In, image; eexists; split; eauto.
Qed.

Lemma freshen_Alpha :
  freshen_stmt
    (fun σ next e next' e' =>
      unique_bindings ![e] ->
      fresher_than next (used_vars ![e] :|: image (apply_r σ) (used_vars ![e])) ->
      Alpha_conv ![e] ![e'] (apply_r σ))
    (fun σ next ces next' ces' =>
      unique_bindings_ces ![ces] ->
      fresher_than next (used_vars_ces ![ces] :|: image (apply_r σ) (used_vars_ces ![ces])) ->
      Alpha_conv_ces ![ces] ![ces'] (apply_r σ))
    (fun σ next fds next' fds' =>
      unique_bindings_no_names ![fds] ->
      fresher_than next (used_vars_fundefs ![fds] :|: image (apply_r σ) (used_vars_fundefs ![fds])) ->
      Alpha_conv_no_names ![fds] ![fds'] (apply_r σ)).
Proof.
  apply freshen_ind; intros; unbox_newtypes; cbn in *; normalize_roundtrips.
  Local Ltac easy_case H0 H1 :=
    normalize_images; constructor; auto; try solve_easy;
    rewrite apply_r_set; apply H0; try solve_easy; now inv H1.
  - easy_case H0 H1.
  - normalize_images; constructor; auto; try solve_easy.
    apply H0; try solve_easy.
    change (ces_of_proto' exp_of_proto) with ces_of_proto in *.
    inv H1; try constructor; auto.
    rewrite bound_var_Ecase in H10.
    rewrite unique_bindings_Ecase in H8.
    now split.
  - change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto in *.
    apply Alpha_Efun with (f' := apply_r σ'); try solve_easy.
    + (* names(fds') = fs' ⊆ [next, next')
         next is fresher than σ(FV(Efun fds e)) ∪ BV(Efun fds e) *)
      eapply Disjoint_Included_l; [eapply freshen_bounded_names; eauto with Ensembles_DB; try lia|].
      apply gensyms_bounded in H.
      eapply Disjoint_Included_l; [eassumption|].
      unfold used_vars, used_vars_fundefs in *. normalize_images.
      repeat match goal with H : fresher_than _ _ |- _ => apply fresher_than_bounded in H end.
      apply Union_Disjoint_r; (eapply Disjoint_Included_r; [eassumption|]; apply Disjoint_intervals; lia).
    + inv H5.
      rewrite unique_bindings_fundefs_decomp in H10.
      decompose [and] H10; clear H10.
      rewrite unique_names_NoDup in H8.
      (* NoDup fds and NoDup fs' ==> σ' is a bijection ==> can construct fundefs injection.
         NB: just an injection is not enough because construct_fundefs_injection starts with
         σ and builds bindings up as it goes along. This means that if fds contains duplicates
         then fds' <> map (apply_r σ) fds. *)
      apply NoDup_construct_fundefs_injection with (fs := fs'); auto.
      * eapply gensyms_NoDup'; eauto.
      * apply gensyms_bounded in H.
        rewrite <- name_in_fundefs_FromList.
        eapply Disjoint_Included_r; [eassumption|].
        normalize_images; unfold used_vars_fundefs in *; normalize_images.
        repeat match goal with H : fresher_than _ _ |- _ => apply fresher_than_bounded in H end.
        eapply Disjoint_Included_l; [apply name_in_fundefs_bound_var_fundefs|].
        eapply Disjoint_Included_l; [eassumption|].
        eapply Disjoint_intervals; lia.
      * erewrite freshen_fds_names; eauto with Ensembles_DB; try lia.
        now normalize_roundtrips.
    + rewrite Alpha_conv_fundefs_decomp; split.
      * eapply freshen_Alpha_names; eauto with Ensembles_DB; lia.
      * apply H2. { inv H5. now rewrite unique_bindings_fundefs_decomp in H10. }
        normalize_images.
        assert (next' >= next) by (eapply gensyms_upper1; eauto).
        assert (next'' >= next') by (eapply freshen_fds_increasing; eauto).
        assert (next''' >= next'') by (eapply freshen_exp_increasing; eauto).
        apply fresher_than_Union; [solve_easy|].
        (* σ'(x) is either in fs' or in σ. 
           If in fs', next' fresher than fs'.
           If in σ, next' ≥ next and next fresher than σ(vars(fds)). *)
        eapply fresher_than_antimon; [eapply set_lists_image; eauto|].
        apply fresher_than_Union; [|solve_easy].
        apply gensyms_bounded in H.
        eapply fresher_than_antimon; [eassumption|].
        unfold fresher_than; easy_interval.
    + apply H4; [now inv H5|]; auto.
      (* Same argument as in previous subcase + the fact that next'' ≥ next'. *)
      normalize_images.
      assert (next' >= next) by (eapply gensyms_upper1; eauto).
      assert (next'' >= next') by (eapply freshen_fds_increasing; eauto).
      assert (next''' >= next'') by (eapply freshen_exp_increasing; eauto).
      apply fresher_than_Union; [solve_easy|].
      eapply fresher_than_antimon; [eapply set_lists_image; eauto|].
      apply fresher_than_Union; [|solve_easy].
      apply gensyms_bounded in H.
      eapply fresher_than_antimon; [eassumption|].
      unfold fresher_than; easy_interval.
  - easy_case H0 H1.
  - easy_case H0 H1. 
  - constructor; auto; try solve_easy.
  - easy_case H0 H1.
  - constructor; auto; try solve_easy.
  - constructor; auto; try solve_easy.
  - decompose [and] H5; clear H5.
    normalize_images; freshen_used_facts.
    exists (apply_r σ'); repeat match goal with |- _ /\ _ => split end; auto.
    + apply H4; auto. solve_easy.
    + unfold used_vars in *; normalize_images.
      repeat match goal with H : fresher_than _ _ |- _ => apply fresher_than_bounded in H end.
      apply Union_Disjoint_r.
      * (* xs' ⊆ [next, next') and next fresher than σ(FV(e)) *)
        apply gensyms_bounded in H.
        eapply Disjoint_Included_l; [eassumption|].
        eapply Disjoint_Included_r; [eassumption|].
        apply Disjoint_intervals; lia.
      * (* xs' ⊆ [next, next') and next fresher than BV(e) *)
        apply gensyms_bounded in H.
        eapply Disjoint_Included_l; [eassumption|].
        eapply Disjoint_Included_r; [eassumption|].
        apply Disjoint_intervals; lia.
    + eapply set_gensyms_inj; eauto.
    + apply H2; auto.
      apply fresher_than_Union; [solve_easy|].
      (* σ'(x) is either in xs' or in σ.
         If in xs', next' fresher than xs'
         If in σ, next' fresher than σ(vars(e)). *)
      eapply fresher_than_antimon; [eapply set_lists_image; eauto|].
      apply fresher_than_Union; [|solve_easy].
       apply gensyms_bounded in H.
       eapply fresher_than_antimon; [eassumption|].
       unfold fresher_than; easy_interval.
  - constructor; auto; try solve_easy.
  - decompose [and] H3; clear H3; normalize_images.
    assert (next' >= next) by (eapply freshen_exp_increasing; eauto).
    assert (next'' >= next') by (eapply freshen_ces_increasing; eauto).
    constructor; cbn.
    + split; auto; apply H0; auto; solve_easy.
    + apply H2; auto; solve_easy.
Qed.

Corollary freshen_exp_Alpha : forall σ next e next' e',
  (next', e') = freshen_exp next σ e ->
  unique_bindings ![e] ->
  fresher_than next (used_vars ![e] :|: image (apply_r σ) (used_vars ![e])) ->
  Alpha_conv ![e] ![e'] (apply_r σ).
Proof. apply freshen_Alpha. Qed.

(** * Inlining as a relation *)

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
(* Inlining for CPS *)
| inline_cps :
  forall (C : frames_t exp_univ_exp exp_univ_exp) f ft ft' (xs : list var) e e' e'' (ys : list var)
    lhs σ,
  lhs = Eapp f ft ys /\
  known_function f ft xs e C lhs /\
  Alpha_conv ![e] ![e'] id /\
  unique_bindings ![e'] /\
  Disjoint _ (used_vars ![C ⟦ e ⟧]) (bound_var ![e']) /\
  set_lists ![xs] ![ys] (M.empty _) = Some σ /\
  e'' = rename_all' σ e' ->
  inline_step
    (C ⟦ Eapp f ft' ys ⟧)
    (C ⟦ Rec e'' ⟧).

(* Maintain map of known functions while traversing *)
Definition S_fns {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := {
  ρ : fun_map |
  forall f ft xs e_body, M.get f ρ = Some (ft, xs, e_body) ->
  known_function [f]! ft xs e_body C e }.

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

(* Inlining heuristic is a piece of state *)
Record S_IH {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := mk_IH {un_IH : InlineHeuristic}.

(* Though inlining heuristics don't have any nontrivial invariants, the Preserves_R
    instance must make calls to update_* methods in the proper places. *)
Instance Preserves_S_S_IH : Preserves_S _ exp_univ_exp (@S_IH).
Proof.
  constructor; intros A B C f x [IH].
  - (* No change on the way back up *) constructor; exact IH.
  - (* Update the heuristic on the way down *)
    destruct f;
    match goal with
    | |- S_IH (C >:: Efun0 ?e) ?fds => constructor; exact (IH.(update_funDef1) fds e)
    | |- S_IH (C >:: Efun1 ?fds) ?e => constructor; exact (IH.(update_funDef2) fds e)
    | |- S_IH (C >:: Ffun3 ?f ?ft ?xs) ?e => constructor; exact (IH.(update_inFun) f ft xs e)
    | |- _ => constructor; exact IH
    end.
Defined.

Definition S_inline : forall {A}, exp_c A exp_univ_exp -> univD A -> Set :=
  S_prod (S_prod (S_prod (S_prod (S_plain comp_data) (@S_IH)) (@S_fresh)) (@S_fns)) (@S_uniq).

Require Import Coq.Strings.String.

(** * Inlining as a recursive function *)

Definition log_msg s cdata :=
  let '{| next_var := x; nect_ctor_tag := c; next_ind_tag := t; next_fun_tag := ft;
          cenv := cenv; fenv := fenv; nenv := nenv; log := log |} := cdata in
  mkCompData x c t ft cenv fenv nenv (s :: log).

Fixpoint In_ctx f ft xs e fds :
  In (Ffun f ft xs e) fds ->
  exists (C : frames_t exp_univ_exp exp_univ_list_fundef), fds = C ⟦ e ⟧.
Proof.
  destruct fds as [|[f' ft' xs' e'] fds]; [inversion 1|intros Hin; inv Hin].
  - exists <[cons_fundef0 fds; Ffun3 f' ft' xs']>; now cbn.
  - destruct (In_ctx f ft xs e fds H) as [C HC].
    exists (<[cons_fundef1 (Ffun f' ft' xs' e')]> >++ C); subst fds; rewrite frames_compose_law; now cbn.
Qed.

Lemma known_in_ctx f ft xs e (C : frames_t exp_univ_exp _) lhs :
  known_function f ft xs e C lhs ->
  exists (D : frames_t exp_univ_exp _), C ⟦ lhs ⟧ = D ⟦ e ⟧.
Proof.
  unfold known_function.
  intros [[D [fds [E [Heq Hin]]]] | [[D [fds1 [fds2 [E [Heq Hin]]]]] | []]].
  - subst C; repeat rewrite frames_compose_law; cbn.
    apply In_ctx in Hin; destruct Hin as [C HC]; subst fds.
    exists (D >++ <[Efun0 (E ⟦ lhs ⟧)]> >++ C); rewrite !frames_compose_law; now cbn.
  - subst C; rewrite !frames_compose_law; cbn.
    assert (Hin' : In (Ffun f ft xs e) (rev fds1 ++ E ⟦ lhs ⟧ :: fds2)). {
      apply in_app_or in Hin.
      destruct Hin as [Hfds1|Hfds2]; apply in_or_app; [|right; now right].
      left; apply in_rev; now rewrite rev_involutive. }
    rewrite frames_compose_law with (fs := D).
    rewrite ctx_of_fds_app.
    apply In_ctx in Hin'; cbn in Hin'; destruct Hin' as [C HC].
    rewrite HC; exists (D >++ C); now rewrite frames_compose_law.
Qed.

Definition rw_inline' : rewriter exp_univ_exp inline_step
  trivial_delay_t trivial_R_C (@S_inline).
Proof.
  mk_rw; mk_easy_delay.
  (* To actually perform inlining, we need to check the heuristic, do the renaming, etc. *)
  - clear; unfold trivial_delay_t, delayD, Delayed_trivial_delay_t in *.
    intros _ R C f ft' ys _ _ [[[[cdata [IH]] [fresh Hfresh]] [ρ Hρ]] Huniq] success failure.
    (* Look up f in the map of known functions *)
    destruct (M.get ![f] ρ) as [[[ft xs] e]|] eqn:Hget; [|cond_failure].
    pose (Hρ' := Hρ); clearbody Hρ'.
    specialize (Hρ ![f] ft xs e Hget).
    specialize success with (ft := ft) (xs := xs) (e := e).
    (* Check the heuristic *)
    destruct (decide_App IH f ft ys) eqn:Hdec; [|cond_failure].
    (* Do the freshening + renaming.
       Ideally, we wouldn't actually call [rename_all], which makes an extra pass over the
       function body. Instead, we could pass σ into freshen_exp as the initial renaming. This
       works as long as FV(e) ∩ BV(e) = ∅ (so the mapping [xs ↦ ys] never overlaps with future
       updates to σ). *)
    destruct (set_lists ![xs] ![ys] (M.empty _)) as [σ|] eqn:Hσ; [|cond_failure].
    replace [![f]]! with f in Hρ by now unbox_newtypes.
    destruct (freshen_exp fresh (M.empty _) e) as [fresh' e'] eqn:Hfreshen; symmetry in Hfreshen.
    specialize success with (e' := e') (σ := σ).
    (* Prove that we did what we said we did *)
    cond_success success; eapply success; [..|reflexivity| |]; [exact tt|..];
      repeat match goal with |- _ /\ _ => split end; eauto.
    + assert (Hid : f_eq id (apply_r (M.empty _))). {
        unfold f_eq, apply_r; intros x; now rewrite M.gempty. }
      rewrite Hid; eapply freshen_exp_Alpha; eauto.
      * (* for every known function (ft, xs, e), exists D s.t. C[f(ys)] = D[e].
           then UB(D[e]) ==> UB e by ub_app_ctx_f *)
        apply known_in_ctx in Hρ; destruct Hρ as [D HD].
        unfold S_uniq in Huniq; rewrite HD, app_exp_c_eq, isoBAB in Huniq.
        now apply ub_app_ctx_f in Huniq.
      * rewrite <- Hid, image_id, Union_idempotent.
        (* fresh > C[f(ys)] = D[e] for some D and then vars(D[e]) ⊇ vars(e) *)
        apply known_in_ctx in Hρ; destruct Hρ as [D HD].
        match type of Hfresh with
        | fresher_than fresh (used_vars ![?e]) => change (used_vars ![e]) with (used e) in Hfresh
        end.
        rewrite HD, used_app in Hfresh.
        eapply fresher_than_antimon; [|apply Hfresh]; eauto with Ensembles_DB.
    + eapply freshen_exp_uniq; eauto.
      (* UB(C[f(ys)] ==> UB(D[e]) ==> UB(e) by ub_app_ctx_f *)
      apply known_in_ctx in Hρ; destruct Hρ as [D HD].
      unfold S_uniq in Huniq; rewrite HD, app_exp_c_eq, isoBAB in Huniq.
      now apply ub_app_ctx_f in Huniq.
    + (* BV(e') ⊆ [fresh, fresh') by freshen_exp_bounded and fresh > vars(C[e]) *)
      apply known_in_ctx in Hρ; destruct Hρ as [D HD].
      apply fresher_than_bounded in Hfresh.
      apply freshen_exp_bounded in Hfreshen.
      change (used_vars ![?e]) with (used e); rewrite used_app.
      eapply Disjoint_Included_r; [eassumption|].
      apply Union_Disjoint_l.
      * change (used_vars ![?e]) with (used e) in Hfresh; rewrite used_app in Hfresh.
        eapply Disjoint_Included_l; [eapply Included_Union_l|].
        eapply Disjoint_Included_l; [eassumption|].
        apply Disjoint_intervals; lia.
      * change (used_vars ![?e]) with (used e) in Hfresh; rewrite HD, used_app in Hfresh.
        eapply Disjoint_Included_l; [eapply Included_Union_r|].
        eapply Disjoint_Included_l; [eassumption|].
        apply Disjoint_intervals; lia.
    + constructor.
    (* We must explain how to maintain all the intermediate state variables across the edit *)
    + unfold trivial_delay_t, delayD, Delayed_trivial_delay_t in *.
      split; [split; [split; [split|]|]|]; unfold S_plain, S_fresh, S_fns, S_uniq.
      * (* Need to set fresh variable in cdata properly for future passes.
           Though we don't use it, later passes do. *)
        exact (update_next_var fresh' cdata).
      * (* Update the inlining heuristic *)
        constructor; exact (IH.(update_App) f ft ys).
      * (* fresh' is a sufficiently fresh variable *)
        exists fresh'.
        (* first need to show used_vars (rename_all σ e) ⊆ used_vars e ∪ image σ (used_vars e). then have 
             vars(C[rename_all σ e'])
             = vars(C) ∪ vars(rename_all σ e')
             ⊆ vars(C) ∪ used_vars e' ∪ image σ (used_vars e)
             = vars(C) ∪ used_vars e' ∪ ys
             ⊆ vars(C) ∪ used_vars e' ∪ vars(C[f(ys)])
             = used_vars e' ∪ vars(C[f(ys)])
             < fresh' *)
        change (used_vars ![?e]) with (used e); rewrite used_app; apply fresher_than_Union.
        -- assert (fresh' >= fresh) by (eapply freshen_exp_increasing; eauto).
           eapply fresher_than_monotonic; [eassumption|].
           eapply fresher_than_antimon; [|eassumption].
           change (used_vars ![?e]) with (used e); rewrite used_app; eauto with Ensembles_DB.
        -- unfold Rec; eapply fresher_than_antimon; [apply rename_all_used|].
           apply fresher_than_Union.
           ++ eapply freshen_exp_used; try eassumption.
              assert (Hid : f_eq (apply_r (M.empty cps.var)) id) by (intros x; apply apply_r_empty).
              rewrite Hid, image_id, Union_idempotent.
              apply known_in_ctx in Hρ; destruct Hρ as [D HD].
              rewrite HD in Hfresh; eapply fresher_than_antimon; [|eassumption].
              change (used_vars ![D ⟦ e ⟧]) with (used (D ⟦ e ⟧)); rewrite used_app; eauto with Ensembles_DB.
           ++ eapply fresher_than_antimon; [eapply set_lists_image''; eauto|].
              rewrite empty_image; normalize_sets.
              assert (fresh' >= fresh) by (eapply freshen_exp_increasing; eauto).
              eapply fresher_than_monotonic; [eassumption|].
              eapply fresher_than_antimon; [|eassumption].
              change (used_vars ![?e]) with (used e); rewrite used_app.
              unbox_newtypes; cbn; normalize_used_vars; eauto with Ensembles_DB.
      * (* The set of known functions remains the same *)
        exists ρ.
        (* For any known g:
           - If g was in an earlier bundle, it's still there
           - If g was in a bundle and we are in one of the bundle's definitions, we're still
             in that definition *)
        intros f0 ft0 xs0 e_body Hget_f0.
        specialize (Hρ' f0 ft0 xs0 e_body Hget_f0); unfold known_function in Hρ'|-*.
        now destruct Hρ' as [Habove | [Hwithin | []]].
      * (* Unique bindings is preserved *)
        rewrite app_exp_c_eq, isoBAB.
        rewrite (proj1 (ub_app_ctx_f _)); split; [|split].
        -- unfold S_uniq in Huniq.
           rewrite app_exp_c_eq, isoBAB in Huniq.
           rewrite (proj1 (ub_app_ctx_f _)) in Huniq.
           decompose [and] Huniq; clear Huniq; auto.
        -- (* Follows from UB(e') because rename_all' doesn't change bindings *)
           unfold Rec.
           apply rename_all_uniq.
           apply known_in_ctx in Hρ; destruct Hρ as [D HD].
           unfold S_uniq in Huniq; rewrite HD, app_exp_c_eq, isoBAB in Huniq.
           apply ub_app_ctx_f in Huniq; decompose [and] Huniq.
           apply freshen_exp_uniq in Hfreshen; auto.
        -- (* Follows from vars(C[e]) ∩ BV(e') = ∅.
                BV(e'') = BV(e')
                BV(C) ⊆ vars(C[e]) *)
           unfold Rec; rewrite <- rename_all_bv.
           assert (bound_var_ctx ![C] \subset used_vars ![C ⟦ Eapp f ft' ys ⟧]). {
             rewrite app_exp_c_eq, isoBAB; unfold used_vars.
             rewrite bound_var_app_ctx; eauto with Ensembles_DB. }
           apply fresher_than_bounded in Hfresh.
           apply freshen_exp_bounded in Hfreshen.
           eapply Disjoint_Included_l; [eassumption|].
           eapply Disjoint_Included_l; [eassumption|].
           eapply Disjoint_Included_r; [eassumption|].
           apply Disjoint_intervals; lia.
Defined.

Definition rw_inline : rewriter exp_univ_exp inline_step
  trivial_delay_t trivial_R_C (@S_inline).
Proof.
  let x := eval unfold rw_inline', Fuel_Fix, rw_chain, rw_id, rw_base in rw_inline' in
  let x := eval unfold delayD, Delayed_trivial_delay_t in x in
  let x := eval lazy beta iota zeta in x in
  exact x.
Defined.

Definition initial_fns (e : exp) : S_fns <[]> e.
Proof. exists (M.empty _); intros f ft xs e_body; rewrite M.gempty; inversion 1. Defined.

Lemma inline_top' (e : exp) (s : S_inline <[]> e)
  : result exp_univ_exp inline_step (@S_inline) <[]> e.
Proof. exact (run_rewriter' rw_inline e tt s). Defined.

Definition inline_top (IH : InlineHeuristic) (c : comp_data) (e : exp) (H : unique_bindings ![e])
  : exp * comp_data :=
  let '{| resTree := e'; resState := (cdata, _, _, _, _) |} :=
    run_rewriter' rw_inline e tt (c, mk_IH _ _ _ IH, initial_fresh e, initial_fns e, H)
  in (e', cdata).

(* For now, to allow extraction, these functions assume the inliner receives terms with 
   unique bindings *)
Axiom assume_unique_bindings : forall {A}, A.
Definition inline_unsafe (IH : InlineHeuristic) (e : exp) (c : comp_data) : exp * comp_data :=
  inline_top IH c e assume_unique_bindings.

(* d should be max argument size, perhaps passed through by uncurry *)
Definition postuncurry_contract (e:exp) (s:M.t nat) (d:nat) :=
  inline_unsafe (PostUncurryIH s) e.

Definition inlinesmall_contract (e:exp) (bound:nat)  (d:nat) :=
  inline_unsafe (InlineSmallIH bound (M.empty _)) e.

Definition inline_uncurry_contract (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
  inline_unsafe (InlineSmallOrUncurried bound (M.empty _) s) e.

Definition inline_uncurry (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
  inline_unsafe (InlineUncurried (M.empty bool)) e.

Definition inline_uncurry_marked_anf (e:exp) (s:M.t nat) (bound:nat)  (d:nat) :=
  inline_unsafe (InlinedUncurriedMarkedAnf s) e.
