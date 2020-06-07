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

(* -------------------- Inlining heuristics --------------------

   Rather than parameterizing by [St] as in inline.v, the heuristic is
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
        | Fcons f ft xs e fdc' =>
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
  | Fcons f t (k::xs) (Efun (Fcons h _ _ _ Fnil) (Eapp k' _ [h'])) fds' =>
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
  | Fcons f t xs (Efun (Fcons h ht ys e Fnil) (Ehalt h')) fds' =>
    let s' :=
      if ((![h] =? ![h']) && negb (occurs_in_exp ![f] ![Efun (Fcons h ht ys e Fnil) (Ehalt h')]))%bool
      then M.set ![f] true s else s
    in
    find_uncurried fds' s'
  | Fcons f t xs (Eapp f' t' xs') fds' =>
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

Fixpoint find_def (f : var) (fds : fundefs) :=
  match fds with
  | Fcons f' ft xs e fds => if Pos.eqb ![f] ![f'] then Some (ft, xs, e) else find_def f fds
  | Fnil => None
  end.

(* The function definition f(xs) = e_body (with fun tag ft) is in scope at C⟦e⟧ if... *)
Definition known_function {A} (f : var) (ft : fun_tag) (xs : list var) (e_body : exp)
          (C : exp_c A exp_univ_exp) (e : univD A) : Prop :=
  (* ...f was defined in a bundle encountered earlier... *)
  (exists D fds E, C = D >:: Efun1 fds >++ E /\ List.In (f, ft, xs, e_body) [fds]!) \/
  (* ...or f is in a bundle and we are currently inside one of the bundle's definitions... *)
  (exists D fds1 g gt ys fds2 E,
    C = D >++ ctx_of_fds fds1 >:: Fcons3 g gt ys fds2 >++ E /\
    (List.In (f, ft, xs, e_body) fds1 \/ find_def f fds2 = Some (ft, xs, e_body))) \/
  (* ...or f is in a bundle that we are currently traversing *)
  (match A return exp_c A exp_univ_exp -> univD A -> Prop with
   | exp_univ_fundefs => fun C fds2 => exists D fds1,
     C = D >++ ctx_of_fds fds1 /\
     (List.In (f, ft, xs, e_body) fds1 \/ find_def f fds2 = Some (ft, xs, e_body))
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
  forall (C : frames_t exp_univ_fundefs exp_univ_exp) f ft xs e fds,
  When (fun (r : R_misc) (s : S_misc) => true) ->
  inline_step
    (C ⟦ Fcons f ft xs e fds ⟧)
    (C ⟦ Fcons f ft xs (Local (fun IH => IH.(update_inFun) f ft xs e) e) (Rec fds) ⟧)
(* Inlining for CPS *)
| inline_cps :
  forall (C : frames_t exp_univ_exp exp_univ_exp) f ft (xs : list var) e e' (ys : list var) lhs next_x,
  lhs = Eapp f ft ys ->
  known_function f ft xs e C lhs ->
  Alpha_conv ![e] ![e'] (id <{ ![xs] ~> ![ys] }>) ->
  Disjoint _ (bound_var ![e']) (used_vars ![C ⟦ lhs ⟧]) ->
  fresher_than next_x (used_vars ![C ⟦ lhs ⟧] :|: used e') ->
  (* Only inline if the inlining heuristic decides to *)
  When (fun (IH : R_misc) (s : S_misc) => IH.(decide_App) f ft ys) ->
  inline_step
    (C ⟦ Eapp f ft ys ⟧)
    (C ⟦ (* Update inlining heuristic *)
         Local (fun IH => IH.(update_App) f ft ys)
         (* Hack: set fresh variable in cdata properly for future passes *)
         (Modify (update_next_var next_x)
         (Rec e')) ⟧).

(* Maintain map of known functions while traversing *)
Definition S_fns {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := {
  ρ : M.tree (fun_tag * list var * exp) | 
  forall f ft xs e_body, M.get f ρ = Some (ft, xs, e_body) ->
  known_function [f]! ft xs e_body C e }.

(* TODO: move the following lemmas to cps_proto.v *)

Instance exp_Frame_inj : Frame_inj exp_univ.
Proof. intros A B f x y; destruct f; now inversion 1. Qed.

Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.Eqdep.
Ltac inv_ex :=
  repeat progress match goal with
  | H : existT ?P ?T _ = existT ?P ?T _ |- _ => apply inj_pairT2 in H
  end.

(* Inhabited types *)

Class Inhabited A := inhabitant : A.

Instance Inhabited_pos : Inhabited positive := xH.
Instance Inhabited_var : Inhabited var := mk_var inhabitant.
Instance Inhabited_fun_tag : Inhabited fun_tag := mk_fun_tag inhabitant.
Instance Inhabited_ctor_tag : Inhabited ctor_tag := mk_ctor_tag inhabitant.
Instance Inhabited_prim : Inhabited prim := mk_prim inhabitant.
Instance Inhabited_N : Inhabited N := N0.

Instance Inhabited_exp : Inhabited exp := Ehalt inhabitant.
Instance Inhabited_fundefs : Inhabited fundefs := Fnil.

Instance Inhabited_list A : Inhabited (list A) := [].
Instance Inhabited_prod A B `{Inhabited A} `{Inhabited B} : Inhabited (A * B) := (inhabitant, inhabitant).

Definition univ_inhabitant {A} : univD A :=
  match A with
  | exp_univ_prod_ctor_tag_exp => inhabitant
  | exp_univ_list_prod_ctor_tag_exp => inhabitant
  | exp_univ_fundefs => inhabitant
  | exp_univ_exp => inhabitant
  | exp_univ_var => inhabitant
  | exp_univ_fun_tag => inhabitant
  | exp_univ_ctor_tag => inhabitant
  | exp_univ_prim => inhabitant
  | exp_univ_N => inhabitant
  | exp_univ_list_var => inhabitant
  end.

(* Inhabited types, with assumption that inhabited <> inhabited' *)

Class Inhabited' A := inhabitant' : A.

Instance Inhabited'_pos : Inhabited' positive := xO xH.
Instance Inhabited'_var : Inhabited' var := mk_var inhabitant'.
Instance Inhabited'_fun_tag : Inhabited' fun_tag := mk_fun_tag inhabitant'.
Instance Inhabited'_ctor_tag : Inhabited' ctor_tag := mk_ctor_tag inhabitant'.
Instance Inhabited'_prim : Inhabited' prim := mk_prim inhabitant'.
Instance Inhabited'_N : Inhabited' N := Npos inhabitant'.

Instance Inhabited'_list A `{Inhabited' A} : Inhabited' (list A) := [inhabitant'].
Instance Inhabited'_prod A B `{Inhabited' A} `{Inhabited' B} : Inhabited' (A * B) := (inhabitant', inhabitant').

Instance Inhabited'_exp : Inhabited' exp := Ehalt inhabitant'.
Instance Inhabited'_fundefs : Inhabited' fundefs := Fcons inhabitant' inhabitant' inhabitant' inhabitant' Fnil.

Lemma frame_ext_eq' {A B A' B'} (f : exp_frame_t A B) (g : exp_frame_t A' B') :
  A = A' -> B = B' ->
  (forall x x', JMeq x x' -> JMeq (frameD f x) (frameD g x')) -> JMeq f g.
Proof.
  destruct f, g; try congruence; simpl; intros _ _ Hext;
  pose (Hext1 := Hext inhabitant inhabitant JMeq_refl); clearbody Hext1;
  pose (Hext2 := Hext inhabitant' inhabitant' JMeq_refl); clearbody Hext2;
  inversion Hext1; inversion Hext2; inv_ex;
  repeat match goal with H : _ = _ |- _ => inv H end; constructor.
Qed.

Corollary frame_ext_eq {A B} (f g : exp_frame_t A B) :
  (forall x, frameD f x = frameD g x) -> f = g.
Proof.
  intros Hext; enough (JMeq f g) by now apply JMeq_eq.
  apply frame_ext_eq'; auto; intros x x' Hxx'.
  inversion Hxx'; inv_ex; subst x'.
  specialize (Hext x); rewrite Hext; now constructor.
Qed.

Class Sized A := size : A -> nat.

Fixpoint size_pos (n : positive) :=
  match n with
  | xI x => S (size_pos x)
  | xO x => S (size_pos x)
  | xH => 1%nat
  end.
Instance Sized_pos : Sized positive := size_pos.

Instance Sized_var : Sized var := fun '(mk_var x) => S (size x).
Instance Sized_fun_tag : Sized fun_tag := fun '(mk_fun_tag x) => S (size x).
Instance Sized_ctor_tag : Sized ctor_tag := fun '(mk_ctor_tag x) => S (size x).
Instance Sized_prim : Sized prim := fun '(mk_prim x) => S (size x).
Instance Sized_N : Sized N := fun n => match n with N0 => 1%nat | Npos x => S (size x) end.

Definition size_list {A} (size : A -> nat) : list A -> nat := fold_right (fun x n => S (size x + n)) 1%nat.
Definition size_prod {A B} (sizeA : A -> nat) (sizeB : B -> nat) : A * B -> nat := fun '(x, y) => S (sizeA x + sizeB y).

Instance Size_list A `{Sized A} : Sized (list A) := size_list size.
Instance Size_prod A B `{Sized A} `{Sized B} : Sized (A * B) := size_prod size size.

Fixpoint size_exp (e : exp) : nat with size_fundefs (fds : fundefs) : nat.
Proof.
- refine (match e with
  | Econstr x c ys e => S (size x + size c + size ys + size_exp e)
  | Ecase x ces => S (size x + size_list (size_prod size size_exp) ces)
  | Eproj x c n y e => S (size x + size c + size n + size y + size_exp e)
  | Eletapp x f ft ys e => S (size x + size f + size ft + size ys + size_exp e)
  | Efun fds e => S (size_fundefs fds + size_exp e)
  | Eapp f ft xs => S (size f + size ft + size xs)
  | Eprim x p ys e => S (size x + size p + size ys + size_exp e)
  | Ehalt x => S (size x)
  end).
- refine (match fds with
  | Fcons f ft xs e fds => S (size f + size ft + size xs + size_exp e + size_fundefs fds)
  | Fnil => 1%nat
  end).
Defined.

Instance Sized_exp : Sized exp := size_exp.
Instance Sized_fundefs : Sized fundefs := size_fundefs.

Definition univ_size {A} : univD A -> nat :=
  match A with
  | exp_univ_prod_ctor_tag_exp => size
  | exp_univ_list_prod_ctor_tag_exp => size
  | exp_univ_fundefs => size
  | exp_univ_exp => size
  | exp_univ_var => size
  | exp_univ_fun_tag => size
  | exp_univ_ctor_tag => size
  | exp_univ_prim => size
  | exp_univ_N => size
  | exp_univ_list_var => size
  end.

Lemma frame_size_gt {A B} (f : exp_frame_t A B) (x : univD A) :
  (univ_size (frameD f x) > univ_size x)%nat.
Proof.
  destruct f; cbn;
  try change (size_exp x) with (size x); cbn;
  try change (size_fundefs x) with (size x); cbn;
  try change (size_list (size_prod size size) x) with (size x); cbn;
  lia.
Qed.

Fixpoint exp_c_size_ge {A B} (C : exp_c A B) (x : univD A) {struct C} :
  (univ_size (C ⟦ x ⟧) >= univ_size x)%nat.
Proof.
  destruct C as [|A AB B f C]; simpl; [lia|].
  assert (univ_size (C ⟦ exp_frameD A AB f x ⟧) >= univ_size (frameD f x))%nat by apply exp_c_size_ge.
  assert (univ_size (frameD f x) > univ_size x)%nat by apply frame_size_gt.
  lia.
Qed.

Definition exp_c_size_eq {A B} (C : exp_c A B) (x : univD A) :
  univ_size (C ⟦ x ⟧) = univ_size x -> JMeq C (<[]> : exp_c A A).
Proof.
  destruct C as [|A AB B f C]; simpl; [constructor|intros HC].
  assert (univ_size (C ⟦ exp_frameD A AB f x ⟧) >= univ_size (exp_frameD A AB f x))%nat
   by apply exp_c_size_ge.
  assert (univ_size (exp_frameD A AB f x) > univ_size x)%nat by apply frame_size_gt.
  lia.
Qed.

Lemma exp_ext_nil {A B} (C : exp_c A B) : A = B -> (forall x, JMeq x (C ⟦ x ⟧)) -> JMeq C (<[]> : exp_c A A).
Proof.
  destruct C as [|A AB B f C]; [constructor|simpl].
  intros HeqB Hext; subst; specialize (Hext univ_inhabitant).
  inversion Hext; inv_ex.
  apply f_equal with (f := univ_size) in H.
  match type of Hext with
  | JMeq _ (?C ⟦ ?f ⟧) =>
    match f with
    | exp_frameD _ _ _ ?x =>
      assert (univ_size (C ⟦ f ⟧) >= univ_size f)%nat by apply exp_c_size_ge;
      assert (univ_size f > univ_size x)%nat by apply frame_size_gt;
      lia
    end
  end.
Qed.

Corollary exp_ext_nil' {A B} (C : exp_c A B) : A = B -> (forall x, JMeq x (C ⟦ x ⟧)) -> JMeq C (<[]> : exp_c B B).
Proof. intros; subst; now apply exp_ext_nil. Qed.

Lemma exp_c_ext_eq' {A B A'} (C : exp_c A B) (D : exp_c A' B) :
  A = A' -> (forall x x', JMeq x x' -> C ⟦ x ⟧ = D ⟦ x' ⟧) -> JMeq C D.
Proof.
  remember (frames_len C + frames_len D)%nat as n eqn:Heqn.
  revert A B A' C D Heqn; induction n as [n IHn] using lt_wf_ind.
  intros A B A' C D Heqn Heq Hext.
  destruct (frames_split C) as [[AB [g [C' HC]]] | HClen0];
  destruct (frames_split D) as [[AB' [g' [D' HD]]] | HDlen0].
  - admit.
  - admit.
  - admit.
  - destruct C, D; simpl in HClen0, HDlen0; try congruence; constructor.
Admitted.
(*
  destruct C, D.
  - constructor.
  - intros Heq Hext; apply JMeq_sym; apply exp_ext_nil'; [congruence|].
    subst; intros x; specialize (Hext x x JMeq_refl); simpl in *; rewrite <- Hext; constructor.
  - intros Heq Hext; subst; apply exp_ext_nil; [congruence|].
    intros x; specialize (Hext x x JMeq_refl); simpl in *; rewrite Hext; constructor.
  - 
    intros ? Hwat; subst; simpl in *.
    clear - Hwat.
  destruct f, g; try congruence; simpl; intros _ _ Hext;
  pose (Hext1 := Hext inhabitant inhabitant JMeq_refl); clearbody Hext1;
  pose (Hext2 := Hext inhabitant' inhabitant' JMeq_refl); clearbody Hext2;
  inversion Hext1; inversion Hext2; inv_ex;
  repeat match goal with H : _ = _ |- _ => inv H end; constructor.
Qed. *)

(*
Lemma ctx_cons_inj U V1 V2 W
      (f : exp_frame_t U V1) (C : exp_c V1 W)
      (g : exp_frame_t U V2) (D : exp_c V2 W) :
  JMeq (C >:: f) (D >:: g) -> V1 = V2 /\ JMeq f g /\ JMeq C D.
Proof.
  destruct f, g.
  inversion 1; inv_ex;
  try lazymatch goal with H : _ >:: _ = _ >:: _ |- _ => inversion H end;
  inv_ex; subst; repeat split; try constructor.
  inversion 1.
  inv_ex. *)

Definition uframe_t {U : Set} `{H : Frame U} := {A & {B & @frame_t U H A B}}.
Definition uframes_t {U : Set} `{H : Frame U} := list (@uframe_t U H).

Fixpoint well_typed {U : Set} `{H : Frame U} (A B : U) (fs : @uframes_t U H) : Prop.
Proof.
  destruct fs as [|f fs]; [exact (A = B)|].
  destruct f as [A' [AB f]].
  exact (A = A' /\ well_typed U H AB B fs).
Defined.

Fixpoint untype {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) : @uframes_t U H.
Proof.
  destruct fs as [|A AB B f fs]; [exact []|refine (_ :: _)].
  - do 2 eexists; exact f.
  - eapply untype; exact fs.
Defined.

Fixpoint untype_well_typed {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) :
  well_typed A B (untype fs).
Proof.
  destruct fs as [|A AB B f fs]; [reflexivity|simpl].
  split; [reflexivity|now apply untype_well_typed].
Defined.

Fixpoint retype {U : Set} `{H : Frame U} (A B : U) (fs : @uframes_t U H)
         (Hty : well_typed A B fs) {struct fs} : 
  @frames_t U H A B.
Proof.
  destruct fs as [|[A' [AB f]] fs]; simpl in Hty.
  - subst; exact <[]>.
  - destruct Hty; subst.
    refine (_ >:: f).
    now eapply retype.
Defined.

Definition frames_sig_t {U : Set} `{H : Frame U} A B := {fs : @uframes_t U H | well_typed A B fs}.

Definition ty_split {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) : @frames_sig_t U H A B.
Proof. exists (untype fs); now apply untype_well_typed. Defined.

Definition ty_merge {U : Set} `{H : Frame U} {A B : U} : @frames_sig_t U H A B -> @frames_t U H A B.
Proof. intros [fs Hfs]; now eapply retype. Defined.

Fixpoint t_sig_t {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) :
  ty_merge (ty_split fs) = fs.
Proof.
  destruct fs as [|A AB B f fs]; [reflexivity|simpl].
  unfold eq_rec_r, eq_rec, eq_rect, eq_sym; f_equal.
  rewrite <- t_sig_t; reflexivity.
Qed.

Fixpoint sig_t_sig' {U : Set} `{H : Frame U} {A B : U} (fs : @uframes_t U H)
         (Hty : @well_typed U H A B fs) {struct fs} :
  ty_split (ty_merge (exist _ fs Hty)) = (exist _ fs Hty).
Proof.
  destruct fs as [|[A' [AB' f]] fs]; simpl in Hty.
  - subst; reflexivity.
  - destruct Hty as [? Hwt]; subst; cbn; unfold ty_split; cbn.
    apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    specialize (sig_t_sig' U H _ _ fs Hwt).
    apply (@f_equal _ _ (@proj1_sig _ _)) in sig_t_sig'; cbn in sig_t_sig'.
    now rewrite sig_t_sig'.
Defined.

Definition sig_t_sig {U : Set} `{H : Frame U} {A B : U} (fs : @frames_sig_t U H A B) :
  ty_split (ty_merge fs) = fs.
Proof. destruct fs as [fs Hfs]; apply sig_t_sig'. Defined.

Instance Iso_frames {U : Set} `{H : Frame U} {A B : U} : Iso (@frames_t U H A B) (@frames_sig_t U H A B) := {
  isoAofB := ty_merge;
  isoBofA := ty_split;
  isoABA := t_sig_t;
  isoBAB := sig_t_sig }.

(* If not entering or exiting a function bundle, the set of known functions remains the same *)

(* Inductive frames_eq {U : Set} `{Frame U} : forall {A B A' B' : U}, frames_t A B -> frames_t A' B' -> Prop := *)
(* | frames_eq_nil : forall A A', A = A' -> frames_eq (<[]> : frames_t A A) (<[]> : frames_t A' A'). *)
(* | frames_eq_cons : forall A AB B A' AB' B', A = A' -> frames_eq (<[]> : frames_t A A) (<[]> : frames_t A' A'). *)

Fixpoint frames_eq {U : Set} `{Frame U} {A B A' B' : U} (fs : frames_t A B) (gs : frames_t A' B') : Prop.
Proof.
  destruct fs as [|A AB B f fs]; destruct gs as [|A' AB' B' g gs].
  - exact (A = A0).
  - exact False.
  - exact False.
  - refine (exists (HA : A = A') (HAB : AB = AB'), _).
    subst; refine (f = g /\ _).
    eapply frames_eq; [exact fs|exact gs].
Defined.

(* Infix "~=" := Feq (at level 80, no associativity). *)

Definition frames_split' {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) :
  (exists AB (g : F A AB) (gs : frames_t' F AB B), fs = gs >:: g) \/ (frames_len fs = O).
Proof. destruct fs as [| A' AB B' f fs]; [now right|left; now do 3 eexists]. Qed.

Fixpoint eq_frames_eq {U : Set} `{Frame U} {A B : U}
      (fs gs : frames_t A B) :
  fs = gs -> frames_eq fs gs.
Proof.
  destruct fs; destruct (frames_split' gs) as [[AA [g [gs' Hgs]]]|Hglen].
  - subst gs; now inversion 1.
  - intros Hnil; subst; reflexivity.
  - subst gs; inversion 1; subst; inv_ex; simpl; exists eq_refl, eq_refl; cbn.
    split; [auto|now apply eq_frames_eq].
  - destruct gs; [inversion 1|inversion Hglen].
Qed.

Fixpoint frames_eq_eq {U : Set} `{Frame U} {A B : U}
      {fs gs : frames_t A B} :
  frames_eq fs gs -> fs = gs.
Proof.
  destruct fs; destruct (frames_split' gs) as [[AB [g [gs' Hgs]]]|Hglen].
  - subst gs; inversion 1.
  - admit.
  - subst gs; simpl.
    unfold eq_rect_r, eq_rect, eq_sym.
    intros [HA [HAB Heqs]].
Admitted.

Lemma eq_JMeq {A} {x y : A} (H : x = y) : JMeq x y. Proof. subst; constructor. Qed.

Lemma known_nonbundle_dn {A B} (C : exp_c B exp_univ_exp) (fr : exp_frame_t A B)
      (e : univD A) f ft xs e_body :
  A <> exp_univ_fundefs -> B <> exp_univ_fundefs ->
  known_function f ft xs e_body C (frameD fr e) ->
  known_function f ft xs e_body (C >:: fr) e.
Proof.
  destruct fr; try congruence; intros _ _ Hknown;
  solve [
    destruct Hknown as [[D [fds [E [HC Hfxs]]]] | [[D [fds1 [g [gt [ys [fds2 [E [HC Hfxs]]]]]]]] | []]];
    [left|right; left]; subst C; repeat eexists;
    try match goal with |- _ /\ _ => split end; try match goal with
    | |- context [?fs >++ ?gs >:: ?g] => change (fs >++ gs >:: g) with (fs >++ (gs >:: g))
    end; try reflexivity; try assumption].
Qed.

Lemma known_nonbundle_up {A B} (C : exp_c B exp_univ_exp) (fr : exp_frame_t A B)
      (e : univD A) f ft xs e_body :
  A <> exp_univ_fundefs -> B <> exp_univ_fundefs ->
  known_function f ft xs e_body (C >:: fr) e ->
  known_function f ft xs e_body C (frameD fr e).
Proof.
  destruct fr; try congruence; intros _ _ Hknown.
    destruct Hknown as [[D [fds [E [HC Hfxs]]]] | [[D [fds1 [g [gt [ys [fds2 [E [HC Hfxs]]]]]]]] | []]];
    [left|right; left].
    apply eq_frames_eq in HC.
    destruct (frames_split' E) as [[AB [Ef [E' HE]]] | HElen]; [subst E|].
    simpl in HC.
    apply frames_eq_eq in HC.
    inversion HC; inv_ex.
    inversion HC.
    inversion HC.
    apply inj_pairT2 in H0.
    inversion H0.
    apply inj_pairT2 in H2.
    Check inj_pairT2.
    SearchAbout existT.
    subst E.
    destruct E.

    subst C; repeat eexists;
    try match goal with |- _ /\ _ => split end; try match goal with
    | |- context [?fs >++ ?gs >:: ?g] => change (fs >++ gs >:: g) with (fs >++ (gs >:: g))
    end; try reflexivity; try assumption.
Defined.


(* The function definition f(xs) = e_body (with fun tag ft) is in scope at C⟦e⟧ if... *)
Definition known_function {A} (f : var) (ft : fun_tag) (xs : list var) (e_body : exp)
          (C : exp_c A exp_univ_exp) (e : univD A) : Prop :=
  (* ...f was defined in a bundle encountered earlier... *)
  (exists D fds E, C = D >:: Efun1 fds >++ E /\ List.In (f, ft, xs, e_body) [fds]!) \/
  (* ...or f is in a bundle and we are currently inside one of the bundle's definitions... *)
  (exists D fds1 g gt ys fds2 E,
    C = D >++ ctx_of_fds fds1 >:: Fcons3 g gt ys fds2 >++ E /\
    (List.In (f, ft, xs, e_body) fds1 \/ find_def f fds2 = Some (ft, xs, e_body))) \/
  (* ...or f is in a bundle that we are currently traversing *)
  (match A return exp_c A exp_univ_exp -> univD A -> Prop with
   | exp_univ_fundefs => fun C fds2 => exists D fds1,
     C = D >++ ctx_of_fds fds1 /\
     (List.In (f, ft, xs, e_body) fds1 \/ find_def f fds2 = Some (ft, xs, e_body))
   | _ => fun _ _ => False
   end C e).

Instance Preserves_S : Preserves_S _ exp_univ_exp (@S_fns).
Proof.
  constructor.
  (* Moving upwards *)
  - admit.
  (* Moving downwards *)
  - intros A B C f e [ρ Hρ].
    destruct f; lazymatch goal with
    (* There are only a few cases that we care about: *)
    | |- S_fns (C >:: Efun0 ?fds) ?e => idtac
    | |- S_fns (C >:: Efun1 ?e) ?fds => idtac
    | |- S_fns (C >:: Fcons3 ?f ?ft ?xs ?fds) ?e => idtac
    | |- S_fns (C >:: Fcons4 ?f ?ft ?xs ?e) ?fds => idtac
    (* For all the others, the map should remain unchanged *)
    | _ =>
      exists ρ; intros f' ft' xs' e' Hftxse';
      specialize (Hρ f' ft' xs' e' Hftxse')
    end.
  (* Before entering the body of a function f, need to delete ρ(f) and add fds *)
  - rename v into f, f into ft, l into xs, f0 into fds; destruct f as [f].
    exists (M.remove f ρ); intros g gt ys e Hget.
    destruct (Pos.eq_dec g f) as [Hgf|Hgf]; [subst; now rewrite M.grs in Hget|].
    rewrite M.gro in Hget by auto; now apply known_function_cons.
  (* When moving on from one function f(xs) = e body, need to update ρ(f) *)
  - rename v into f, f into ft, l into xs; destruct f as [f].
    exists (M.set f (ft, xs, e) ρ); intros g gt ys eg Hget.
    destruct (Pos.eq_dec g f) as [Hgf|Hgf];
      [subst f|rewrite M.gso in Hget by auto; now apply known_function_cons].
    rewrite M.gss in Hget; inv Hget.
    unfold known_function.
    + admit.
    + rewrite M.gso in Hget by auto; now apply known_function_cons.
  (* It only remains to show that the extended map satisfies the invariant *)
  intros f' ft' xs' e' Hget.
  destruct (Pos.eq_dec f0 f').
  - subst; rewrite M.gss in Hget; inv Hget; right; left.
Abort.

(*
Lemma known_function_cons {A B} f ft xs e_body C (fr : exp_frame_t A B) (e : univD A) :
  known_function f ft xs e_body C (frameD fr e) ->
  known_function f ft xs e_body (C >:: fr) e.
Proof.
  intros Hknown; destruct fr; solve [
    destruct Hknown as [[D [fds [E [HC Hfxs]]]] | [D [fds1 [g [gt [ys [fds2 [E [HC Hfxs]]]]]]]]];
    [left|right]; subst C; repeat eexists;
    try match goal with |- _ /\ _ => split end; try match goal with
    | |- context [?fs >++ ?gs >:: ?g] => change (fs >++ gs >:: g) with (fs >++ (gs >:: g))
    end; try reflexivity; try assumption].
Qed.
*)

(*
Fixpoint add_fundefs (fds:fundefs) ρ :=
  match fds with
  | Fnil => ρ
  | Fcons f t xs e fds => M.set ![f] (t, xs, e) (add_fundefs fds ρ)
  end.
*)

Definition r_map : Set := M.tree cps.var.

Fixpoint fun_names (fds : fundefs) : list var :=
  match fds with
  | Fnil => []
  | Fcons f _ _ _ fds => f :: fun_names fds
  end.

Fixpoint freshen_term (next : positive) (σ : r_map) (e : exp) {struct e} : positive * exp
with freshen_fun (next : positive) (σ : r_map) (fds : fundefs) {struct fds} : positive * fundefs.
Proof.
- refine (
  match e with
  | Econstr x c ys e =>
    let '(next, x') := gensym next in
    let ys := [apply_r_list σ ![ys]]! in
    let '(next, e) := freshen_term next (M.set ![x] ![x'] σ) e in
    (next, Econstr x' c ys e)
  | Ecase x ces =>
    let fix freshen_ces next ces {struct ces} :=
      match ces with
      | [] => (next, [])
      | (c, e) :: ces =>
        let '(next, e) := freshen_term next σ e in
        let '(next, ces) := freshen_ces next ces in
        (next, (c, e) :: ces)
      end
    in
    let x := [apply_r σ ![x]]! in
    let '(next, ces) := freshen_ces next ces in
    (next, Ecase x ces)
  | Eproj x c n y e =>
    let '(next, x') := gensym next in
    let y := [apply_r σ ![y]]! in
    let '(next, e) := freshen_term next (M.set ![x] ![x'] σ) e in
    (next, Eproj x' c n y e)
  | Eletapp x f ft ys e =>
    let '(next, x') := gensym next in
    let f := [apply_r σ ![f]]! in
    let ys := [apply_r_list σ ![ys]]! in
    let '(next, e) := freshen_term next (M.set ![x] ![x'] σ) e in
    (next, Eletapp x' f ft ys e)
  | Efun fds e =>
    let fs := fun_names fds in
    let '(next, fs') := gensyms next fs in
    match set_lists ![fs] ![fs'] σ with
    | Some σ =>
      let '(next, fds) := freshen_fun next σ fds in
      let '(next, e) := freshen_term next σ e in
      (next, Efun fds e)
    | None => (* unreachable *) (next, Efun Fnil e)
    end
  | Eapp f ft xs =>
    let f := [apply_r σ ![f]]! in
    let xs := [apply_r_list σ ![xs]]! in
    (next, Eapp f ft xs)
  | Eprim x p ys e =>
    let '(next, x') := gensym next in
    let ys := [apply_r_list σ ![ys]]! in 
    let '(next, e) := freshen_term next (M.set ![x] ![x'] σ) e in
    (next, Eprim x' p ys e)
  | Ehalt x =>
    let x := [apply_r σ ![x]]! in
    (next, Ehalt x)
  end).
- refine (
  match fds with
  | Fcons f ft xs e fds =>
    let f := [apply_r σ ![f]]! in
    let '(next, xs') := gensyms next xs in
    match set_lists ![xs] ![xs'] σ with
    | Some σ =>
      let '(next, e) := freshen_term next σ e in
      let '(next, fds) := freshen_fun next σ fds in
      (next, Fcons f ft xs' e fds)
    | None => (* unreachable *) (next, Fnil)
    end
  | Fnil => (next, Fnil)
  end).
Defined.

Fixpoint freshen_term_spec e {struct e} :
  forall S next σ next' e',
  injective_subdomain (occurs_free ![e]) (apply_r σ) ->
  fresher_than next S ->
  (next', e') = freshen_term next σ e ->
  Alpha_conv ![e] ![e'] (apply_r σ) /\
  Disjoint _ (bound_var ![e']) S /\
  fresher_than next' (S :|: used_vars ![e'])
with freshen_fun_spec fds {struct fds} :
  forall S next σ next' fds',
  injective_subdomain (occurs_free_fundefs ![fds]) (apply_r σ) ->
  fresher_than next S ->
  (next', fds') = freshen_fun next σ fds ->
  Alpha_conv_fundefs ![fds] ![fds'] (apply_r σ) /\
  Disjoint _ (bound_var_fundefs ![fds']) S /\
  fresher_than next' (S :|: used_vars_fundefs ![fds']).
Proof.
  - destruct e; intros S next σ next' e'; unbox_newtypes; simpl;
    repeat match goal with
    | |- context [let '(_, _) := ?f ?e in _] =>
      let next := fresh "next" in
      let e' := fresh "e" in
      let Hfreshen := fresh "Hfreshen" in
      destruct (f e) as [next e'] eqn:Hfreshen; symmetry in Hfreshen
    end.
Admitted.

(*
Definition rename' {A} (σ : r_map) : univD A -> univD A :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(c, e) => (c, [rename_all σ ![e]]!)
  | exp_univ_list_prod_ctor_tag_exp => fun ces => map (fun '(c, e) => (c, [rename_all σ ![e]]!)) ces
  | exp_univ_fundefs => fun fds => [rename_all_fun σ ![fds]]!
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
Definition range {A B} (f : A -> option B) : Ensemble B :=
  fun y => exists x, f x = Some y.
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
