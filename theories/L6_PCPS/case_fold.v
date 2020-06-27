Require Import Coq.ZArith.ZArith Coq.Strings.String Coq.Lists.List.
Require Import L6.Prototype L6.cps_proto L6.proto_util.
Import ListNotations.
Unset Strict Unquote Universe Mode.

Inductive cfold_step : exp -> exp -> Prop :=
| cfold_step0 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c e ces,
  (exists D ys E, C = D >:: Econstr3 x c ys >++ E) /\ In (c, e) ces ->
  When (fun (r : unit) (s : unit) => true) ->
  cfold_step (C ⟦ Ecase x ces ⟧) (C ⟦ Rec e ⟧).

Definition R_C_ctors {A} (C : exp_c A exp_univ_exp) : Set := {
  ρ : M.tree (ctor_tag * list var) |
  forall x c ys, M.get x ρ = Some (c, ys) -> exists D E, C = D >:: Econstr3 (mk_var x) c ys >++ E }.

Instance Preserves_R_C_R_C_ctors : Preserves_R_C _ _ (@R_C_ctors).
Proof.
  intros A B fs f [ρ Hρ]; destruct f;
  try lazymatch goal with
  | |- R_C_ctors (fs >:: Econstr3 ?x' ?c' ?ys') => rename x' into x, c' into c, ys' into ys
  | _ => let x := fresh "x" with c := fresh "c" with ys := fresh "ys" with Hget := fresh "Hget" in
    exists ρ; intros x c ys Hget; destruct (Hρ x c ys Hget) as [D [E Heq]];
    match goal with |- exists _ _, _ >:: ?f = _ => exists D, (E >:: f); now subst end
  end.
  destruct x as [x]; exists (M.set x (c, ys) ρ); cbn; intros x' c' ys' Hget.
  destruct (Pos.eq_dec x x'); [subst; rewrite M.gss in Hget|rewrite M.gso in Hget by auto].
  - inversion Hget; now exists fs, <[]>.
  - destruct (Hρ x' c' ys' Hget) as [D [E Heq]]; subst. now exists D, (E >:: Econstr3 (mk_var x) c ys).
Defined.

(* TODO: move to prototype.v and make uncurry_proto use this *)
Ltac mk_easy_delay :=
  try lazymatch goal with
  | |- ConstrDelay _ -> _ =>
    clear; simpl; intros; lazymatch goal with H : forall _, _ |- _ => eapply H; try reflexivity; eauto end
  | |- EditDelay _ -> _ =>
    clear; simpl; intros; lazymatch goal with H : forall _, _ |- _ => eapply H; try reflexivity; eauto end
  end.

(* TODO: move to proto_util.v *)
Definition trivial_S {A} (C : exp_c A exp_univ_exp) (e : univD A) : Set := unit.
Instance Preserves_S_trivial_S : Preserves_S _ _ (@trivial_S). Proof. do 2 constructor. Defined.

Fixpoint find_case (c : ctor_tag) (ces : list (ctor_tag * exp)) : option exp :=
  match ces with
  | [] => None
  | (c', e) :: ces => if Pos.eqb ![c] ![c'] then Some e else find_case c ces
  end.

Lemma find_case_refines_In : forall c e ces, find_case c ces = Some e -> In (c, e) ces.
Proof.
  intros [c] e ces; induction ces as [| [[c'] e'] ces IHces]; [inversion 1|cbn].
  destruct (Pos.eq_dec c c') as [|Hneq]; subst; [rewrite Pos.eqb_refl; now inversion 1|].
  rewrite <- Pos.eqb_neq in Hneq; now rewrite Hneq.
Qed.

Definition rw_cfold : rewriter exp_univ_exp cfold_step unit unit
  (@trivial_delay_t) (@R_C_ctors) (@trivial_R_e) (@trivial_S).
Proof.
  mk_rw; mk_easy_delay; [|do 2 constructor].
  intros _ _ _ R C [x] ces [ρ Hρ] _ _ success failure.
  destruct (M.get x ρ) as [[c ys]|] eqn:Hget; [|exact failure].
  destruct (find_case c ces) as [e|] eqn:Hfind; [|exact failure].
  apply (success c e); [split; [|now apply find_case_refines_In]|reflexivity].
  destruct (Hρ x c ys Hget) as [D [E Heq]]; repeat eexists; eassumption.
Defined.
