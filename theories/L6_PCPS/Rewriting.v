Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.funind.Recdef.
Require Import Coq.PArith.BinPos.
Require Import Lia.
From compcert.lib Require Import Maps.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Ltac2.Ltac2.
Import Ltac2.Notations.
Set Default Proof Mode "Ltac2".

Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.Eqdep.
Ltac inv_ex :=
  repeat progress match goal with
  | H : existT ?P ?T _ = existT ?P ?T _ |- _ => apply inj_pairT2 in H
  end.

Require Export CertiCoq.L6.Frame.

Set Implicit Arguments.

(* -------------------- Annotations -------------------- *)

Definition Rec {A} (rhs : A) : A := rhs.
Definition BottomUp {A} (rhs : A) : A := rhs.

(* -------------------- Erased values -------------------- *)

(* An erased value of type [A] is a value which can only be used to construct Props.
   We can represent erased values [x] in CPS with answer type Prop, as functions of
   the form [fun k => k x]: *)
Definition erased A := (A -> Prop) -> Prop.
Class e_ok {A} (x : erased A) := erased_ok : exists (y : A), x = (fun k => k y).
(* These two items are carried separately so that they can both be erased during extraction.
   Bundling them together in a dependent pair type would erase to a pair type [box × box] *)

(* Erasing a value *)
Definition erase {A} : A -> erased A := fun x k => k x.
Instance erase_ok {A} (x : A) : e_ok (erase x). Proof. exists x; reflexivity. Qed.

(* Erased values can always be used to construct other erased values *)
Definition e_map {A B} (f : A -> B) (x : erased A) : erased B := fun k => x (fun x => k (f x)).
Instance e_map_ok {A B} (f : A -> B) (x : erased A) `{H : e_ok _ x} : e_ok (e_map f x).
Proof. destruct H as [y Hy]; subst x; unfold e_map; now exists (f y). Qed.

(* Only proofs can be unerased *)
Definition recover (x : erased Prop) : Prop := x (fun x => x).
Notation "'«' P '»'" := (recover P).

(* Remove all erased operators from a goal using e_ok hypotheses *)
Ltac unerase :=
  repeat match goal with
  | H : e_ok ?x |- _ => 
    let x' := fresh x in
    rename x into x';
    destruct H as [x H];
    subst x'
  end;
  unfold recover, e_map, erase in *.

Ltac2 unerase () := ltac1:(unerase).
Ltac2 Notation "unerase" := unerase ().

(* Example *)
Require Import Lia.
Require Extraction.
Module Example.

Fixpoint thingy (n : erased nat) `{Hn : e_ok _ n} (m p : nat) (Hmp : «e_map (fun n => n + m = p) n») {struct m} : nat.
Proof.
  destruct m as [|m] > [exact p|].
  specialize (thingy (e_map S n) _ m p); apply thingy; clear thingy.
  ltac1:(unerase; lia).
Defined.

Print thingy.
(* Since n and its proof are carried separately, both are erased entirely *)
Recursive Extraction thingy.
End Example.

(* -------------------- Fixpoint combinator -------------------- *)

(* Equations and Program Fixpoint use a fixpoint combinator which has the following type when
   specialized to a particular measure [measure]:
     [forall arg_pack, (forall arg_pack', measure arg_pack' < measure arg_pack -> P arg_pack') -> P arg_pack]
   This requires wrapping and unwrapping [arg_pack]s. Instead we'll make
     [forall (cost : erased nat), e_ok cost -> (forall cost', e_ok cost' -> cost' < cost -> Q cost') -> Q cost]
   which can achieve the same thing without arg packs by setting
     [Q := fun cost => arg1 -> ‥ -> arg_n -> cost = measure(arg1, ‥, arg_n) -> P (arg1, ‥, arg_n)].

   After a function has been defined this way, unfolding all fixpoint combinators will leave behind a
   primitive fixpoint of type
     [forall (cost : erased nat), e_ok cost -> Accessible cost -> arg1 -> ‥ -> arg_n -> cost = measure ‥ -> P ‥]
   that is structurally recursive on the accessibility proof [Accessible cost].

   Extraction will erase [cost : erased nat], [e_ok cost], [Accessible cost], and [cost = measure ‥],
   leaving a plain recursive function of type [arg1 -> ‥ -> arg_n -> P ‥]. *)
Require Import Coq.Arith.Wf_nat.
Section WellfoundedRecursion.

(* Modelled after https://coq.inria.fr/library/Coq.Init.Wf.html#Acc *)
Section AccS.

  Context (A : Type) (B : A -> Prop) (R : forall x, B x -> forall y, B y -> Prop).

  Inductive AccS (x : A) (Hx : B x) : Prop :=
    AccS_intro : (forall (y : A) (Hy : B y), R Hy Hx -> @AccS y Hy) -> AccS Hx.

  Definition well_foundedS := forall (x : A) (Hx : B x), AccS Hx.

  Section FixS.

    Context
      (Rwf : well_foundedS)
      (P : A -> Type)
      (F : forall (x : A) (Hx : B x), (forall (y : A) (Hy : B y), R Hy Hx -> P y) -> P x).

    Fixpoint FixS_F (x : A) (Hx : B x) (H : AccS Hx) {struct H} : P x :=
      F (fun (y : A) (Hy : B y) (Hyx : R Hy Hx) =>
          FixS_F (let 'AccS_intro H := H in H y Hy Hyx)).

    Definition FixS (x : A) (Hx : B x) : P x := FixS_F (Rwf Hx).

  End FixS.

End AccS.

Section FixEN.

Definition enat := erased nat.
Definition e_lt : forall x : enat, e_ok x -> forall y : enat, e_ok y -> Prop :=
  fun n Hn m Hm => «e_map (fun n => «e_map (fun m => n < m) m») n».

Lemma e_lt_wf : well_foundedS e_ok e_lt.
Proof.
  intros n Hn; unerase.
  induction n as [n IHn] using Wf_nat.lt_wf_ind.
  constructor; intros m Hm Hmn; unerase.
  now apply IHn.
Defined.

Definition FixEN :
  forall P : enat -> Type,
  (forall (x : enat) (Hx : e_ok x), (forall (y : enat) (Hy : e_ok y), e_lt Hy Hx -> P y) -> P x) ->
  forall x : enat, e_ok x -> P x
  := FixS e_lt_wf.

End FixEN.

End WellfoundedRecursion.

Extraction Inline FixEN FixS FixS_F.

Module FixENExample.

Definition plus : forall (cost : enat) `{e_ok _ cost}, forall n m : nat, «e_map (eq n) cost» -> nat.
Proof.
  apply (FixEN (fun cost => forall n m : nat, «e_map (eq n) cost» -> nat)).
  intros cost Hok rec n m Hcost.
  destruct n as [|n] > [exact m|].
  specialize rec with (n := n).
  specialize (rec (erase n) _).
  apply S, rec > [|exact m|]; unfold e_lt in *; ltac1:(unerase; lia).
Defined.

End FixENExample.

Print FixENExample.plus.
Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction FixENExample.plus.

(* -------------------- 1-hole contexts built from frames -------------------- *)

(* A 1-hole context made out of frames F *)
Inductive frames_t' {U : Set} {F : U -> U -> Set} : U -> U -> Set :=
| frames_nil : forall {A}, frames_t' A A
| frames_cons : forall {A B C}, F A B -> frames_t' B C -> frames_t' A C.
Arguments frames_t' {U} F _ _.
Notation "C '>::' f" := (frames_cons f C) (at level 50, left associativity).
Notation "<[]>" := (frames_nil).
Notation "<[ x ; .. ; z ]>" := (frames_cons z .. (frames_cons x frames_nil) ..).

(* The 1-hole contexts you usually want *)
Definition frames_t {U : Set} `{Frame U} : U -> U -> Set := frames_t' frame_t.

(* Context application *)
Reserved Notation "C '⟦' x '⟧'" (at level 50, no associativity).
Fixpoint framesD {U : Set} `{Frame U} {A B : U}
         (fs : frames_t A B) : univD A -> univD B :=
  match fs with
  | <[]> => fun x => x
  | fs >:: f => fun x => fs ⟦ frameD f x ⟧
  end
where "C '⟦' x '⟧'" := (framesD C x).

Lemma framesD_cons {U : Set} `{Frame U} {A B C : U}
      (fs : frames_t B C) (f : frame_t A B)
      (x : univD A)
  : (fs >:: f) ⟦ x ⟧ = fs ⟦ frameD f x ⟧.
Proof. reflexivity. Defined.

(* Context composition *)
Reserved Notation "gs '>++' fs" (at level 50, left associativity).
Fixpoint frames_compose {U : Set} {F : U -> U -> Set} {A B C : U}
         (fs : frames_t' F A B) : frames_t' F B C -> frames_t' F A C :=
  match fs with
  | <[]> => fun gs => gs
  | fs >:: f => fun gs => gs >++ fs >:: f
  end
where "gs '>++' fs" := (frames_compose fs gs).

(* Laws: functor laws + injectivity *)

Lemma frames_id_law {U : Set} `{Frame U} {A} (x : univD A) : <[]> ⟦ x ⟧ = x.
Proof. auto. Defined.

Lemma frames_compose_law {U : Set} `{Frame U} {A B C} :
  forall (fs : frames_t B C) (gs : frames_t A B) (x : univD A),
  (fs >++ gs) ⟦ x ⟧ = fs ⟦ gs ⟦ x ⟧ ⟧.
Proof. intros fs gs; revert fs; induction gs; simpl; auto. Defined.

Class Frame_inj (U : Set) `{Frame U} :=
  frame_inj :
    forall {A B : U} (f : frame_t A B) (x y : univD A),
    frameD f x = frameD f y -> x = y.

Fixpoint frames_inj {U : Set} `{Frame U} `{Frame_inj U} {A B} (fs : frames_t A B) :
  forall (x y : univD A), fs ⟦ x ⟧ = fs ⟦ y ⟧ -> x = y.
Proof.
  destruct fs; auto; simpl; intros x y Heq.
  apply frames_inj with (fs := fs) in Heq; auto.
  apply (frame_inj f) in Heq; auto.
Defined.

(* Misc. lemmas (mostly about how frames_t is similar to list) *)

Definition flip {U} (F : U -> U -> Set) : U -> U -> Set := fun A B => F B A.
Fixpoint frames_rev {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) : frames_t' (flip F) B A :=
  match fs with
  | <[]> => <[]>
  | fs >:: f => <[f]> >++ frames_rev fs
  end.
Fixpoint frames_revD {U : Set} `{Frame U} {A B : U}
         (fs : frames_t' (flip frame_t) B A) : univD A -> univD B :=
  match fs with
  | <[]> => fun x => x
  | fs >:: f => fun x => frameD f (frames_revD fs x)
  end.

Fixpoint frames_nil_comp {U : Set} {F : U -> U -> Set} {A B : U}
         (fs : frames_t' F A B) {struct fs}
  : <[]> >++ fs = fs.
Proof. destruct fs > [reflexivity|simpl; now rewrite frames_nil_comp]. Defined.

Fixpoint frames_revD_comp {U : Set} `{HFrame : Frame U} {A B C : U}
         (fs : frames_t' (flip frame_t) B A) (gs : frames_t' (flip frame_t) C B)
         (x : univD A)
         {struct gs}
  : frames_revD (fs >++ gs) x = frames_revD gs (frames_revD fs x).
Proof. destruct gs > [reflexivity|simpl; now rewrite frames_revD_comp]. Defined.

Fixpoint framesD_rev {U : Set} `{Frame U} {A B : U} (fs : frames_t A B) (x : univD A)
         {struct fs} : fs ⟦ x ⟧ = frames_revD (frames_rev fs) x.
Proof.
  destruct fs > [reflexivity|simpl].
  now rewrite frames_revD_comp, <- framesD_rev.
Defined.

Fixpoint frames_rev_assoc {U : Set} {F : U -> U -> Set} {A B C D : U}
         (fs : frames_t' F A B) (gs : frames_t' F B C) (hs : frames_t' F C D)
         {struct fs}
  : hs >++ (gs >++ fs) = hs >++ gs >++ fs.
Proof.
  destruct fs > [reflexivity|simpl].
  now rewrite frames_rev_assoc.
Defined.

Fixpoint frames_rev_comp {U : Set} {F : U -> U -> Set} {A B C : U}
         (fs : frames_t' F A B) (gs : frames_t' F B C)
         {struct fs}
  : frames_rev (gs >++ fs) = frames_rev fs >++ frames_rev gs.
Proof.
  destruct fs; simpl.
  - now rewrite frames_nil_comp.
  - now rewrite frames_rev_comp, frames_rev_assoc.
Defined.

Fixpoint frames_rev_rev {U : Set} `{Frame U} {A B : U} (fs : frames_t A B)
         {struct fs} : frames_rev (frames_rev fs) = fs.
Proof.
  destruct fs > [reflexivity|simpl].
  now rewrite frames_rev_comp, frames_rev_rev.
Defined.

Fixpoint frames_any {U : Set} {F : U -> U -> Set} (P : forall {A B : U}, F A B -> Prop)
         {A B} (fs : frames_t' F A B) : Prop :=
  match fs with
  | <[]> => False
  | fs >:: f => P f \/ frames_any (@P) fs
  end.

Fixpoint frames_any_app
         {U : Set} {F : U -> U -> Set} (P : forall {A B : U}, F A B -> Prop)
         {A B C} (gs : frames_t' F B C) (fs : frames_t' F A B)
         {struct fs}
  : frames_any (@P) (gs >++ fs) <-> frames_any (@P) gs \/ frames_any (@P) fs.
Proof.
  destruct fs > [simpl; ltac1:(tauto)|simpl].
  rewrite frames_any_app; ltac1:(tauto).
Defined.

Fixpoint frames_any_cons
         {U : Set} {F : U -> U -> Set} (P : forall {A B : U}, F A B -> Prop)
         {A B C} (fs : frames_t' F B C) (f : F A B)
         {struct fs}
  : frames_any (@P) (fs >:: f) <-> frames_any (@P) fs \/ P f.
Proof. unfold frames_any; ltac1:(tauto). Defined.

Fixpoint frames_ind {U : Set} {F : U -> U -> Set} (P : forall {A B}, frames_t' F A B -> Prop)
         (Hnil : forall {A}, P (<[]> : frames_t' F A A))
         (Hcons : forall {A B C} (f : F A B) (fs : frames_t' F B C), P fs -> P (fs >:: f))
         {A B} (fs : frames_t' F A B) {struct fs}
  : P fs.
Proof.
  destruct fs > [apply Hnil|apply Hcons].
  now apply frames_ind.
Defined.

Fixpoint frames_len {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) : nat :=
  match fs with
  | <[]> => O
  | fs >:: f => S (frames_len fs)
  end.

Fixpoint frames_len_compose {U : Set} {F : U -> U -> Set} {A B C}
         (fs : frames_t' F A B) (gs : frames_t' F B C) {struct fs} :
  frames_len (gs >++ fs) = frames_len fs + frames_len gs.
Proof.
  destruct fs as [ |A' AB B' f fs] > [reflexivity|simpl].
  now rewrite frames_len_compose.
Qed.

(* Useful in situations where [destruct] struggles with dependencies *)
Definition frames_split' {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) :
  (exists AB (g : F A AB) (gs : frames_t' F AB B), fs = gs >:: g) \/
  (A = B /\ JMeq fs (<[]> : frames_t' F A A) /\ frames_len fs = 0%nat).
Proof. destruct fs as [| A' AB B' f fs] > [now right|left; now do 3 eexists]. Qed.

(* Like frames_split', but peels off frames from the left instead of from the right *)
Fixpoint frames_split {U : Set} {F : U -> U -> Set} {A B} (fs : frames_t' F A B) :
  (exists AB (g : F AB B) (gs : frames_t' F A AB), fs = <[g]> >++ gs) \/ (frames_len fs = O).
Proof.
  destruct fs as [| A' AB B' f fs] > [now right|left].
  destruct (frames_split _ _ _ _ fs) as [[AB' [g [gs Hgs]]] | Hnil].
  - subst.
    do 2 eexists; exists (gs >:: f); reflexivity.
  - destruct fs; simpl in Hnil; inversion Hnil.
    do 2 eexists; exists <[]>; reflexivity.
Qed.

(* Misc. equality experiments *)

Inductive Feq {U : Set} {F : U -> U -> Set} : forall {A B C D : U}, F A B -> F C D -> Prop :=
| Feq_refl : forall {A B} (f : F A B), Feq f f.
Infix "~=" := Feq (at level 80, no associativity).

Class UnivEq {U : Set} (F : U -> U -> Set) :=
  univ_eq : forall {A B C D : U} (f : F A B) (g : F C D), {f ~= g} + {~ (f ~= g)}.

Class EqDec A := eq_dec' : forall x y : A, {x = y} + {x <> y}.

(* Assumes there's proper EqDec instances hanging around for concrete subtrees *)
Ltac derive_UnivEq :=
  unfold UnivEq;
  intros A B C D;
  destruct A eqn:HA; rewrite <- HA; destruct C eqn:HC; rewrite <- HC;
  try solve [subst; intros f g; right; inversion 1];
  destruct B eqn:HB; rewrite <- HB; destruct D eqn:HD; rewrite <- HD;
  try solve [subst; intros f g; right; inversion 1];
  intros f g;
  destruct f; try discriminate;
  destruct g; try discriminate;
  try solve [left; apply Feq_refl|right; inversion 1; inv_ex; congruence];
  let rec gen_comparisons lhs rhs :=
    lazymatch lhs with
    | ?lf ?le =>
      lazymatch rhs with
      | ?rf ?re =>
        destruct (eq_dec' le re); [|right; inversion 1; inv_ex; congruence];
        gen_comparisons lf rf
      end
    | _ => subst; now left
    end
  in
  lazymatch goal with
  | |- {?lhs ~= ?rhs} + {~ (?lhs ~= ?rhs)} => gen_comparisons lhs rhs
  end.

(* Untyping + retyping of frames *)

Definition uframe_t {U : Set} `{H : Frame U} := {A & {B & @frame_t U H A B}}.
Definition uframes_t {U : Set} `{H : Frame U} := list (@uframe_t U H).

Fixpoint well_typed {U : Set} `{H : Frame U} (A B : U) (fs : @uframes_t U H) : Prop.
Proof.
  destruct fs as [|f fs] > [exact (A = B)|].
  destruct f as [A' [AB f]].
  exact (A = A' /\ well_typed U H AB B fs).
Defined.

Fixpoint well_typed_comp {U : Set} `{H : Frame U} (A B C : U) (fs gs : @uframes_t U H) {struct fs} :
  well_typed A B fs ->
  well_typed B C gs ->
  well_typed A C (fs ++ gs).
Proof.
  destruct fs as [|[A' [AB f]] fs].
  - cbn; intros; subst; assumption.
  - cbn; intros [HAB Hfs] Hgs; split > [assumption|eapply well_typed_comp; eauto].
Defined.

Definition untype_frame {U : Set} `{H : Frame U} {A B : U} (f : @frame_t U H A B) : @uframe_t U H.
Proof. exists A, B; exact f. Defined.

Fixpoint untype {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) : @uframes_t U H.
Proof.
  destruct fs as [|A AB B f fs] > [exact []|ltac1:(refine (_ :: _))].
  - exact (untype_frame f).
  - eapply untype; exact fs.
Defined.

Fixpoint untype_well_typed {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) :
  well_typed A B (untype fs).
Proof.
  destruct fs as [|A AB B f fs] > [reflexivity|simpl].
  split > [reflexivity|now apply untype_well_typed].
Defined.

Fixpoint retype {U : Set} `{H : Frame U} (A B : U) (fs : @uframes_t U H)
         (Hty : well_typed A B fs) {struct fs} : 
  @frames_t U H A B.
Proof.
  destruct fs as [|[A' [AB f]] fs]; simpl in Hty.
  - subst; exact <[]>.
  - destruct Hty; subst.
    ltac1:(refine (_ >:: f)).
    eapply retype; eauto.
Defined.

Definition frames_sig_t {U : Set} `{H : Frame U} A B := {fs : @uframes_t U H | well_typed A B fs}.

Definition ty_split {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) : @frames_sig_t U H A B.
Proof. exists (untype fs); ltac1:(eapply untype_well_typed; eauto). Defined.

Definition ty_merge {U : Set} `{H : Frame U} {A B : U} : @frames_sig_t U H A B -> @frames_t U H A B.
Proof. intros [fs Hfs]; ltac1:(eapply retype; eauto). Defined.

Fixpoint ty_u_ty {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B)
         (Hfs : well_typed A B (untype fs)) {struct fs} :
  retype A B (untype fs) Hfs = fs.
Proof.
  destruct fs as [|A AB B f fs]; cbn in Hfs.
  - (assert (Hfs = eq_refl) by apply UIP); subst; reflexivity.
  - destruct Hfs as [Hfs1 Hfs2]; (assert (Hfs1 = eq_refl) by apply UIP); subst; cbn.
    now rewrite ty_u_ty.
Defined.

Fixpoint t_sig_t {U : Set} `{H : Frame U} {A B : U} (fs : @frames_t U H A B) :
  ty_merge (ty_split fs) = fs.
Proof.
  destruct fs as [|A AB B f fs] > [reflexivity|simpl].
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
    ltac1:(apply (@f_equal _ _ (@proj1_sig _ _)) in sig_t_sig'; cbn in sig_t_sig').
    now rewrite sig_t_sig'.
Defined.

Definition sig_t_sig {U : Set} `{H : Frame U} {A B : U} (fs : @frames_sig_t U H A B) :
  ty_split (ty_merge fs) = fs.
Proof. destruct fs as [fs Hfs]; ltac1:(apply sig_t_sig'). Defined.

Fixpoint untype_comp {U : Set} `{H : Frame U} {A B C : U}
      (gs : @frames_t U H A B) (fs : @frames_t U H B C) {struct gs} :
  untype (fs >++ gs) = untype gs ++ untype fs.
Proof. destruct gs as [|A AB B g gs] > [reflexivity|simpl; ltac1:(congruence)]. Defined.

Lemma cong_untype {U : Set} `{H : Frame U} {A B : U} (fs gs : @frames_t U H A B) :
  fs = gs -> untype fs = untype gs.
Proof. intros; now f_equal. Defined.

Fixpoint unique_typings {U : Set} `{H : Frame U} {A B : U} (fs : @uframes_t U H)
      (Hfs Hgs : well_typed A B fs) {struct fs} :
  Hfs = Hgs.
Proof.
  destruct fs as [|[A' [AB f]] fs].
  - now apply UIP.
  - simpl in Hfs, Hgs; destruct Hfs as [Hfs1 Hfs2], Hgs as [Hgs1 Hgs2].
    assert (Hfs1 = Hgs1) by apply UIP; subst.
    specialize (unique_typings U H _ _ fs Hfs2 Hgs2); now subst.
Defined.

Fixpoint cong_retype {U : Set} `{H : Frame U} (A B : U) (fs gs : @uframes_t U H)
      (Hfs : well_typed A B fs) (Hgs : well_typed A B gs) {struct fs} :
  fs = gs -> retype A B fs Hfs = retype A B gs Hgs.
Proof. intros; subst gs; ltac1:(assert (Hfs = Hgs) by apply unique_typings); now subst. Defined.

(* -------------------- Rewriters -------------------- *)
Section Rewriters.

Context
  (* Types the rewriter will encounter + type of 1-hole contexts *)
  (U : Set) `{HFrame : Frame U}
  (* The type of trees being rewritten *)
  (Root : U).

(* State variables, parameters, and delayed computations *)
Section Strategies.

Context
  (D : Set) (I_D : forall (A : U), univD A -> D -> Prop)
  (R : Set) (I_R : forall (A : U), frames_t A Root -> R -> Prop)
  (S : Set) (I_S : forall (A : U), frames_t A Root -> univD A -> S -> Prop).

Definition Delay {A} (e : univD A) : Set := {d | I_D A e d}.
Definition Param {A} (C : erased (frames_t A Root)) : Set :=
  {r | «e_map (fun C => I_R C r) C»}.
Definition State {A} (C : erased (frames_t A Root)) (e : univD A) : Set :=
  {s | «e_map (fun C => I_S C e s) C»}.

Class Delayed := {
  delayD : forall {A} (e : univD A), Delay e -> univD A;
  delay_id : forall {A} (e : univD A), Delay e;
  delay_id_law : forall {A} (e : univD A), delayD (delay_id e) = e }.

Class Preserves_R :=
  preserve_R :
    forall {A B : U} (fs : erased (frames_t B Root)) `{e_ok _ fs} (f : frame_t A B),
    Param fs -> Param (e_map (fun fs => fs >:: f) fs).

Class Preserves_S_up :=
  preserve_S_up :
    forall {A B : U} (fs : erased (frames_t B Root)) `{e_ok _ fs} (f : frame_t A B) (x : univD A),
    State (e_map (fun fs => fs >:: f) fs) x -> State fs (frameD f x).

Class Preserves_S_dn :=
  preserve_S_dn :
    forall {A B : U} (fs : erased (frames_t B Root)) `{e_ok _ fs} (f : frame_t A B) (x : univD A),
    State fs (frameD f x) -> State (e_map (fun fs => fs >:: f) fs) x.

Extraction Inline delayD delay_id preserve_R preserve_S_up preserve_S_dn.

End Strategies.

(* Handy instances *)

(* Structures with no invariants *)

Definition I_D_plain (D : Set) (A : U) (_ : univD A) (_ : D) : Prop := True.
Definition id_Delay := @Delay unit (@I_D_plain unit).

Global Instance Delayed_id_Delay : Delayed (@I_D_plain unit).
Proof.
  ltac1:(unshelve econstructor).
  - intros A x _; exact x.
  - intros; exists tt; exact I.
  - reflexivity.
Defined.

Definition I_R_plain (R : Set) (A : U) (C : frames_t A Root) (_ : R) : Prop := True.
Definition I_S_plain (S : Set) (A : U) (C : frames_t A Root) (_ : univD A) (_ : S) : Prop := True.

Global Instance Preserves_R_plain (R : Set) : Preserves_R (@I_R_plain R).
Proof. unfold Preserves_R; intros; assumption. Defined.

Global Instance Preserves_S_up_plain (S : Set) : Preserves_S_up (@I_S_plain S).
Proof. unfold Preserves_S_up; intros; assumption. Defined.

Global Instance Preserves_S_dn_plain (S : Set) : Preserves_S_dn (@I_S_plain S).
Proof. unfold Preserves_S_dn; intros; assumption. Defined.

Extraction Inline Delayed_id_Delay Preserves_R_plain Preserves_S_up_plain Preserves_S_dn_plain.

(* Composing two parameters *)
Section R_prod.

Context
  (R1 R2 : Set)
  (I_R1 : forall A, frames_t A Root -> R1 -> Prop) 
  (I_R2 : forall A, frames_t A Root -> R2 -> Prop).

Definition I_R_prod A (C : frames_t A Root) : R1 * R2 -> Prop :=
  fun '(r1, r2) => I_R1 C r1 /\ I_R2 C r2.

Global Instance Preserves_R_prod
       `{H1 : @Preserves_R _ (@I_R1)}
       `{H2 : @Preserves_R _ (@I_R2)} :
  Preserves_R I_R_prod.
Proof.
  unfold I_R_prod; intros A B C C_ok f [[r1 r2] Hr12].
  assert (Hr1 : «e_map (fun C => I_R1 _ C r1) C»). { unerase; now destruct Hr12. }
  assert (Hr2 : «e_map (fun C => I_R2 _ C r2) C»). { unerase; now destruct Hr12. }
  pattern r1 in Hr1; pattern r2 in Hr2. apply exist in Hr1; apply exist in Hr2. clear Hr12 r1 r2.
  ltac1:(unshelve eapply preserve_R with (f := f) in Hr1); try assumption.
  ltac1:(unshelve eapply preserve_R with (f := f) in Hr2); try assumption.
  destruct Hr1 as [r1 Hr1], Hr2 as [r2 Hr2]; exists (r1, r2).
  unerase; auto.
Defined.

Extraction Inline Preserves_R_prod.

End R_prod.

(* Composing two states *)
Section S_prod.

Context
  (S1 S2 : Set)
  (I_S1 : forall A, frames_t A Root -> univD A -> S1 -> Prop) 
  (I_S2 : forall A, frames_t A Root -> univD A -> S2 -> Prop).

Definition I_S_prod A (C : frames_t A Root) (e : univD A) : S1 * S2 -> Prop :=
  fun '(s1, s2) => I_S1 C e s1 /\ I_S2 C e s2.

Global Instance Preserves_S_up_prod
         `{H1 : @Preserves_S_up _ (@I_S1)}
         `{H2 : @Preserves_S_up _ (@I_S2)} :
  Preserves_S_up I_S_prod.
Proof.
  unfold I_S_prod; intros A B C C_ok f x [[s1 s2] Hs12].
  assert (Hs1 : «e_map (fun C => I_S1 _ (C >:: f) x s1) C»). { unerase; now destruct Hs12. }
  assert (Hs2 : «e_map (fun C => I_S2 _ (C >:: f) x s2) C»). { unerase; now destruct Hs12. }
  pattern s1 in Hs1; pattern s2 in Hs2; apply exist in Hs1; apply exist in Hs2; clear Hs12 s1 s2.
  ltac1:(unshelve eapply preserve_S_up with (f := f) in Hs1); try assumption.
  ltac1:(unshelve eapply preserve_S_up with (f := f) in Hs2); try assumption.
  destruct Hs1 as [s1 Hs1], Hs2 as [s2 Hs2]; exists (s1, s2); unerase; auto.
Defined.

Global Instance Preserves_S_dn_prod
         `{H1 : @Preserves_S_dn _ (@I_S1)}
         `{H2 : @Preserves_S_dn _ (@I_S2)} :
  Preserves_S_dn I_S_prod.
Proof.
  unfold I_S_prod; intros A B C C_ok f x [[s1 s2] Hs12].
  assert (Hs1 : «e_map (fun C => I_S1 _ C (frameD f x) s1) C»). { unerase; now destruct Hs12. }
  assert (Hs2 : «e_map (fun C => I_S2 _ C (frameD f x) s2) C»). { unerase; now destruct Hs12. }
  pattern s1 in Hs1; pattern s2 in Hs2; apply exist in Hs1; apply exist in Hs2; clear Hs12 s1 s2.
  ltac1:(unshelve eapply preserve_S_dn with (f := f) in Hs1); try assumption.
  ltac1:(unshelve eapply preserve_S_dn with (f := f) in Hs2); try assumption.
  destruct Hs1 as [s1 Hs1], Hs2 as [s2 Hs2]; exists (s1, s2); unerase; auto.
Defined.

Extraction Inline Preserves_S_up_prod Preserves_S_dn_prod.

End S_prod.

Section FuelAndMetric.

Definition Fuel (fueled : bool) := if fueled then positive else unit.

Definition is_empty (fueled : bool) : Fuel fueled -> bool :=
  match fueled with
  | true => fun fuel => match fuel with xH => true | _ => false end
  | false => fun 'tt => false
  end.

Definition fuel_dec (fueled : bool) : Fuel fueled -> Fuel fueled :=
  match fueled with
  | true => fun fuel => Pos.pred fuel
  | false => fun fuel => fuel
  end.

Definition lots_of_fuel : positive := (1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1)%positive.

Extraction Inline is_empty fuel_dec lots_of_fuel.

Definition Metric (fueled : bool) :=
  if fueled then unit
  else Fuel fueled -> forall A, frames_t A Root -> univD A -> nat.

Definition run_metric (fueled : bool) (metric : Metric fueled)
           (fuel : Fuel fueled) A (C : frames_t A Root) (e : univD A) : nat :=
  match fueled return Fuel fueled -> Metric fueled -> nat with
  | true => fun fuel 'tt => Pos.to_nat fuel
  | false => fun fuel metric => metric fuel A C e
  end fuel metric.

End FuelAndMetric.

(* The type of the rewriter *)
Section Rewriter.

Context
  (* Fueled rewriters use [positive] as fuel parameter *)
  (fueled : bool)
  (Fuel := Fuel fueled)
  (metric : Metric fueled)
  (run_metric := run_metric fueled metric)
  (* One rewriting step *)
  (Rstep : relation (univD Root))
  (* Delayed computation, parameter, and state variable *)
  (D : Set) (I_D : forall (A : U), univD A -> D -> Prop)
  (R : Set) (I_R : forall (A : U), frames_t A Root -> R -> Prop)
  (S : Set) (I_S : forall (A : U), frames_t A Root -> univD A -> S -> Prop)
  `{HDelay : Delayed _ I_D}.

(* The result returned by a rewriter when called with context C and exp e *)
Record result A (C : erased (frames_t A Root)) (e : univD A) : Set := mk_result {
  resTree : univD A;
  resState : State I_S C resTree;
  resProof : «e_map (fun C => clos_refl_trans _ Rstep (C ⟦ e ⟧) (C ⟦ resTree ⟧)) C» }.

Definition rw_for (fuel : Fuel) A (C : erased (frames_t A Root)) (e : univD A) :=
  forall n `{e_ok _ n} (r : Param I_R C) (s : State I_S C e),
  «e_map (fun n => «e_map (fun C => n = run_metric fuel C e) C») n» ->
  result C e.

Definition rewriter' :=
  forall (fuel : Fuel) A (C : erased (frames_t A Root)) `{e_ok _ C} (e : univD A) (d : Delay I_D e),
  rw_for fuel C (delayD d).

Definition res_chain A (C : erased (frames_t A Root)) `{e_ok _ C} (e : univD A) (m : result C e)
           (k : forall e (s : State I_S C e), result C e) : result C e.
Proof.
  destruct m as [e' s' Hrel1]; cbn in k.
  specialize (k e' s'); destruct k as [e'' s'' Hrel2].
  econstructor > [exact s''|unerase; eapply rt_trans; eauto].
Defined.

Extraction Inline res_chain.

End Rewriter.

End Rewriters.
