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

(* -------------------- 1-hole contexts built from frames -------------------- *)

Class Frame_inj (U : Set) `{Frame U} :=
  frame_inj :
    forall {A B : U} (f : frame_t A B) (x y : univD A),
    frameD f x = frameD f y -> x = y.

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

(* By defining a Preserves instance for some [P], the user explains:
   - How to preserve a value [P C x] which depends on the current context C + focused node x
     through each step of a (mutually) recursive traversal of a [univD Root].
   - How to preserve the same value across edits to the focused node. *)

(* The environment can only depend on context *)
Class Preserves_R (U : Set) `{Frame U} (Root : U)
      (P : forall {A : U}, frames_t A Root -> Set) : Set :=
  preserve_R :
    forall {A B : U} (fs : frames_t B Root) (f : frame_t A B),
    P fs -> P (fs >:: f).

(* State can depend on both context and value on focus, and needs to be preserved while moving
   upwards and downwards *)
Class Preserves_S (U : Set) `{Frame U} (Root : U)
      (P : forall {A : U}, frames_t A Root -> univD A -> Set) : Set := {
  preserve_S_up :
    forall {A B : U} (fs : frames_t B Root) (f : frame_t A B) (x : univD A),
    P (fs >:: f) x -> P fs (frameD f x);
  preserve_S_dn :
    forall {A B : U} (fs : frames_t B Root) (f : frame_t A B) (x : univD A),
    P fs (frameD f x) -> P (fs >:: f) x }.

(* -------------------- Delayed computation -------------------- *)

(* The delayed computation may depend on the focus *)
Class Delayed {U : Set} `{Frame U} (D : forall {A}, univD A -> Set) := {
  delayD : forall {A} (e : univD A), D e -> univD A;
  delay_id : forall {A} (e : univD A), D e;
  delay_id_law : forall {A} (e : univD A), delayD e (delay_id e) = e }.

(* -------------------- Handy instances -------------------- *)

Definition trivial_R_C {U : Set} `{Frame U} {Root : U} A (C : frames_t A Root) : Set := unit.
Instance Preserves_R_trivial_R_C {U : Set} `{H : Frame U} {Root : U} :
  Preserves_R _ Root (@trivial_R_C U H Root).
Proof. constructor. Defined.

Definition trivial_S {U : Set} `{Frame U} {Root : U} A (C : frames_t A Root) (e : univD A) : Set := unit.
Instance Preserves_S_trivial_S {U : Set} `{H : Frame U} {Root : U} :
  Preserves_S _ Root (@trivial_S U H Root).
Proof. do 2 constructor. Defined.

Definition trivial_delay_t {U : Set} `{Frame U} A (e : univD A) : Set := unit.
Instance Delayed_trivial_delay_t {U : Set} `{H : Frame U} : Delayed (@trivial_delay_t U H).
Proof. ltac1:(unshelve econstructor; [intros A e _; exact e|..]; reflexivity). Defined.

(* Parameters and state variables with no invariants *)

Definition R_plain {U : Set} `{Frame U} {Root : U}
           (R : Set) A (C : frames_t A Root) : Set :=
  R.

Instance Preserves_R_R_plain (U : Set) `{Frame U} (Root : U) (R : Set) :
  Preserves_R _ Root (R_plain R).
Proof. intros A B fs x s; exact s. Defined.

Definition S_plain {U : Set} `{Frame U} {Root : U}
           (S : Set) A (C : frames_t A Root) (e : univD A) : Set :=
  S.

Instance Preserves_S_S_plain (U : Set) `{Frame U} (Root : U) (S : Set) :
  Preserves_S _ Root (S_plain S).
Proof. constructor; intros A B fs f x s; exact s. Defined.

(* Composing two parameters *)

Definition R_prod {U : Set} `{Frame U} {Root : U}
           (R1 R2 : forall {A}, frames_t A Root -> Set) 
           A (C : frames_t A Root) : Set :=
  R1 C * R2 C.

Instance Preserves_R_R_prod {U : Set} `{H : Frame U} {Root : U}
         (R1 R2 : forall {A}, frames_t A Root -> Set) 
         `{H1 : @Preserves_R U H Root (@R1)} 
         `{H2 : @Preserves_R U H Root (@R2)} :
  Preserves_R _ Root (R_prod (@R1) (@R2)).
Proof. unfold R_prod; intros A B fs f [s1 s2]; split; now eapply @preserve_R. Defined.

(* Composing two states *)

Definition S_prod {U : Set} `{Frame U} {Root : U}
           (S1 S2 : forall {A}, frames_t A Root -> univD A -> Set) 
           A (C : frames_t A Root) (e : univD A) : Set :=
  S1 C e * S2 C e.

Instance Preserves_S_S_prod {U : Set} `{H : Frame U} {Root : U}
         (S1 S2 : forall A, frames_t A Root -> univD A -> Set)
         `{H1 : @Preserves_S U H Root S1} 
         `{H2 : @Preserves_S U H Root S2} :
  Preserves_S _ Root (S_prod S1 S2).
Proof.
  constructor; unfold S_prod; intros A B fs f x [s1 s2]; split;
  try (now eapply @preserve_S_up); (now eapply @preserve_S_dn).
Defined.

(* -------------------- Annotations -------------------- *)

Definition Rec {A} (rhs : A) : A := rhs.
Definition BottomUp {A} (rhs : A) : A := rhs.

(* -------------------- The type of the rewriter -------------------- *)

Section Rewriters.

Context
  (* Types the rewriter will encounter + type of 1-hole contexts *)
  {U} `{HFrame : Frame U} 
  (* The type of trees being rewritten *)
  (root : U) 
  (* One rewriting step *)
  (R : relation (univD root)) 
  (* Delayed computation *)
  (D : forall A, univD A -> Set) `{@Delayed U HFrame (@D)} 
  (* Env relevant to R; depends on current context C *)
  (R_C : forall A, frames_t A root -> Set) 
  (* State relevant to R *)
  (St : forall A, frames_t A root -> univD A -> Set).

Section Rewriters1.

(* The current context and focus *)
Context {A} (C : frames_t A root) (e : univD A).

(* The result returned by a rewriter when called with context C and exp e *)
Record result : Set := mk_result {
  resTree : univD A;
  resState : St _ C resTree;
  resProof : clos_refl_trans _ R (C ⟦ e ⟧) (C ⟦ resTree ⟧) }.

Definition rw_for : Set := R_C _ C -> St _ C e -> result.

End Rewriters1.

(* The identity rewriter *)
Definition rw_id A (C : frames_t A root) (e : univD A) : rw_for C e.
Proof. intros r s; econstructor > [exact s|apply rt_refl]. Defined.

(* The simplest rewriter *)
Definition rw_base A (C : frames_t A root) (e : univD A) (d : D _ e) :
  rw_for C (delayD e d).
Proof. intros r s; econstructor > [exact s|apply rt_refl]. Defined.

(* Extend rw1 with rw2 *)
Definition rw_chain
  A (C : frames_t A root) (e : univD A) (d : D _ e)
  (rw1 : rw_for C (delayD e d)) (rw2 : forall e, rw_for C e)
  : rw_for C (delayD e d).
Proof.
  intros r s.
  destruct (rw1 r s) as [e' s' Hrel]; clear s.
  destruct (rw2 e' r s') as [e'' s'' Hrel']; clear s'.
  econstructor > [exact s''|eapply rt_trans; eauto].
Defined.

End Rewriters.

Definition Fuel := positive.

Definition lots_of_fuel : Fuel := (1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1)%positive.

Require Import Lia.

Definition Fuel_Fix {A} (d : A) (f : A -> A) : Fuel -> A.
Proof.
  apply (@Fix positive Pos.lt Coqlib.Plt_wf (fun _ => A)); intros n rec.
  destruct n as [n'|n'|] eqn:Hn > [| |exact d]; ltac1:(refine (f (rec (Pos.pred n) _)); lia).
Defined.
