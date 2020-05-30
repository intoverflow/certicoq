Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.

Require Import Ltac2.Ltac2.
Import Ltac2.Notations.
Set Default Proof Mode "Ltac2".

(* -------------------- 1-hole contexts -------------------- *)

(* One layer of a 1-hole context *)
Class Frame (U : Set) := {
  (* The type to poke holes in + all its transitive dependencies *)
  univD : U -> Set;
  (* Frames, indexed by hole type + root type *)
  frame_t : U -> U -> Set;
  (* Frame application *)
  frameD : forall {A B : U}, frame_t A B -> univD A -> univD B }.

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

Require Import Coq.Logic.Eqdep.
Ltac inv_ex :=
  repeat progress match goal with
  | H : existT ?P ?T _ = existT ?P ?T _ |- _ => apply inj_pairT2 in H
  end.

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

(* By defining a Preserves instance for some [P], the user explains:
   - How to preserve a value [P C x] which depends on the current context C + focused node x
     through each step of a (mutually) recursive traversal of a [univD Root].
   - How to preserve the same value across edits to the focused node. *)

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

(* One half of environment can only depend on context *)
Class Preserves_R_C (U : Set) `{Frame U} (Root : U)
      (P : forall {A : U}, frames_t A Root -> Set) : Set :=
  preserve_R_C :
    forall {A B : U} (fs : frames_t B Root) (f : frame_t A B) (x : univD A),
    P fs -> P (fs >:: f).

(* The other half of environment can only depend on focus *)
Class Preserves_R_e (U : Set) `{Frame U}
      (P : forall {A : U}, univD A -> Set) : Set :=
  preserve_R_e : forall {A B : U} (f : frame_t A B) (x : univD A),
    P (frameD f x) -> P x.

(* -------------------- Delayed computation -------------------- *)

(* The delayed computation may depend on the focus *)
Class Delayed {U : Set} `{Frame U} (D : forall {A}, univD A -> Set) := {
  delayD : forall {A} (e : univD A), D e -> univD A;
  delay_id : forall {A} (e : univD A), D e;
  delay_id_law : forall {A} (e : univD A), delayD e (delay_id e) = e }.

(* -------------------- Monadic operators -------------------- *)

Definition When {R S} (_ : R -> S -> bool) : Prop := True.
Definition Put {S A} (_ : S) (rhs : A) : A := rhs.
Definition Modify {S A} (_ : S -> S) (rhs : A) : A := rhs.
Definition Local {R A} (_ : R -> R) (rhs : A) : A := rhs.
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
  (* Env and state that aren't relevant to R *)
  (R_misc : Set) (S_misc : Set) 
  (* Delayed computation *)
  (D : forall A, univD A -> Set) `{@Delayed U HFrame (@D)} 
  (* Env relevant to R; depends on current context C *)
  (R_C : forall A, frames_t A root -> Set) 
  (* Env relevant to R; depends on current focus e *)
  (R_e : forall A, univD A -> Set) 
  (* State relevant to R *)
  (St : forall A, frames_t A root -> univD A -> Set).

Section Rewriters1.

(* The current context and focus *)
Context {A} (C : frames_t A root) (e : univD A).

(* The result returned by a rewriter when called with context C and exp e *)
Record result : Set := mk_result {
  resTree : univD A;
  resState : St _ C resTree;
  resSMisc : S_misc;
  resProof : clos_refl_trans _ R (C ⟦ e ⟧) (C ⟦ resTree ⟧) }.

Definition rw_for : Set := R_C _ C -> R_e _ e -> St _ C e -> result.

Definition rw_for' : Set := R_C _ C -> St _ C e -> result.

End Rewriters1.

(* The identity rewriter *)
Definition rw_id (mr : R_misc) (ms : S_misc) A (C : frames_t A root) (e : univD A) : rw_for C e.
Proof. intros r_C r_e s; econstructor > [exact s|exact ms|apply rt_refl]. Defined.

Definition rw_id' (mr : R_misc) (ms : S_misc) A (C : frames_t A root) (e : univD A) : rw_for' C e.
Proof. intros r_C s; econstructor > [exact s|exact ms|apply rt_refl]. Defined.

(* The simplest rewriter *)
Definition rw_base (mr : R_misc) (ms : S_misc) A (C : frames_t A root) (e : univD A) (d : D _ e) :
  rw_for C (delayD e d).
Proof. intros r_C r_e s; econstructor > [exact s|exact ms|apply rt_refl]. Defined.

(* Extend rw1 with rw2 *)
Definition rw_chain
  A (C : frames_t A root) (e : univD A) (d : D _ e)
  (rw1 : R_misc -> S_misc -> rw_for C (delayD e d))
  (rw2 : forall e, R_misc -> S_misc -> rw_for' C e)
  : R_misc -> S_misc -> rw_for C (delayD e d).
Proof.
  intros mr ms r_C r_e s.
  destruct (rw1 mr ms r_C r_e s) as [e' s' ms' Hrel]; clear s ms.
  destruct (rw2 e' mr ms' r_C s') as [e'' s'' ms'' Hrel']; clear s' ms'.
  econstructor > [exact s''|exact ms''|eapply rt_trans; eauto].
Defined.

End Rewriters.

Section Rewriters.

(* Here the arguments are slightly different (this matters to the MetaCoq): each combinator
   takes in two extra parameters R_misc and S_misc. *)
Context
  {U}
  `{HFrame : Frame U}
  (root : U)
  (R : relation (univD root))
  (R_misc : Set)
  (S_misc : Set)
  (mr : R_misc) (ms : S_misc)
  (R_C : forall A, frames_t A root -> Set)
  (R_e : forall A, univD A -> Set)
  (St : forall A, frames_t A root -> univD A -> Set)
  A (C : frames_t A root)
.

Definition rw_Put (new_state : S_misc) (rhs : univD A)
  (rw : R_misc -> S_misc -> rw_for root R S_misc (@R_C) (@R_e) (@St) C rhs) :
  rw_for root R S_misc (@R_C) (@R_e) (@St) C (Put new_state rhs).
Proof.
  unfold Put; intros r_C r_e s.
  (* Hack: the extra redex is to force Coq's section mechanism to include ms as a parameter. *)
  exact (rw mr ((fun _ => new_state) ms) r_C r_e s).
Defined.

Definition rw_Modify (f : S_misc -> S_misc) (rhs : univD A)
  (rw : R_misc -> S_misc -> rw_for root R S_misc (@R_C) (@R_e) (@St) C rhs) :
  rw_for root R S_misc (@R_C) (@R_e) (@St) C (Modify f rhs).
Proof.
  unfold Modify; intros r_C r_e s.
  exact (rw mr (f ms) r_C r_e s).
Defined.

Definition rw_Local (f : R_misc -> R_misc) (rhs : univD A)
  (rw : R_misc -> S_misc -> rw_for root R S_misc (@R_C) (@R_e) (@St) C rhs) :
  rw_for root R S_misc (@R_C) (@R_e) (@St) C (Local f rhs).
Proof.
  unfold Local; intros r_C r_e s.
  exact (rw (f mr) ms r_C r_e s).
Defined.

End Rewriters.
