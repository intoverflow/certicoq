(* Expressions and contexts isomorphic to those defined in cps.v and ctx.v.
   We define a separate copy of these because:
   - The MetaCoq in Prototype.v doesn't support treating AST types defined with type aliases
     like [var] and [fun_tag] differently. This version of the AST defines them as singleton
     inductives.
   - Prototype.v additionally generates a type of one-hole contexts for [exp] trees and
     we have to explain how this type relates to [exp_ctx] and [fundefs_ctx].

   The actual definition of [exp] is in cps_proto_metacoq.v because the MetaCoq takes a
   lot of time and space (~6 GB) to run (most of this is for quoting exp_aux_data). *)

From Coq Require Import ZArith.ZArith Lists.List.
Import ListNotations.

Require Import CertiCoq.L6.Prototype.

Require Export CertiCoq.L6.cps_proto_metacoq.
Print exp_univ.
Print exp_univD.
Print exp_frame_t.
Print exp_frameD.
Print exp_Frame_ops.

Require CertiCoq.L6.cps.
Require Import CertiCoq.L6.ctx.

(* The type of one-hole contexts *)
Definition exp_c : exp_univ -> exp_univ -> Set := frames_t.

(* The type of finite maps, restricted to Set (MetaCoq struggles a bit with Type) *)
Definition PM : Set -> Set := Maps.PTree.tree.
Module PM := Maps.PTree.

(* -------------------- exp is isomorphic to cps.exp -------------------- *)

Definition strip_vars : list var -> list cps.var := map (fun '(mk_var x) => x).

Fixpoint exp_of_proto (e : exp) : cps.exp :=
  match e with
  | Econstr (mk_var x) (mk_ctor_tag c) ys e => cps.Econstr x c (strip_vars ys) (exp_of_proto e)
  | Ecase (mk_var x) ces => cps.Ecase x (map (fun '(mk_ctor_tag c, e) => (c, exp_of_proto e)) ces)
  | Eproj (mk_var x) (mk_ctor_tag c) n (mk_var y) e => cps.Eproj x c n y (exp_of_proto e)
  | Eletapp (mk_var x) (mk_var f) (mk_fun_tag ft) ys e =>
    cps.Eletapp x f ft (strip_vars ys) (exp_of_proto e)
  | Efun fds e => cps.Efun (fundefs_of_proto fds) (exp_of_proto e)
  | Eapp (mk_var f) (mk_fun_tag ft) xs => cps.Eapp f ft (strip_vars xs)
  | Eprim (mk_var x) (mk_prim p) ys e => cps.Eprim x p (strip_vars ys) (exp_of_proto e)
  | Ehalt (mk_var x) => cps.Ehalt x
  end
with fundefs_of_proto (fds : fundefs) : cps.fundefs :=
  match fds with
  | Fcons (mk_var f) (mk_fun_tag ft) xs e fds =>
    cps.Fcons f ft (strip_vars xs) (exp_of_proto e) (fundefs_of_proto fds)
  | Fnil => cps.Fnil
  end.
Definition ce_of_proto := fun '(mk_ctor_tag c, e) => (c, exp_of_proto e).
Definition ces_of_proto := map ce_of_proto.

Fixpoint proto_of_exp (e : cps.exp) : exp :=
  match e with
  | cps.Econstr x c ys e => Econstr (mk_var x) (mk_ctor_tag c) (map mk_var ys) (proto_of_exp e)
  | cps.Ecase x ces => Ecase (mk_var x) (map (fun '(c, e) => (mk_ctor_tag c, proto_of_exp e)) ces)
  | cps.Eproj x c n y e => Eproj (mk_var x) (mk_ctor_tag c) n (mk_var y) (proto_of_exp e)
  | cps.Eletapp x f ft ys e =>
    Eletapp (mk_var x) (mk_var f) (mk_fun_tag ft) (map mk_var ys) (proto_of_exp e)
  | cps.Efun fds e => Efun (proto_of_fundefs fds) (proto_of_exp e)
  | cps.Eapp f ft ys => Eapp (mk_var f) (mk_fun_tag ft) (map mk_var ys)
  | cps.Eprim x p ys e => Eprim (mk_var x) (mk_prim p) (map mk_var ys) (proto_of_exp e)
  | cps.Ehalt x => Ehalt (mk_var x)
  end
with proto_of_fundefs (fds : cps.fundefs) : fundefs :=
  match fds with
  | cps.Fcons f ft xs e fds =>
    Fcons (mk_var f) (mk_fun_tag ft) (map mk_var xs) (proto_of_exp e) (proto_of_fundefs fds)
  | cps.Fnil => Fnil
  end.
Definition proto_of_ce := fun '(c, e) => (mk_ctor_tag c, proto_of_exp e).
Definition proto_of_ces := map proto_of_ce.

Lemma strip_vars_map xs : strip_vars (map mk_var xs) = xs.
Proof. induction xs as [|x xs IHxs]; simpl; congruence. Qed.

Fixpoint exp_proto_exp e : exp_of_proto (proto_of_exp e) = e
with fundefs_proto_fundefs fds : fundefs_of_proto (proto_of_fundefs fds) = fds.
Proof.
  - destruct e; simpl; try rewrite strip_vars_map; try congruence.
    induction l as [ | [c e] ces IHces]; [reflexivity|]; simpl.
    inversion IHces.
    repeat rewrite H0.
    repeat f_equal.
    now apply exp_proto_exp.
  - destruct fds; simpl; try rewrite strip_vars_map; congruence.
Qed.

Lemma ces_proto_ces ces : ces_of_proto (proto_of_ces ces) = ces.
Proof. induction ces as [| [c e] ces IHces]; [reflexivity|simpl]; now rewrite exp_proto_exp, IHces. Qed.

Lemma map_strip_vars xs : map mk_var (strip_vars xs) = xs.
Proof. induction xs as [| [x] xs IHxs]; simpl; congruence. Qed.

Local Ltac destruct_sings :=
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x as [x]; simpl end.

Fixpoint proto_exp_proto e : proto_of_exp (exp_of_proto e) = e
with proto_fundefs_proto fds : proto_of_fundefs (fundefs_of_proto fds) = fds.
Proof.
  - destruct e; simpl; destruct_sings; try rewrite map_strip_vars; try congruence.
    induction ces as [| [[c] e] ces IHces]; [reflexivity|]; simpl.
    inversion IHces.
    repeat rewrite H0.
    repeat f_equal.
    now apply proto_exp_proto.
  - destruct fds; simpl; destruct_sings; try rewrite map_strip_vars; congruence.
Qed.

Lemma proto_ces_proto ces : proto_of_ces (ces_of_proto ces) = ces.
Proof.
  induction ces as [| [[c] e] ces IHces]; [reflexivity|simpl];
  now rewrite proto_exp_proto, IHces.
Qed.

(* ---------- exp_c with the right indices is isomorphic to cps.exp_ctx and cps.fundefs_ctx ---------- *)

(* cps.exp_ctx -> exp_c _ _ *)

Definition c_of_ces (ces : list (cps.ctor_tag * cps.exp)) :
  exp_c exp_univ_list_prod_ctor_tag_exp exp_univ_list_prod_ctor_tag_exp :=
  fold_right
    (fun '(c, e) frames =>
      <[cons_prod_ctor_tag_exp1 (mk_ctor_tag c, proto_of_exp e)]> >++ frames)
    <[]>
    ces.

Definition c_of_ces_ctx' c_of_exp_ctx (ces1 : list (cps.ctor_tag * cps.exp)) (c : cps.ctor_tag)
           (C : exp_ctx) (ces2 : list (cps.ctor_tag * cps.exp))
  : exp_c exp_univ_exp exp_univ_list_prod_ctor_tag_exp :=
  c_of_ces ces1
    >++ <[cons_prod_ctor_tag_exp0 (proto_of_ces ces2); pair_ctor_tag_exp1 (mk_ctor_tag c)]>
    >++ c_of_exp_ctx C.

Fixpoint c_of_exp_ctx (C : exp_ctx) : exp_c exp_univ_exp exp_univ_exp
with c_of_fundefs_ctx (C : fundefs_ctx) : exp_c exp_univ_exp exp_univ_fundefs.
Proof.
  - refine (
      match C with
      | Hole_c => <[]>
      | Econstr_c x c ys C => <[Econstr3 (mk_var x) (mk_ctor_tag c) (map mk_var ys)]> >++ c_of_exp_ctx C
      | Eproj_c x c n y C => <[Eproj4 (mk_var x) (mk_ctor_tag c) n (mk_var y)]> >++ c_of_exp_ctx C
      | Eprim_c x p ys C => <[Eprim3 (mk_var x) (mk_prim p) (map mk_var ys)]> >++ c_of_exp_ctx C
      | Eletapp_c x f ft ys C =>
        <[Eletapp4 (mk_var x) (mk_var f) (mk_fun_tag ft) (map mk_var ys)]> >++ c_of_exp_ctx C
      | Ecase_c x ces1 c C ces2 => <[Ecase1 (mk_var x)]> >++ c_of_ces_ctx' c_of_exp_ctx ces1 c C ces2
      | Efun1_c fds C => <[Efun1 (proto_of_fundefs fds)]> >++ c_of_exp_ctx C
      | Efun2_c C e => <[Efun0 (proto_of_exp e)]> >++ c_of_fundefs_ctx C
      end).
  - refine (
      match C with
      | Fcons1_c f ft xs C fds =>
        <[Fcons3 (mk_var f) (mk_fun_tag ft) (map mk_var xs) (proto_of_fundefs fds)]> >++ c_of_exp_ctx C
      | Fcons2_c f ft xs e C =>
        <[Fcons4 (mk_var f) (mk_fun_tag ft) (map mk_var xs) (proto_of_exp e)]> >++ c_of_fundefs_ctx C
      end).
Defined.

Definition c_of_ces_ctx := c_of_ces_ctx' c_of_exp_ctx.

(* exp_c _ _ -> cps.exp_ctx: directly writing a recursive function on exp_c is annoying because
   of the indices. Instead map each frame to a "slice" of an exp_ctx represented as a function 
   ctx |-> slice + ctx. Then all the functions can be composed together and initialized with 
   the empty context. *)

Inductive zero : Set :=.
Definition univ_rep (A : exp_univ) : Set :=
  match A with
  | exp_univ_prod_ctor_tag_exp => cps.ctor_tag * exp_ctx
  | exp_univ_list_prod_ctor_tag_exp =>
    list (cps.ctor_tag * cps.exp) * cps.ctor_tag * exp_ctx * list (cps.ctor_tag * cps.exp)
  | exp_univ_fundefs => fundefs_ctx
  | exp_univ_exp => exp_ctx
  | exp_univ_var => zero
  | exp_univ_fun_tag => zero
  | exp_univ_ctor_tag => zero
  | exp_univ_prim => zero
  | exp_univ_N => zero
  | exp_univ_list_var => zero
  end.

Ltac unbox_newtypes :=
  repeat lazymatch goal with
  | x : var |- _ => destruct x as [x]
  | x : prim |- _ => destruct x as [x]
  | x : fun_tag |- _ => destruct x as [x]
  | x : ctor_tag |- _ => destruct x as [x]
  end.

Definition exp_frame_rep {A B} (f : exp_frame_t A B) : univ_rep A -> univ_rep B.
Proof.
  destruct f eqn:Hf; simpl; unbox_newtypes;
  try lazymatch goal with |- zero -> _ => inversion 1 end.
  - exact (fun ctx => (c, ctx)).
  - exact (fun '(c, e) => ([], c, e, ces_of_proto l)).
  - exact (fun '(ces1, c, e, ces2) => (ce_of_proto p :: ces1, c, e, ces2)).
  - exact (fun ctx => Fcons1_c v f0 (strip_vars l) ctx (fundefs_of_proto f1)).
  - exact (fun ctx => Fcons2_c v f0 (strip_vars l) (exp_of_proto e) ctx).
  - exact (fun ctx => Econstr_c v c (strip_vars l) ctx).
  - exact (fun '(ces1, c, e, ces2) => Ecase_c v ces1 c e ces2).
  - exact (fun ctx => Eproj_c v c n v0 ctx).
  - exact (fun ctx => Eletapp_c v v0 f0 (strip_vars l) ctx).
  - exact (fun ctx => Efun2_c ctx (exp_of_proto e)).
  - exact (fun ctx => Efun1_c (fundefs_of_proto f0) ctx).
  - exact (fun ctx => Eprim_c v p (strip_vars l) ctx).
Defined.

Fixpoint exp_c_rep {A B} (C : exp_c A B) : univ_rep A -> univ_rep B :=
  match C with
  | <[]> => fun x => x
  | C >:: f => fun x => exp_c_rep C (exp_frame_rep f x)
  end.

Definition exp_ctx_of_c (C : exp_c exp_univ_exp exp_univ_exp) : exp_ctx :=
  exp_c_rep C Hole_c.

Definition fundefs_ctx_of_c (C : exp_c exp_univ_exp exp_univ_fundefs) : fundefs_ctx :=
  exp_c_rep C Hole_c.

Fixpoint exp_c_rep_compose {A B C} (fs : exp_c A B) (gs : exp_c B C) x {struct fs} :
  exp_c_rep (gs >++ fs) x = exp_c_rep gs (exp_c_rep fs x).
Proof.
  destruct fs as [ |A' AB B' f fs]; [reflexivity|simpl].
  now rewrite exp_c_rep_compose.
Qed.

Local Ltac normalize_roundtrips' :=
  try rewrite exp_c_rep_compose; simpl;
  try rewrite strip_vars_map;
  try rewrite exp_proto_exp;
  try rewrite ces_proto_ces;
  try rewrite fundefs_proto_fundefs;
  try rewrite map_strip_vars;
  try rewrite proto_exp_proto;
  try rewrite proto_ces_proto;
  try rewrite proto_fundefs_proto.

(* exp_ctx -> exp_c -> exp_ctx *)

Lemma fold_right_cons {A B} (f : A -> B -> B) z x xs :
  fold_right f z (x :: xs) = f x (fold_right f z xs).
Proof. reflexivity. Qed.

Lemma ces_ctx_c_ces_ctx : forall ces ces1 c C ces2,
  exp_c_rep (c_of_ces ces) (ces1, c, C, ces2) = (ces ++ ces1, c, C, ces2).
Proof.
  clear; induction ces as [| [c e] ces IHces]; [reflexivity|]; intros ces1 ctr C ces2.
  unfold c_of_ces; rewrite fold_right_cons, exp_c_rep_compose.
  rewrite IHces; simpl; now normalize_roundtrips'.
Qed.

Fixpoint exp_ctx_c_exp_ctx (C : exp_ctx) : exp_ctx_of_c (c_of_exp_ctx C) = C
with fundefs_ctx_c_fundefs_ctx (C : fundefs_ctx) : fundefs_ctx_of_c (c_of_fundefs_ctx C) = C.
Proof.
  all: unfold exp_ctx_of_c, fundefs_ctx_of_c in *;
    destruct C; simpl;
    try reflexivity;
    normalize_roundtrips';
    try solve [(rewrite exp_ctx_c_exp_ctx + rewrite fundefs_ctx_c_fundefs_ctx); reflexivity].
  unfold c_of_ces_ctx'.
  rewrite exp_c_rep_compose.
  normalize_roundtrips'.
  now rewrite ces_ctx_c_ces_ctx, app_nil_r, exp_ctx_c_exp_ctx.
Qed.

(* exp_c -> exp_ctx -> exp_c: because exp_c is 'inside-out', destructing normally
   on (C : exp_c _ _) yields subcases like
     c_of_foo (foo_of_c (C >:: f)) = C
     <=> c_of_foo (exp_c_rep C (exp_frame_rep f Hole_c)) = C
   which isn't helpful because c_of_foo is stuck: exp_c_rep won't spit out a constructor
   until its consumed the rest of C.

   Fix: split C into <[]> and <[g]> >++ gs cases and use exp_c_rep_compose:
     c_of_foo (foo_of_c (<[f]> >++ C)) = C
     <=> c_of_foo (exp_c_rep (<[f]> >++ C Hole_c)) = C
     <=> c_of_foo (exp_c_rep <[f]> (exp_c_rep C Hole_c)) = C
     <=> c_of_foo (exp_frame_rep f (exp_c_rep C Hole_c)) = C
   [exp_frame_rep f] will expose constructors for c_of_foo. *)

Definition c_ctx_c_stmt {A B} : exp_c A B -> Prop :=
  match A, B with
  | exp_univ_exp, exp_univ_exp => fun C => c_of_exp_ctx (exp_ctx_of_c C) = C
  | exp_univ_exp, exp_univ_fundefs => fun C => c_of_fundefs_ctx (fundefs_ctx_of_c C) = C
  | exp_univ_exp, exp_univ_prod_ctor_tag_exp => fun C =>
    let '(c, ctx) := exp_c_rep C Hole_c in
    <[pair_ctor_tag_exp1 (mk_ctor_tag c)]> >++ c_of_exp_ctx ctx = C
  | exp_univ_exp, exp_univ_list_prod_ctor_tag_exp => fun C =>
    let '(ces1, c, ctx, ces2) := exp_c_rep C Hole_c in
    c_of_ces_ctx ces1 c ctx ces2 = C
  | _, _ => fun _ => True
  end.

Lemma c_ctx_c {A B} (C : exp_c A B) : c_ctx_c_stmt C.
Proof.
  remember (frames_len C) as n eqn:Heqn; generalize dependent C; revert A B.
  induction n as [n IHn] using lt_wf_ind.
  intros A B C Hlen.
  destruct (frames_split C) as [[AB [g [gs Hgs]]] | Hnil].
  - destruct g, A; try exact I; unbox_newtypes; simpl;
      unfold exp_ctx_of_c, fundefs_ctx_of_c;
      subst C n; try rewrite exp_c_rep_compose; simpl;
      try match goal with
      | |- context [match ?e with end] =>
        let H := fresh "H" in assert (H : zero) by exact e; inversion H
      end;
      match goal with |- context [exp_c_rep gs Hole_c] =>
        match type of gs with
        | frames_t' _ ?hole ?root =>
          specialize IHn with (A := hole) (B := root);
          unfold c_ctx_c_stmt in IHn;
          unfold exp_ctx_of_c, fundefs_ctx_of_c in IHn
        end
      end;
      normalize_roundtrips';
      try solve [erewrite IHn; eauto; rewrite frames_len_compose; simpl; omega].
    + destruct (exp_c_rep gs Hole_c) as [c e] eqn:Hce.
      unfold c_of_ces_ctx, c_of_ces_ctx'; simpl; normalize_roundtrips'.
      specialize IHn with (C := gs).
      rewrite Hce in IHn.
      erewrite <- IHn; eauto; [|rewrite frames_len_compose; simpl; omega].
      now rewrite frames_rev_assoc.
    + destruct (exp_c_rep gs Hole_c) as [[[ces1 c] e] ces2] eqn:Hces12.
      destruct p as [[c'] e']; simpl.
      unfold c_of_ces_ctx, c_of_ces_ctx' in *; simpl; normalize_roundtrips'.
      specialize IHn with (C := gs).
      rewrite Hces12 in IHn.
      erewrite <- IHn; eauto; [|rewrite frames_len_compose; simpl; omega].
      now rewrite frames_rev_assoc.
    + destruct (exp_c_rep gs Hole_c) as [[[ces1 c] e] ces2] eqn:Hces12.
      simpl; unfold c_of_ces_ctx, c_of_ces_ctx' in *; simpl; normalize_roundtrips'.
      specialize IHn with (C := gs).
      rewrite Hces12 in IHn.
      erewrite <- IHn; eauto; rewrite frames_len_compose; simpl; omega.
  - destruct C; simpl in Hnil; inversion Hnil.
    destruct A; try exact I; reflexivity.
Qed.

Corollary c_exp_ctx_c (C : exp_c exp_univ_exp exp_univ_exp) :
  c_of_exp_ctx (exp_ctx_of_c C) = C.
Proof. apply (c_ctx_c C). Qed.

Corollary c_fundefs_ctx_c (C : exp_c exp_univ_exp exp_univ_fundefs) :
  c_of_fundefs_ctx (fundefs_ctx_of_c C) = C.
Proof. apply (c_ctx_c C). Qed.

Ltac normalize_roundtrips :=
  try rewrite exp_c_rep_compose; simpl;
  try rewrite strip_vars_map in *;
  try rewrite exp_proto_exp in *;
  try rewrite ces_proto_ces in *;
  try rewrite fundefs_proto_fundefs in *;
  try rewrite map_strip_vars in *;
  try rewrite proto_exp_proto in *;
  try rewrite proto_ces_proto in *;
  try rewrite proto_fundefs_proto in *;
  try rewrite c_exp_ctx_c in *;
  try rewrite c_fundefs_ctx_c in *;
  try rewrite exp_ctx_c_exp_ctx in *;
  try rewrite fundefs_ctx_c_fundefs_ctx in *.

(* ---------- package all the above together ---------- *)

Class Iso A B := {
  isoAofB : B -> A;
  isoBofA : A -> B;
  isoABA : forall x, isoAofB (isoBofA x) = x;
  isoBAB : forall x, isoBofA (isoAofB x) = x }.

Notation "'![' e ']'" := (isoBofA e).
Notation "'[' e ']!'" := (isoAofB e).

Instance Iso_var : Iso var cps.var := {
  isoAofB := mk_var;
  isoBofA := un_var;
  isoABA := fun '(mk_var x) => eq_refl;
  isoBAB := fun x => eq_refl }.

Instance Iso_vars : Iso (list var) (list cps.var) := {
  isoAofB := map mk_var;
  isoBofA := strip_vars;
  isoABA := map_strip_vars;
  isoBAB := strip_vars_map }.

Instance Iso_fun_tag : Iso fun_tag cps.fun_tag := {
  isoAofB := mk_fun_tag;
  isoBofA := un_fun_tag;
  isoABA := fun '(mk_fun_tag x) => eq_refl;
  isoBAB := fun x => eq_refl }.

Instance Iso_ctor_tag : Iso ctor_tag cps.ctor_tag := {
  isoAofB := mk_ctor_tag;
  isoBofA := un_ctor_tag;
  isoABA := fun '(mk_ctor_tag x) => eq_refl;
  isoBAB := fun x => eq_refl }.

Instance Iso_prim : Iso prim cps.prim := {
  isoAofB := mk_prim;
  isoBofA := un_prim;
  isoABA := fun '(mk_prim x) => eq_refl;
  isoBAB := fun x => eq_refl }.

Instance Iso_exp : Iso exp cps.exp := {
  isoAofB := proto_of_exp;
  isoBofA := exp_of_proto;
  isoABA := proto_exp_proto;
  isoBAB := exp_proto_exp }.

Instance Iso_fundefs : Iso fundefs cps.fundefs := {
  isoAofB := proto_of_fundefs;
  isoBofA := fundefs_of_proto;
  isoABA := proto_fundefs_proto;
  isoBAB := fundefs_proto_fundefs }.

Instance Iso_exp_c_exp_ctx : Iso (exp_c exp_univ_exp exp_univ_exp) exp_ctx := {
  isoAofB := c_of_exp_ctx;
  isoBofA := exp_ctx_of_c;
  isoABA := c_exp_ctx_c;
  isoBAB := exp_ctx_c_exp_ctx }.

Instance Iso_fundefs_c_fundefs_ctx : Iso (exp_c exp_univ_exp exp_univ_fundefs) fundefs_ctx := {
  isoAofB := c_of_fundefs_ctx;
  isoBofA := fundefs_ctx_of_c;
  isoABA := c_fundefs_ctx_c;
  isoBAB := fundefs_ctx_c_fundefs_ctx }.

Lemma iso_proof {A B} `{Iso A B} (P : A -> Prop) (Hxy : forall y, P [y]!) : forall x, P x.
Proof.
  intros x; specialize (Hxy ![x]).
  now rewrite isoABA in Hxy.
Qed.

Ltac iso x := pattern x; revert x; apply iso_proof; intros x.

Lemma iso_BofA_inj {A B} `{Iso A B} x y : ![x] = ![y] -> x = y.
Proof.
  intros Heq; apply f_equal with (f := fun x => [x]!) in Heq.
  now repeat rewrite isoABA in Heq.
Qed.

Lemma iso_AofB_inj {A B} `{Iso A B} x y : [x]! = [y]! -> x = y.
Proof.
  intros Heq; apply f_equal with (f := fun x => ![x]) in Heq.
  now repeat rewrite isoBAB in Heq.
Qed.

(* ---------- exp_c application agrees with app_ctx_f + app_f_ctx_f ---------- *)

Fixpoint app_exp_ctx_eq (C : exp_ctx) e {struct C} :
  C |[ e ]| = ![([C]! : exp_c exp_univ_exp exp_univ_exp) ⟦ [e]! ⟧]
with app_fundefs_ctx_eq (C : fundefs_ctx) e {struct C} :
  app_f_ctx_f C e = ![([C]! : exp_c exp_univ_exp exp_univ_fundefs) ⟦ [e]! ⟧].
Proof.
  all: destruct C; simpl;
    try lazymatch goal with
    | |- context [(?fs >++ ?gs) ⟦ _ ⟧] =>
      rewrite (@frames_compose_law exp_univ Frame_exp _ _ _ fs gs)
    end; simpl; normalize_roundtrips; try reflexivity;
    try solve [(rewrite <- app_exp_ctx_eq + rewrite <- app_fundefs_ctx_eq); reflexivity].
  f_equal.
  unfold c_of_ces_ctx'.
  repeat rewrite frames_compose_law.
  rewrite <- (proto_exp_proto (c_of_exp_ctx C ⟦ proto_of_exp e ⟧)).
  rewrite <- app_exp_ctx_eq.
  simpl.
  assert (Harms : forall ces1 ces2, c_of_ces ces1 ⟦ ces2 ⟧ = proto_of_ces ces1 ++ ces2). {
    clear; induction ces1 as [| [c e] ces1 IHces]; intros ces2; [reflexivity|].
    unfold c_of_ces; now rewrite fold_right_cons, frames_compose_law, IHces. }
  rewrite Harms, map_app; normalize_roundtrips.
  now rewrite ces_proto_ces.
Qed.

Local Ltac mk_corollary parent :=
  apply iso_BofA_inj; simpl; repeat normalize_roundtrips;
  symmetry; apply parent.

Corollary app_exp_c_eq (C : exp_c exp_univ_exp exp_univ_exp) :
  forall e, C ⟦ e ⟧ = [![C] |[ ![e] ]|]!.
Proof. iso C; intros e; iso e; mk_corollary app_exp_ctx_eq. Qed.

Corollary app_f_exp_c_eq (C : exp_c exp_univ_exp exp_univ_fundefs) :
  forall e, C ⟦ e ⟧ = [app_f_ctx_f ![C] ![e]]!.
Proof. iso C; intros e; iso e; mk_corollary app_fundefs_ctx_eq. Qed.

(* ---------- exp_c composition agrees with comp_ctx_f + comp_f_ctx_f ---------- *)

Local Ltac fold_exp_c_reps :=
  lazymatch goal with
  | |- context [exp_c_rep ?C Hole_c] =>
    lazymatch type of C with
    | exp_c exp_univ_exp exp_univ_exp => change (exp_c_rep C Hole_c) with (exp_ctx_of_c C)
    end
  | H : context [exp_c_rep ?C Hole_c] |- _ =>
    lazymatch type of C with
    | exp_c exp_univ_exp exp_univ_exp => change (exp_c_rep C Hole_c) with (exp_ctx_of_c C) in H
    end
  end.

Fixpoint comp_exp_ctx_eq C D {struct C} : comp_ctx_f C D = ![[C]! >++ [D]!]
with comp_fundefs_ctx_eq C D {struct C} : comp_f_ctx_f C D = ![[C]! >++ [D]!].
Proof.
  all: simpl in *; destruct C; simpl; unfold exp_ctx_of_c, fundefs_ctx_of_c;
    repeat rewrite exp_c_rep_compose; simpl;
    fold_exp_c_reps; normalize_roundtrips; f_equal; try solve
    [reflexivity
    |match goal with
      | |- _ ?C ?D = _ =>
        let use_IH IH1 IH2 :=
          specialize (IH1 C D); clear IH2;
          unfold exp_ctx_of_c, fundefs_ctx_of_c in IH1;
          rewrite exp_c_rep_compose in IH1
        in
        use_IH comp_exp_ctx_eq comp_fundefs_ctx_eq + use_IH comp_fundefs_ctx_eq comp_exp_ctx_eq
     end; unfold exp_ctx_of_c in *;
     fold_exp_c_reps; normalize_roundtrips; assumption].
  unfold c_of_ces_ctx'.
  repeat rewrite exp_c_rep_compose; simpl.
  rewrite ces_ctx_c_ces_ctx, app_nil_r; normalize_roundtrips; f_equal.
  specialize (comp_exp_ctx_eq C D); unfold exp_ctx_of_c in comp_exp_ctx_eq.
  rewrite exp_c_rep_compose in comp_exp_ctx_eq; fold_exp_c_reps; now normalize_roundtrips.
Qed.

Corollary comp_exp_c_eq C D : C >++ D = [comp_ctx_f ![C] ![D]]!.
Proof. revert D; iso C; intros D; iso D; mk_corollary comp_exp_ctx_eq. Qed.

Corollary comp_fundefs_c_eq C D : C >++ D = [comp_f_ctx_f ![C] ![D]]!.
Proof. revert D; iso C; intros D; iso D; mk_corollary comp_fundefs_ctx_eq. Qed.
