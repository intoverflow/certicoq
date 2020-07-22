(* Expressions and contexts isomorphic to those defined in cps.v and ctx.v.
   We define a separate copy of these because:
   - The MetaCoq in Prototype.v doesn't support treating AST types defined with type aliases
     like [var] and [fun_tag] differently. This version of the AST defines them as singleton
     inductives.
   - Prototype.v additionally generates a type of one-hole contexts for [exp] trees and
     we have to explain how this type relates to [exp_ctx] and [fundefs_ctx].

   The actual definition of [exp] is in cps_proto_metacoq.v because the MetaCoq takes a
   lot of time and space (~6 GB) to run (most of this is for quoting exp_aux_data). *)

From Coq Require Import ZArith.ZArith Lists.List Sets.Ensembles.
Require Import Lia.
Import ListNotations.

Require Import CertiCoq.L6.Prototype.

Require Export CertiCoq.L6.cps_proto_metacoq.
Print exp_univ.
Print exp_univD.
Print exp_frame_t.
Print exp_frameD.
Print exp_Frame_ops.

Require CertiCoq.L6.cps.
From CertiCoq.L6 Require Import identifiers ctx Ensembles_util.

(* The type of one-hole contexts *)
Definition exp_c : exp_univ -> exp_univ -> Set := frames_t.

Module M := cps.M.

(* -------------------- exp is isomorphic to cps.exp -------------------- *)

Definition strip_vars : list var -> list cps.var := map (fun '(mk_var x) => x).

Lemma strip_vars_app xs ys : strip_vars (xs ++ ys) = strip_vars xs ++ strip_vars ys.
Proof. unfold strip_vars; now rewrite map_app. Qed.

Definition fundefs := list fundef.

Definition fundefs_of_proto' exp_of_proto :=
  fold_right
    (fun '(Ffun (mk_var f) (mk_fun_tag ft) xs e) fds =>
      cps.Fcons f ft (strip_vars xs) (exp_of_proto e) fds)
    cps.Fnil.
Definition ce_of_proto' exp_of_proto : ctor_tag * exp -> cps.ctor_tag * cps.exp :=
  fun '(mk_ctor_tag c, e) => (c, exp_of_proto e).
Definition ces_of_proto' exp_of_proto := map (ce_of_proto' exp_of_proto).

Fixpoint exp_of_proto (e : exp) : cps.exp :=
  match e with
  | Econstr (mk_var x) (mk_ctor_tag c) ys e => cps.Econstr x c (strip_vars ys) (exp_of_proto e)
  | Ecase (mk_var x) ces => cps.Ecase x (ces_of_proto' exp_of_proto ces)
  | Eproj (mk_var x) (mk_ctor_tag c) n (mk_var y) e => cps.Eproj x c n y (exp_of_proto e)
  | Eletapp (mk_var x) (mk_var f) (mk_fun_tag ft) ys e =>
    cps.Eletapp x f ft (strip_vars ys) (exp_of_proto e)
  | Efun fds e => cps.Efun (fundefs_of_proto' exp_of_proto fds) (exp_of_proto e)
  | Eapp (mk_var f) (mk_fun_tag ft) xs => cps.Eapp f ft (strip_vars xs)
  | Eprim (mk_var x) (mk_prim p) ys e => cps.Eprim x p (strip_vars ys) (exp_of_proto e)
  | Ehalt (mk_var x) => cps.Ehalt x
  end.

Definition ce_of_proto := ce_of_proto' exp_of_proto.
Definition ces_of_proto := ces_of_proto' exp_of_proto.
Definition fundefs_of_proto := fundefs_of_proto' exp_of_proto.

Definition proto_of_ce' proto_of_exp : cps.ctor_tag * cps.exp -> ctor_tag * exp :=
  fun '(c, e) => (mk_ctor_tag c, proto_of_exp e).
Definition proto_of_ces' proto_of_exp := map (proto_of_ce' proto_of_exp).

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
    Ffun (mk_var f) (mk_fun_tag ft) (map mk_var xs) (proto_of_exp e) :: proto_of_fundefs fds
  | cps.Fnil => []
  end.

Definition proto_of_ce := proto_of_ce' proto_of_exp.
Definition proto_of_ces := proto_of_ces' proto_of_exp.

Lemma strip_vars_map xs : strip_vars (map mk_var xs) = xs.
Proof. induction xs as [|x xs IHxs]; simpl; congruence. Qed.

Fixpoint exp_proto_exp e : exp_of_proto (proto_of_exp e) = e.
Proof.
  destruct e; simpl; try rewrite strip_vars_map; try congruence.
  induction l as [ | [c e] ces IHces]; [reflexivity|]; simpl.
  inversion IHces.
  repeat rewrite H0.
  repeat f_equal.
  now apply exp_proto_exp.
  induction f as [f ft xs e_body fds IHfds|]; [cbn|now rewrite exp_proto_exp].
  inversion IHfds.
  now rewrite H0, H0, H1, H1, strip_vars_map, exp_proto_exp.
Qed.

Lemma fundefs_proto_fundefs fds : fundefs_of_proto (proto_of_fundefs fds) = fds.
Proof.
  pose (H := exp_proto_exp (cps.Efun fds (cps.Ehalt xH))); clearbody H; cbn in H.
  inversion H; now rewrite H1.
Qed.

Lemma ces_proto_ces ces : ces_of_proto (proto_of_ces ces) = ces.
Proof. induction ces as [| [c e] ces IHces]; [reflexivity|simpl]; now rewrite exp_proto_exp, IHces. Qed.

Lemma map_strip_vars xs : map mk_var (strip_vars xs) = xs.
Proof. induction xs as [| [x] xs IHxs]; simpl; congruence. Qed.

Local Ltac destruct_sings :=
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x as [x]; simpl end.

Fixpoint proto_exp_proto e : proto_of_exp (exp_of_proto e) = e.
Proof.
  destruct e; simpl; destruct_sings; try rewrite map_strip_vars; try congruence.
  induction ces as [| [[c] e] ces IHces]; [reflexivity|]; simpl.
  inversion IHces.
  repeat rewrite H0.
  repeat f_equal.
  now apply proto_exp_proto.
  induction fds as [| [[f] [ft] xs e_body] fds IHfds]; [now rewrite proto_exp_proto|cbn].
  inversion IHfds; repeat rewrite H0, H1; now rewrite map_strip_vars, proto_exp_proto.
Qed.

Lemma proto_fundefs_proto fds : proto_of_fundefs (fundefs_of_proto fds) = fds.
Proof.
  pose (H := proto_exp_proto (Efun fds (Ehalt (mk_var xH)))); clearbody H; cbn in H.
  inversion H; now rewrite H1.
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
with c_of_fundefs_ctx (C : fundefs_ctx) : exp_c exp_univ_exp exp_univ_list_fundef.
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
        <[cons_fundef0 (proto_of_fundefs fds); Ffun3 (mk_var f) (mk_fun_tag ft) (map mk_var xs)]>
          >++ c_of_exp_ctx C
      | Fcons2_c f ft xs e C =>
        <[cons_fundef1 (Ffun (mk_var f) (mk_fun_tag ft) (map mk_var xs) (proto_of_exp e))]>
          >++ c_of_fundefs_ctx C
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
  | exp_univ_list_fundef => fundefs_ctx
  | exp_univ_fundef => cps.var * cps.fun_tag * list cps.var * exp_ctx
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
  - exact (fun ctx => (v, f0, strip_vars l, ctx)).
  - exact (fun '(f, ft, xs, ctx) => Fcons1_c f ft xs ctx (fundefs_of_proto l)).
  - destruct f0 as [[f0] [ft] xs e].
    exact (fun ctx => Fcons2_c f0 ft (strip_vars xs) (exp_of_proto e) ctx).
  - exact (fun ctx => Econstr_c v c (strip_vars l) ctx).
  - exact (fun '(ces1, c, e, ces2) => Ecase_c v ces1 c e ces2).
  - exact (fun ctx => Eproj_c v c n v0 ctx).
  - exact (fun ctx => Eletapp_c v v0 f0 (strip_vars l) ctx).
  - exact (fun ctx => Efun2_c ctx (exp_of_proto e)).
  - exact (fun ctx => Efun1_c (fundefs_of_proto l) ctx).
  - exact (fun ctx => Eprim_c v p (strip_vars l) ctx).
Defined.

Fixpoint exp_c_rep {A B} (C : exp_c A B) : univ_rep A -> univ_rep B :=
  match C with
  | <[]> => fun x => x
  | C >:: f => fun x => exp_c_rep C (exp_frame_rep f x)
  end.

Definition exp_ctx_of_c (C : exp_c exp_univ_exp exp_univ_exp) : exp_ctx :=
  exp_c_rep C Hole_c.

Definition fundefs_ctx_of_c (C : exp_c exp_univ_exp exp_univ_list_fundef) : fundefs_ctx :=
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
  | exp_univ_exp, exp_univ_fundef => fun C =>
    let '(f, ft, xs, ctx) := exp_c_rep C Hole_c in
    <[Ffun3 (mk_var f) (mk_fun_tag ft) (map mk_var xs)]> >++ c_of_exp_ctx ctx = C
  | exp_univ_exp, exp_univ_list_fundef => fun C => c_of_fundefs_ctx (fundefs_ctx_of_c C) = C
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
  - destruct g, A; try exact I;
      try match goal with f : fundef |- _ => destruct f as [f ft xs e] end;
      unbox_newtypes; simpl;
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
      try solve [erewrite IHn; eauto; rewrite frames_len_compose; simpl; lia].
    + destruct (exp_c_rep gs Hole_c) as [c e] eqn:Hce.
      unfold c_of_ces_ctx, c_of_ces_ctx'; simpl; normalize_roundtrips'.
      specialize IHn with (C := gs).
      rewrite Hce in IHn.
      erewrite <- IHn; eauto; [|rewrite frames_len_compose; simpl; lia].
      now rewrite frames_rev_assoc.
    + destruct (exp_c_rep gs Hole_c) as [[[ces1 c] e] ces2] eqn:Hces12.
      destruct p as [[c'] e']; simpl.
      unfold c_of_ces_ctx, c_of_ces_ctx' in *; simpl; normalize_roundtrips'.
      specialize IHn with (C := gs).
      rewrite Hces12 in IHn.
      erewrite <- IHn; eauto; [|rewrite frames_len_compose; simpl; lia].
      now rewrite frames_rev_assoc.
    + destruct (exp_c_rep gs Hole_c) as [[[f ft] xs] ctx] eqn:Hces12.
      simpl; unfold c_of_ces_ctx, c_of_ces_ctx' in *; simpl; normalize_roundtrips'.
      specialize IHn with (C := gs).
      rewrite Hces12 in IHn.
      erewrite <- IHn; eauto; [now rewrite frames_rev_assoc|]; rewrite frames_len_compose; simpl; lia.
    + destruct (exp_c_rep gs Hole_c) as [[[ces1 c] e] ces2] eqn:Hces12.
      simpl; unfold c_of_ces_ctx, c_of_ces_ctx' in *; simpl; normalize_roundtrips'.
      specialize IHn with (C := gs).
      rewrite Hces12 in IHn.
      erewrite <- IHn; eauto; rewrite frames_len_compose; simpl; lia.
  - destruct C; simpl in Hnil; inversion Hnil.
    destruct A; try exact I; reflexivity.
Qed.

Corollary c_exp_ctx_c (C : exp_c exp_univ_exp exp_univ_exp) :
  c_of_exp_ctx (exp_ctx_of_c C) = C.
Proof. apply (c_ctx_c C). Qed.

Corollary c_fundefs_ctx_c (C : exp_c exp_univ_exp exp_univ_list_fundef) :
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

Instance Iso_ces : Iso (list (ctor_tag * exp)) (list (cps.ctor_tag * cps.exp)) := {
  isoAofB := proto_of_ces;
  isoBofA := ces_of_proto;
  isoABA := proto_ces_proto;
  isoBAB := ces_proto_ces }.

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

Instance Iso_fundefs_c_fundefs_ctx : Iso (exp_c exp_univ_exp exp_univ_list_fundef) fundefs_ctx := {
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
  app_f_ctx_f C e = ![([C]! : exp_c exp_univ_exp exp_univ_list_fundef) ⟦ [e]! ⟧].
Proof.
  all: destruct C; simpl;
    try lazymatch goal with
    | |- context [(?fs >++ ?gs) ⟦ _ ⟧] =>
      rewrite (@frames_compose_law exp_univ Frame_exp _ _ _ fs gs)
    end; simpl; normalize_roundtrips; try reflexivity;
    try solve [(rewrite <- app_exp_ctx_eq + rewrite <- app_fundefs_ctx_eq); reflexivity].
  - f_equal.
    unfold c_of_ces_ctx'.
    repeat rewrite frames_compose_law.
    rewrite <- (proto_exp_proto (c_of_exp_ctx C ⟦ proto_of_exp e ⟧)).
    rewrite <- app_exp_ctx_eq.
    simpl.
    assert (Harms : forall ces1 ces2, c_of_ces ces1 ⟦ ces2 ⟧ = proto_of_ces ces1 ++ ces2). {
      clear; induction ces1 as [| [c e] ces1 IHces]; intros ces2; [reflexivity|].
      unfold c_of_ces; now rewrite fold_right_cons, frames_compose_law, IHces. }
    unfold ces_of_proto'; rewrite Harms, map_app; normalize_roundtrips.
    now rewrite ces_proto_ces.
  - change (fundefs_of_proto' exp_of_proto) with fundefs_of_proto; now rewrite <- app_fundefs_ctx_eq.
Qed.

Local Ltac mk_corollary parent :=
  apply iso_BofA_inj; simpl; repeat normalize_roundtrips;
  symmetry; apply parent.

Corollary app_exp_c_eq (C : exp_c exp_univ_exp exp_univ_exp) :
  forall e, C ⟦ e ⟧ = [![C] |[ ![e] ]|]!.
Proof. iso C; intros e; iso e; mk_corollary app_exp_ctx_eq. Qed.

Corollary app_f_exp_c_eq (C : exp_c exp_univ_exp exp_univ_list_fundef) :
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

(* ---------- Facts about used variables ---------- *)

Fixpoint used_ces (ces : list (ctor_tag * exp)) : Ensemble cps.var :=
  match ces with
  | [] => Empty_set _
  | (_, e) :: ces => used_vars ![e] :|: used_ces ces
  end.

Definition used {A} : univD A -> Ensemble cps.var :=
  match A with
  | exp_univ_prod_ctor_tag_exp => fun '(_, e) => used_vars ![e]
  | exp_univ_list_prod_ctor_tag_exp => used_ces
  | exp_univ_fundef => fun '(Ffun (mk_var x) _ xs e) => x |: FromList ![xs] :|: used_vars ![e]
  | exp_univ_list_fundef => fun fds => used_vars_fundefs ![fds]
  | exp_univ_exp => fun e => used_vars ![e]
  | exp_univ_var => fun '(mk_var x) => [set x]
  | exp_univ_fun_tag => fun _ => Empty_set _
  | exp_univ_ctor_tag => fun _ => Empty_set _
  | exp_univ_prim => fun _ => Empty_set _
  | exp_univ_N => fun _ =>  Empty_set _
  | exp_univ_list_var => fun xs => FromList ![xs]
  end.

(*
(* TODO: use a prettier definition in terms of greatest lower bound of all [frameD f x]s.
   Then show that for every hole type can find x1, x2 such that
     glb_x (frameD f x) = frameD f x1 ∩ frameD f x2 *)
Definition used_c {A B} (C : exp_c A B) : Ensemble cps.var :=
  fun x => forall e, In _ (used (C ⟦ e ⟧)) x.

Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

Local Ltac insts_disagree H spec1 spec2 :=
  pose (Hx1 := H spec1); clearbody Hx1; simpl in Hx1;
  pose (Hx2 := H spec2); clearbody Hx2; simpl in Hx2;
  repeat normalize_used_vars; inversion Hx1; now inversion Hx2.

Lemma used_c_nil {A} : used_c (<[]> : exp_c A A) <--> Empty_set _.
Proof.
  split; [|auto with Ensembles_DB].
  intros x Hx; unfold In, used_c in Hx; simpl in Hx.
  destruct A; simpl in Hx.
  - insts_disagree Hx (mk_ctor_tag xH, Ehalt (mk_var xH)) (mk_ctor_tag xH, Ehalt (mk_var (xO xH))).
  - specialize (Hx []); assumption.
  - specialize (Hx Fnil); simpl in Hx; now normalize_used_vars.
  - insts_disagree Hx (Ehalt (mk_var xH)) (Ehalt (mk_var (xO xH))).
  - insts_disagree Hx (mk_var xH) (mk_var (xO xH)).
  - apply Hx; exact (mk_fun_tag xH).
  - apply Hx; exact (mk_ctor_tag xH).
  - apply Hx; exact (mk_prim xH).
  - apply Hx; exact N0.
  - specialize (Hx []); inversion Hx.
Qed. *)

Definition used_frame {A B} (f : exp_frame_t A B) : Ensemble cps.var. refine (
  match f with
  | pair_ctor_tag_exp0 e => used_vars ![e]
  | pair_ctor_tag_exp1 c => Empty_set _
  | cons_prod_ctor_tag_exp0 ces => used_ces ces
  | cons_prod_ctor_tag_exp1 (_, e) => used_vars ![e]
  | Ffun0 ft xs e => FromList ![xs] :|: used_vars ![e] 
  | Ffun1 f xs e => ![f] |: FromList ![xs] :|: used_vars ![e] 
  | Ffun2 f ft e => ![f] |: used_vars ![e] 
  | Ffun3 f ft xs => ![f] |: FromList ![xs] 
  | cons_fundef0 fds => used_vars_fundefs ![fds]
  | cons_fundef1 fd => @used exp_univ_fundef fd
  | Econstr0 c ys e => FromList ![ys] :|: used_vars ![e]
  | Econstr1 x ys e => ![x] |: FromList ![ys] :|: used_vars ![e]
  | Econstr2 x c e => ![x] |: used_vars ![e]
  | Econstr3 x c ys => ![x] |: FromList ![ys]
  | Ecase0 ces => used_ces ces
  | Ecase1 x => [set ![x]]
  | Eproj0 c n y e => ![y] |: used_vars ![e]
  | Eproj1 x n y e => ![x] |: (![y] |: used_vars ![e])
  | Eproj2 x c y e => ![x] |: (![y] |: used_vars ![e])
  | Eproj3 x c n e => ![x] |: used_vars ![e]
  | Eproj4 x c n y => ![x] |: [set ![y]]
  | Eletapp0 f ft ys e => ![f] |: FromList ![ys] :|: used_vars ![e]
  | Eletapp1 x ft ys e => ![x] |: FromList ![ys] :|: used_vars ![e]
  | Eletapp2 x f ys e => ![x] |: (![f] |: FromList ![ys] :|: used_vars ![e])
  | Eletapp3 x f ft e => ![x] |: (![f] |: used_vars ![e])
  | Eletapp4 x f ft ys => ![x] |: (![f] |: FromList ![ys])
  | Efun0 e => used_vars ![e]
  | Efun1 fds => used_vars_fundefs ![fds]
  | Eapp0 ft xs => FromList ![xs]
  | Eapp1 f xs => ![f] |: FromList ![xs]
  | Eapp2 f ft => [set ![f]]
  | Eprim0 p ys e => FromList ![ys] :|: used_vars ![e]
  | Eprim1 x ys e => ![x] |: FromList ![ys] :|: used_vars ![e]
  | Eprim2 x p e => ![x] |: used_vars ![e]
  | Eprim3 x p ys => ![x] |: FromList ![ys]
  | Ehalt0 => Empty_set _
  end).
Defined.

Lemma used_frameD {A B} (f : exp_frame_t A B) (x : univD A) :
  used (frameD f x) <--> used_frame f :|: used x.
Proof.
  destruct f; simpl in *|-;
  repeat (
    try match goal with p : _ * _ |- _ => destruct p | f : fundef |- _ => destruct f end;
    unbox_newtypes); simpl;
  repeat normalize_used_vars;
  repeat normalize_sets;
  try solve [rewrite Ensemble_iff_In_iff; intros arbitrary; repeat rewrite In_or_Iff_Union; tauto].
  - induction l as [| [[c] e] ces IHces]; simpl; repeat normalize_used_vars; [eauto with Ensembles_DB|].
    rewrite IHces; eauto with Ensembles_DB.
  - induction x as [| [[c] e] ces IHces]; simpl; repeat normalize_used_vars; [eauto with Ensembles_DB|].
    rewrite IHces; eauto with Ensembles_DB.
Qed.

Fixpoint used_c {A B} (C : exp_c A B) : Ensemble cps.var :=
  match C with
  | <[]> => Empty_set _
  | C >:: f => used_c C :|: used_frame f
  end.

Fixpoint used_c_comp {A B root} (C : exp_c B root) (D : exp_c A B) {struct D} :
  used_c (C >++ D) <--> used_c C :|: used_c D.
Proof. destruct D; simpl; [|rewrite used_c_comp]; eauto with Ensembles_DB. Qed.

Fixpoint used_app {A B} (C : exp_c A B) (e : univD A) {struct C} :
  used (C ⟦ e ⟧) <--> used_c C :|: used e.
Proof.
  destruct C; simpl; [eauto with Ensembles_DB|].
  rewrite used_app, used_frameD; eauto with Ensembles_DB.
Qed.

Definition used_iso (e : cps.exp) : used_vars e <--> @used exp_univ_exp [e]!.
Proof. simpl; normalize_roundtrips; reflexivity. Qed.

Definition used_vars_iso (e : univD exp_univ_exp) : used e <--> used_vars ![e].
Proof. reflexivity. Qed.

(* Useful fact for some of the passes: every C : exp_c exp_univ_fundefs exp_univ_exp
   can be decomposed into D, fds, e such that C = D ∘ (Efun (rev fds ++ _) e) *)

Fixpoint ctx_of_fds (fds : fundefs) : exp_c exp_univ_list_fundef exp_univ_list_fundef :=
  match fds with
  | [] => <[]>
  | fd :: fds => ctx_of_fds fds >:: cons_fundef1 fd
  end.

Lemma ctx_of_fds_app (fds1 : list fundef) : forall fds2 : fundefs,
  ctx_of_fds fds1 ⟦ fds2 ⟧ = rev fds1 ++ fds2.
Proof.
  induction fds1 as [| [f ft xs e] fds1 IHfds1]; [reflexivity|].
  simpl; intros fds2; rewrite IHfds1, <- app_assoc; reflexivity.
Qed.

Fixpoint decompose_fd_c' {A B} (C : exp_c A B) {struct C} :
  match A as A', B as B' return exp_c A' B' -> Set with
  | exp_univ_list_fundef, exp_univ_exp => fun C => {'(D, fds, e) | C = D >:: Efun0 e >++ ctx_of_fds fds}
  | _, _ => fun _ => unit
  end C.
Proof.
  destruct C as [|A AB B f C]; [destruct A; exact tt|destruct f, B; try exact tt].
  - specialize (decompose_fd_c' exp_univ_list_fundef exp_univ_exp C); simpl in decompose_fd_c'.
    destruct decompose_fd_c' as [[[C' fds'] e'] HCfdse'].
    exists (C', f :: fds', e'); now simpl.
  - exists (C, [], e); now simpl.
Defined.

Definition decompose_fd_c := @decompose_fd_c' exp_univ_list_fundef exp_univ_exp.

(* Misc. facts that may or may not be useful when dealing with dependently typed [exp_c]s *)

Instance Iso_frames {U : Set} `{H : Frame U} {A B : U} : Iso (@frames_t U H A B) (@frames_sig_t U H A B) := {
  isoAofB := ty_merge;
  isoBofA := ty_split;
  isoABA := t_sig_t;
  isoBAB := sig_t_sig }.

Instance exp_Frame_inj : Frame_inj (U:=exp_univ).
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

Instance Inhabited_list A : Inhabited (list A) := [].
Instance Inhabited_prod A B `{Inhabited A} `{Inhabited B} : Inhabited (A * B) := (inhabitant, inhabitant).

Instance Inhabited_exp : Inhabited exp := Ehalt inhabitant.
Instance Inhabited_fundef : Inhabited fundef := Ffun inhabitant inhabitant inhabitant inhabitant.

Definition univ_inhabitant {A} : univD A :=
  match A with
  | exp_univ_prod_ctor_tag_exp => inhabitant
  | exp_univ_list_prod_ctor_tag_exp => inhabitant
  | exp_univ_fundef => inhabitant
  | exp_univ_list_fundef => inhabitant
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
Instance Inhabited'_fundef : Inhabited' fundef := Ffun inhabitant' inhabitant' inhabitant' inhabitant'.

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

Instance Sized_var : Sized var := fun _ => S O.
Instance Sized_fun_tag : Sized fun_tag := fun _ => S O.
Instance Sized_ctor_tag : Sized ctor_tag := fun _ => S O.
Instance Sized_prim : Sized prim := fun _ => S O.
Instance Sized_N : Sized N := fun _ => S O.

Definition size_list {A} (size : A -> nat) : list A -> nat := fold_right (fun x n => S (size x + n)) 1%nat.
Definition size_prod {A B} (sizeA : A -> nat) (sizeB : B -> nat) : A * B -> nat := fun '(x, y) => S (sizeA x + sizeB y).

Instance Size_list A `{Sized A} : Sized (list A) := size_list size.
Instance Size_prod A B `{Sized A} `{Sized B} : Sized (A * B) := size_prod size size.

Definition size_fundef' size_exp : fundef -> nat :=
  fun '(Ffun f ft xs e) => S (size f + size ft + size xs + size_exp e).
Definition size_fundefs' size_exp := size_list (size_fundef' size_exp).

Fixpoint size_exp (e : exp) : nat.
Proof.
- refine (match e with
  | Econstr x c ys e => S (size x + size c + size ys + size_exp e)
  | Ecase x ces => S (size x + size_list (size_prod size size_exp) ces)
  | Eproj x c n y e => S (size x + size c + size n + size y + size_exp e)
  | Eletapp x f ft ys e => S (size x + size f + size ft + size ys + size_exp e)
  | Efun fds e => S (size_fundefs' size_exp fds + size_exp e)
  | Eapp f ft xs => S (size f + size ft + size xs)
  | Eprim x p ys e => S (size x + size p + size ys + size_exp e)
  | Ehalt x => S (size x)
  end).
Defined.

Instance Sized_exp : Sized exp := size_exp.
Instance Sized_fundef : Sized fundef := size_fundef' size_exp.

Definition univ_size {A} : univD A -> nat :=
  match A with
  | exp_univ_prod_ctor_tag_exp => size
  | exp_univ_list_prod_ctor_tag_exp => size
  | exp_univ_fundef => size
  | exp_univ_list_fundef => size
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
  try change (size_fundefs' size x) with (size x); cbn;
  try change (size_list (size_prod size size) x) with (size x); cbn;
  try change (size x) with 1; cbn;
  try lia.
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

