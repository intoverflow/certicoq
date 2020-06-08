From Coq Require Import ZArith.ZArith Lists.List Strings.String.
Import ListNotations.

From MetaCoq Require Import Template.All.

From CertiCoq.L6 Require Import Prototype.

Unset Strict Unquote Universe Mode.

Inductive var      := mk_var : positive -> var.
Inductive fun_tag  := mk_fun_tag : positive -> fun_tag.
Inductive ctor_tag := mk_ctor_tag : positive -> ctor_tag.
Inductive prim     := mk_prim : positive -> prim.

Definition un_var := fun '(mk_var x) => x.
Definition un_fun_tag := fun '(mk_fun_tag x) => x.
Definition un_ctor_tag := fun '(mk_ctor_tag x) => x.
Definition un_prim := fun '(mk_prim x) => x.

Inductive exp : Type :=
| Econstr (x : var) (c : ctor_tag) (ys : list var) (e : exp)
| Ecase (x : var) (ces : list (ctor_tag * exp))
| Eproj (x : var) (c : ctor_tag) (n : N) (y : var) (e : exp)
| Eletapp (x : var) (f : var) (ft : fun_tag) (ys : list var) (e : exp)
| Efun (fds : list fundef) (e : exp)
| Eapp (f : var) (ft : fun_tag) (xs : list var)
| Eprim (x : var) (p : prim) (ys : list var) (e : exp)
| Ehalt (x : var)
with fundef : Type :=
| Ffun (f : var) (ft : fun_tag) (xs : list var) (e : exp).

(* Takes a while to save aux_data *)
Run TemplateProgram (mk_Frame_ops
  "exp" exp [var; fun_tag; ctor_tag; prim; N; list var]).

Instance Frame_exp : Frame exp_univ := exp_Frame_ops.
Instance AuxData_exp : AuxData exp_univ := exp_aux_data.
