From Coq Require Import ZArith.ZArith Lists.List Strings.String.
Import ListNotations.

From MetaCoq Require Import Template.All.

From CertiCoq.L6 Require Import PrototypeGenFrame cps.

Run TemplateProgram (mk_Frame_ops
  "exp" exp [var; fun_tag; ctor_tag; prim; N; list var]).
Print exp_univ.
Print exp_univD.

Instance Frame_exp : Frame exp_univ := exp_Frame_ops.
Instance AuxData_exp : AuxData exp_univ := exp_aux_data.
