
 
Require Import L4.instances. 


From CertiCoq.Common Require Import certiClasses certiClassesLinkable Common.

Require Import Coq.Unicode.Utf8.

Require Import ZArith.
From CertiCoq.L6 Require Import cps cps_util eval shrink_cps L5_to_L6 beta_contraction uncurry closure_conversion
     hoisting dead_param_elim lambda_lifting.
From CertiCoq.L7 Require Import L6_to_Clight.



(*
   Environment for L6 programs: 
   1 - environment of primitive operations
   2 - environment of constructors (from which datatypes can be reconstructed)
   3 - name environment mapping variables to their original name if it exists
   4 - a map from function tags to information about that class of function
*)
Let L6env : Type := prims * cEnv *  nEnv * fEnv.

Let L6term: Type := env * cps.exp.

Let L6val: Type := cps.val.

(* A: Should pr cenv env be particular values? The translation from L5a doesn't produce
  these values. If it did, we could make the terms contain this information, as in L3 *)
(* Z: pr is the primitive functions map. I don't know where it's populated or it's purpose
   in general. cenv is the tag map which maps constructor tags to info such as arity and
   which type they belong to. env is the environment that contains valuations for the free
   variables of a term.
 *)

Instance bigStepOpSemL6Term : BigStepOpSem (L6env * L6term) L6val :=
  λ p v,
  let '(pr, cenv, nenv, fenv, (rho, e)) := p in
  (* should not modify pr, cenv and nenv *)
  ∃ (n:nat), L6.eval.bstep_e pr cenv rho e v n.

Require Import certiClasses2.


(* Probably want some fact about the wellformedness of L6env w.r.t. L6term *)
Instance WfL6Term : GoodTerm (L6env * L6term) :=
  fun p =>  let '(pr, cenv, nenv, fenv, (rho, e)) := p in
         identifiers.closed_exp e /\
         identifiers.unique_bindings e.

(* FIX!! *)
Global Instance QuestionHeadTermL : QuestionHead L6val :=
fun q t => false.

(* FIX!! *)
Global Instance ObsSubtermL : ObserveNthSubterm L6val :=
fun n t => None.

Instance certiL6 : CerticoqLanguage (L6env * L6term) := {}.
Eval compute in cValue certiL6.

Instance L6_evaln: BigStepOpSemExec (cTerm certiL6) (cValue certiL6) :=
  fun n p =>
    let '((penv, cenv, nenv, fenv), (rho, e)) := p in 
    match bstep_f penv cenv rho e n with
    | exceptionMonad.Exc s => Error s None
    | Ret (inl t) => OutOfTime ((penv,cenv,nenv, fenv), t)
    | Ret (inr v) => Result v
    end.

Open Scope positive_scope.

(* starting tags for L5_to_L6, anything under default is reserved for special constructors/types *)
Definition default_cTag := 99%positive.
Definition default_iTag := 99%positive.

(* assigned for the constructor and the type of closures *)
Definition bogus_cloTag := 15%positive.
Definition bogus_cloiTag := 16%positive.

(* tags for functions and continuations *)
Definition fun_fTag := 3%positive.
Definition kon_fTag := 2%positive.

(* Let bindings for function and environment.
 * Thee function and the argument should be closed terms
 * so we do not care about capturing *)
Definition f' := 1%positive.
Definition Γ := 2%positive.

(* This is application of closure converted functions.
   We will need regular application as well. It's likely that
   only this one will be exposed. *)
(* Instance CloApp : MkApply L6term := *)
(*   mkApp (fun f xs =>  *)
(*            Eproj f' bogus_clo_tag 0%N f *)
(*                  (Eproj Γ bogus_clo_tag 1%N f *)
(*                         (Eapp f' t (Γ :: xs)))). *)

Require Import ExtLib.Data.Monads.OptionMonad.

Require Import ExtLib.Structures.Monads.



(** * Definition of L6 backend pipelines *)

Definition L6_pipeline (e : cTerm certiL5) : exception (cTerm certiL6) :=  
  match e with
  | pair venv vt =>
    match convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) with
    | Some r =>         
      let '(cenv, nenv, fenv, next_cTag, next_iTag, e) :=  r in
      let '(e, (d, s), fenv, nenv) := uncurry_fuel 100 (shrink_cps.shrink_top e) fenv nenv in   
      let (e, nenv) := inline_uncurry_contract e s 10 10 nenv in  
      let e := shrink_cps.shrink_top e in
      let '(cenv',nenv, e) := closure_conversion_hoist
                                  bogus_cloTag
                                  e
                                  next_cTag
                                  next_iTag
                                  cenv nenv
      in
      Ret ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv'), nenv, M.empty _),  (M.empty _, (shrink_top e)))
    | None => Exc "failed converting from L5 to L6"
    end
  end.

(* Optimizing L6 pipeline *)
Definition L6_pipeline_opt (e : cTerm certiL5) : exception (cTerm certiL6) :=  
  match e with
  | pair venv vt =>
    match convert_top default_cTag default_iTag fun_fTag kon_fTag (venv, vt) with
    | Some r =>
      let '(cenv, nenv, fenv, next_cTag, next_iTag, e) :=  r in
      let '(e, (d, s), fenv, nenv) := uncurry_fuel 100 (shrink_cps.shrink_top e) fenv nenv in   
      let (e, nenv) := inline_uncurry_contract e s 10 10 nenv in  
      let e := shrink_cps.shrink_top e in
      (* Lambda Lifting *)
      let (e, nenv) := lambda_lift' e next_iTag nenv in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* closure conversion + hoisting *)
      let '(cenv',nenve, e) := closure_conversion_hoist
                                  bogus_cloTag
                                  e
                                  next_cTag
                                  next_iTag
                                  cenv nenv
      in
      (* Shrink reduction *)
      let e := shrink_cps.shrink_top e in
      (* Dead parameter elimination *)
      let e := dead_param_elim.eliminate e in
      let e := shrink_cps.shrink_top e in
      Ret ((M.empty _ , (add_cloTag bogus_cloTag bogus_cloiTag cenv'), nenv, M.empty _),  (M.empty _, (shrink_top e)))
    | None => Exc "failed converting from L5 to L6"
    end
  end.

(* TODOs for optimized pipeline:
   
   1. Hoist only closed functions 
   2. Run hoisting before CC, to find top-level functions, and not closure convert them
*)

Instance certiL5_t0_L6: 
  CerticoqTranslation (cTerm certiL5) (cTerm certiL6) :=
  fun o => match o with
        | Flag 0 => L6_pipeline
        | Flag _ => L6_pipeline_opt
        end.