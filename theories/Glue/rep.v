(*
  Author: Joomy Korkut (joomy@cs.princeton.edu), 2020

  Generator for the [rep] relation for a given Coq type.

  The [rep] function should match on a Coq value of a given type,
  and check if a C value represents that Coq value
  the same way CertiCoq represents it.

  This is similar to the pattern in VST but instead of [T -> val -> mpred],
  our [rep] function has the type [graph -> T -> mtype -> Prop],
  for a given [T].

  This file defines a [Rep] type class containing the [rep] relation,
  and it also defines a MetaCoq program that generates a [Rep] instance
  for a given Coq type.

  Currently our generator works on:
  [x] simple types like [bool]
  [x] recursive types like [nat]
  [ ] mutually recursive types like [even] and [odd]
  [ ] polymorphic types like [option]
  [ ] multi-polymorphic types like [pair]
  [ ] recursive and polymorphic types like [list]
  [ ] recursive and dependent types like [fin]
  [ ] recursive, polymorphic and dependent types like [vector]
  [ ] types of sort Prop like [True], [and] or [le]
  [ ] types that use functions in its definition

  Game plan:
  * Take a type constructor (in Coq, not reified) as an input.
  * Recursively quote the type constructor, get a type environment as well.
  * The type environment consists of mutual inductive type declarations.
  * For every type in every mutual block,
    find out if there is a [Rep] instance for it,
    and remember it in a list of lists.
    * In order to find out the [Rep] instance, you have to
      quantify over all parameters and indices.
  * If a block is missing any instance,
    define type class instances for each type in the block.

  Caveats:
  * If a type is of sort [Prop], the representation of its values is
    the same as [unit] for all vallues.
  * Parameters are not included in the memory representation,
    indices are. But parameters should be quantified over in the [Rep] instance type.
*)
Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

From MetaCoq.Template Require Import BasicAst.
Require Import MetaCoq.Template.All.

Require Import glue_utils.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MonadNotation
       ListNotations
       MetaCoqNotations.

Require CertiCoq.L6.Prototype.
(* Alias to distinguish terms that are NOT in de Bruijn notation. *)
Definition named_term : Type := term.
(* Alias for terms that do not contain references to local variables,
   therefore can be used in either [term]s in de Bruijn notation
   and [named_term]s in named notation. *)
Definition global_term : Type := term.
(* Alias to denote that a function works with
   either [term], [named_term] or [global_term]. *)
Definition any_term : Type := term.

Module DB.
  (* Uses code written by John Li.
     We should eventually consider making a MetaCoq_utils module. *)
  Import Prototype.

  Definition runGM {A : Type} (m : GM A) : TemplateMonad A :=
    match runStateT m 0%N with
    | inl err => tmFail err
    | inr (t', _) => ret t'
    end.

  (* Takes a named representation, which we hack by using names starting with $,
     and converts it into the de Bruijn representation. *)
  Definition deBruijn (t : named_term) : TemplateMonad term :=
    runGM (indices_of [] t).

  (* Example usage for deBruijn:

     MetaCoq Run (t <- DB.deBruijn
                          (tLambda (nNamed "$x") <% bool %> (tVar "$x")) ;;
                  t' <- tmUnquoteTyped (bool -> bool) t ;;
                  tmPrint t).
  *)

  (* Takes a de Bruijn representation and adds $ to local variables,
     and changes [tRel]s to [tVar]s referring to those variabstarting with $. *)
  Definition undeBruijn (initial : list ident)
                        (t : term) : TemplateMonad named_term :=
    runGM (named_of initial t).

  (* Example usage for undeBruijn:

     MetaCoq Run (t <- DB.undeBruijn nil <% fun (x : bool) => x %> ;;
                  tmPrint t).
  *)
End DB.


Module Substitution.
  (* Capturing substitution for named terms, only use for global terms. *)
  Fixpoint named_subst (t : global_term) (x : ident) (u : named_term) {struct u} : named_term :=
    match u with
    | tVar id => if eq_string id x then t else u
    | tEvar ev args => tEvar ev (map (named_subst t x) args)
    | tCast c kind ty => tCast (named_subst t x c) kind (named_subst t x ty)
    | tProd (nNamed id) A B =>
      if eq_string x id
      then tProd (nNamed id) (named_subst t x A) B
      else tProd (nNamed id) (named_subst t x A) (named_subst t x B)
    | tProd na A B => tProd na (named_subst t x A) (named_subst t x B)
    | tLambda (nNamed id) T M =>
      if eq_string x id
      then tLambda (nNamed id) (named_subst t x T) M
      else tLambda (nNamed id) (named_subst t x T) (named_subst t x M)
    | tLambda na T M => tLambda na (named_subst t x T) (named_subst t x M)
    | tLetIn (nNamed id) b ty b' =>
      if eq_string x id
      then tLetIn (nNamed id) (named_subst t x b) (named_subst t x ty) b'
      else tLetIn (nNamed id) (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tLetIn na b ty b' => tLetIn na (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tApp u0 v => mkApps (named_subst t x u0) (map (named_subst t x) v)
    | tCase ind p c brs =>
        let brs' := map (on_snd (named_subst t x)) brs in
        tCase ind (named_subst t x p) (named_subst t x c) brs'
    | tProj p c => tProj p (named_subst t x c)
    | tFix mfix idx => (* FIXME *)
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tCoFix mfix' idx
    | _ => u
    end.

  (* Substitute multiple [global_term]s into a [named_term]. *)
  Fixpoint named_subst_all (l : list (ident * global_term)) (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End Substitution.

Notation "f >=> g" := (fun x => (f x) >>= g)
                      (at level 51, right associativity) : monad_scope.
Notation "f <$> x" := (x' <- x%monad ;; ret (f x'))
                      (at level 52, right associativity) : monad_scope.

Variables (graph : Type) (mtype : Type).

Inductive cRep : Set :=
| enum : forall (ordinal : N), cRep
| boxed : forall (ordinal : N) (arity : N), cRep.

Variable fitting_index : graph -> mtype -> cRep -> list mtype -> Prop.

Class Rep (A : Type) : Type :=
  { rep : forall (g : graph) (x : A) (p : mtype), Prop }.

(* Starting generation of [Rep] instances! *)

Section Argumentation.

  Record arg_info : Type :=
    { arg_name : BasicAst.ident
      (* the bound name used in the constructor, inside the pattern in the match *)
    ; p_name : BasicAst.ident
      (* the bound name used in the exists, for the [mtype] *)
    ; arg_type : named_term
      (* the fully applied type used as an argument *)
    ; arg_inductive : inductive
      (* the name of the type constructor used in the argument,
        like [nat], [list], [option] *)
    ; arg_one : one_inductive_body
      (* the single definition of the type used in the argument *)
    }.

  Variant arg_variant : Type :=
  | param_arg : forall (param_name : ident) (param_type : named_term), arg_variant
  | value_arg : forall (arg_name exists_name : ident) (arg_type : named_term), arg_variant.

  Definition argumentation
             (ind : inductive)
             (mut : mutual_inductive_body)
             (ctor : ctor_info) : TemplateMonad (list arg_variant * named_term) :=
    let number_of_params : nat := ind_npars mut in
    (* The type names are referred with de Bruijn indices
       so we must add them to the initial context. *)
    let mp : modpath := fst (inductive_mind ind) in
    let kn : kername := inductive_mind ind in
    (* We need two passes here,
       - one to replace the type references to globally unique [ident]s
       - another to substitute those [ident]s into terms referring to those types. *)
    let mut_names : list ident :=
        map (fun one => "$$$" ++ string_of_kername (mp, ind_name one)) (ind_bodies mut) in
    let mut_ind_terms : list (ident * global_term) :=
        mapi (fun i one =>
                let id := "$$$" ++ string_of_kername (mp, ind_name one) in
                let ind := mkInd kn i in
                (id, tInd ind nil))
            (ind_bodies mut) in

    let fix aux (params : nat)
                (arg_count : nat)
                (ctx : list ident)
                (t : term) {struct t}
                : TemplateMonad (list arg_variant * named_term) :=
      match params, t with
      (* Go through the params *)
      | S params', tProd n t b =>
        match n with
        | nNamed id =>
          let id := "$" ++ id in (* as our naming hack requires *)
          '(args, rest) <- aux params' arg_count (id :: ctx) b ;;
          t' <- DB.undeBruijn ctx t ;;
          let t' := Substitution.named_subst_all mut_ind_terms t' in
          ret (param_arg id t' :: args, rest)
        | _ => tmFail "Impossible: unnamed param"
        end
      | S _ , _ => tmFail "Impossible: all constructors quantify over params"

      (* Other arguments *)
      | O , tProd n t b =>
        let arg_name : ident := "$arg" ++ string_of_nat arg_count in
        let exists_name : ident := "$p" ++ string_of_nat arg_count in
        '(args, rest) <- aux O (S arg_count) (arg_name :: ctx) b ;;
        t' <- DB.undeBruijn ctx t ;;
        let t' := Substitution.named_subst_all mut_ind_terms t' in
        ret (value_arg arg_name exists_name t' :: args, rest)
      | O, t =>
        (* rename variables in the root *)
        t' <- DB.undeBruijn ctx t ;;
        let t' := Substitution.named_subst_all mut_ind_terms t' in
        ret (nil , t')
      end in

    aux number_of_params O mut_names (ctor_type ctor).

End Argumentation.

Definition is_sort : Type := bool.

Definition generate_instance_type
           (ind : inductive)
           (one : one_inductive_body)
           (type_quantifier : ident -> named_term -> named_term)
           (replacer : named_term -> named_term) : TemplateMonad term :=
  (* Convert the type of the type to explicitly named representation *)
  ty <- DB.undeBruijn [] (ind_type one) ;;
  let check_sort (t : any_term) : is_sort :=
      match t with tSort _ => true | _ => false end in
  (* Goes over a nested π-type and collects binder names,
     makes up a name where there isn't one.
     It also builds a function to replace the part after the π-binders. *)
  let fix collect
          (t : named_term) (count : nat) (replacer : named_term -> named_term)
          : list (ident * is_sort) * (named_term -> named_term) :=
    match t with
    | tProd nAnon ty rest =>
        let '(idents, f) := collect rest (S count) replacer in
        let new_name := "$arg" ++ string_of_nat count in
        ((new_name, check_sort ty) :: idents, (fun t' => tProd (nNamed new_name) ty (f t')))
    | tProd (nNamed id) ty rest =>
        let '(idents, f) := collect rest (S count) replacer in
        ((id, check_sort ty) :: idents, (fun t' => tProd (nNamed id) ty (f t')))
    | _ => (nil, replacer)
    end in
  let (quantified, new) := collect ty 0 replacer in
  let names := map fst quantified in
  let vars := map tVar names in
  let type_quantifiers := map fst (filter snd quantified) in
  let base := tApp (tInd ind []) vars in

  (* Fully apply the quantified type constructor.
     If you had [list] initially, now you have [forall (A : Type), list A] *)
  let result := new (fold_right type_quantifier base type_quantifiers) in
  (* Convert back to de Bruijn notation and return. *)
  DB.deBruijn result.

(* Checks if the given type class instance type has an instance.
   This wrapper function makes type checking easier
   since [tmInferInstance] is dependently typed but we don't need that now. *)
Definition has_instance (A : Type) : TemplateMonad bool :=
  opt_ins <- tmInferInstance (Some all) A ;;
  ret (match opt_ins with | my_Some _ => true | my_None => false end).

Definition generate_Rep_instance_type
           (ind : inductive)
           (one : one_inductive_body) : TemplateMonad named_term :=
  generate_instance_type ind one
    (fun ty_name t =>
      let n := "Rep_" ++ ty_name in
      tProd (nNamed n) (tApp <% Rep %> [tVar ty_name]) t)
    (fun t => tApp <% Rep %> [t]).

(* Constructs the instance type for the type at hand,
   checks if there's an instance for it. *)
Definition find_missing_instance
           (ind : inductive)
           (one : one_inductive_body) : TemplateMonad bool :=
  t <- generate_Rep_instance_type ind one ;;
  t' <- tmUnquoteTyped Type t ;;
  has_instance t'.

(* Take in a [global_env], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [Rep] instances. *)
Fixpoint find_missing_instances
        (env : global_env) : TemplateMonad (list kername) :=
    match env with
    | (kn, InductiveDecl mut) :: env' =>
      rest <- find_missing_instances env' ;;
      ones <- monad_map_i
                (fun i => find_missing_instance
                            {| inductive_mind := kn ; inductive_ind := i |})
                (ind_bodies mut) ;;
      if (fold_left andb ones true) (* if there are instances for all *)
        then ret rest (* then this one is not missing *)
        else ret (kn :: rest)
    | _ :: env' => find_missing_instances env'
    | nil => ret nil
    end.

Definition get_ty_info_from_inductive
           (ind : inductive) : TemplateMonad ty_info :=
  mut <- tmQuoteInductive (inductive_mind ind) ;;
  match nth_error (ind_bodies mut) (inductive_ind ind) with
  | None => tmFail "Wrong index for the mutual inductive block"
  | Some one =>
      params <- monad_map (fun c => match decl_name c with
                           | nAnon => tmFail "Unnamed inductive type parameter"
                           | nNamed n => ret n
                           end) (ind_params mut) ;;
      ret {| ty_name := inductive_mind ind
           ; ty_body := one
           ; ty_inductive := ind
           ; ty_params := params
           |}
  end.

(* Get the [ty_info] for the first type in the mutual block. *)
Definition get_ty_info
           (kn : kername) : TemplateMonad ty_info :=
  get_ty_info_from_inductive {| inductive_mind := kn ; inductive_ind := 0 |}.

Definition get_one_from_inductive
           (ind : inductive) : TemplateMonad one_inductive_body :=
  ty_body <$> get_ty_info_from_inductive ind.


Fixpoint handle_dissected_args
         (args : list dissected_type)
         (count : nat)
         : TemplateMonad (list arg_info) :=
    match args with
    | nil => ret nil
    | cons (dInd ind as spine) args' =>
      rest <- handle_dissected_args args' (S count) ;;
      let arg_s : BasicAst.ident := ("$arg" ++ string_of_nat count)%string in
      let ex_s : BasicAst.ident := ("$p" ++ string_of_nat count)%string in
      let t : term := tInd ind nil in
      one <- get_one_from_inductive ind ;;
      ret ({| arg_name := arg_s
            ; p_name := ex_s
            ; arg_type := spine
            ; arg_inductive := ind
            ; arg_one := one |} :: rest)
    | cons (dApp (dInd ind) diss as spine) args' =>
      (* tmFail "Dissected type is an application" ;; *)
      rest <- handle_dissected_args args' (S count) ;;
      let arg_s : BasicAst.ident := ("$arg" ++ string_of_nat count)%string in
      let ex_s : BasicAst.ident := ("$p" ++ string_of_nat count)%string in
      let t : term := tInd ind nil in
      one <- get_one_from_inductive ind ;;
      ret ({| arg_name := arg_s
            ; p_name := ex_s
            ; arg_type := spine
            ; arg_inductive := ind
            ; arg_one := one |} :: rest)
    | cons (dParam p) args' =>
      (* Parameters are not included when pattern matching on constructors *)
      handle_dissected_args args' count
    | cons decl _ =>
      (* tmPrint decl ;; *)
      tmFail ("Dissected type is not a type" ++ string_of_nat count)
    end.

Definition make_tInd (ind : inductive) : global_term :=
  tInd ind [].

Fixpoint make_lambdas
         (args : list arg_info)
         : named_term -> named_term :=
  match args with
  | nil => fun x => x
  | arg :: args' =>
    fun x => tLambda (nNamed (arg_name arg))
                     (make_tInd (arg_inductive arg))
                     (make_lambdas args' x)
  end.

Fixpoint make_exists
         (args : list arg_info)
         : named_term -> named_term :=
  match args with
  | nil => fun x => x
  | arg :: args' =>
    fun x => tApp <% ex %>
                  [ <% mtype %>
                  ; tLambda (nNamed (p_name arg))
                            <% mtype %>
                            (make_exists args' x) ]
  end.


(* Special helper functions to make lists consisting of [mtype] values *)
Definition t_cons (t : any_term) (t' : any_term) : any_term :=
  tApp <% @cons %> [<% mtype %> ; t ; t'].
Definition t_conses (xs : list any_term) : any_term :=
  fold_right t_cons <% @nil mtype %> xs.
Definition t_and (t : any_term) (t' : any_term) : any_term :=
  tApp <% @and %> [t ; t'].

(* [tmInferInstance] can create some type checking error
   but this definition solves it for some reason. *)
Definition tmInferInstanceEval (t : Type) := tmInferInstance (Some all) t.

(* Takes in a term representing a type like [forall A, Rep (list A)])

*)
Definition instance_term (inst_ty : term) : TemplateMonad global_term :=
  inst_ty' <- tmUnquoteTyped Type inst_ty ;;
  opt_ins <- tmInferInstanceEval inst_ty' ;;
  match opt_ins with
  | my_Some x => tmQuote x
  | _ => tmFail "No such instance"
  end.

Fixpoint make_prop
         (ind : inductive)
         (one : one_inductive_body)
         (ctor : ctor_info)
         (args : list arg_info)
         : TemplateMonad named_term :=
  let t_g := tVar "$g" in
  let t_p := tVar "$p" in

  let make_prop_base : TemplateMonad named_term :=
    (* Create the [cRep] for this constructor and evaluate *)
    crep <- tmEval all
              (match ctor_arity ctor with
                | O => enum (N.of_nat (ctor_ordinal ctor))
                | a => boxed (N.of_nat (ctor_ordinal ctor)) (N.of_nat a)
                end) ;;
    t_crep <- tmQuote crep ;;
    (* Create list of [[p0;p1;p2;...]] to pass to [fitting_index] *)
    let l := t_conses (map (fun n => tVar ("$p" ++ string_of_nat n))
                           (seq 0 (ctor_arity ctor))) in
    ret (tApp <% fitting_index %>
              [ t_g ; t_p ; t_crep ; l])
  in

  (* Takes in the order of the argument and the [arg_info],
     generates the call to [rep] for that argument *)
  let make_arg_prop (arg' : nat * arg_info) : TemplateMonad named_term :=
    let '(i, arg) := arg' in
    let t_arg := tVar ("$arg" ++ string_of_nat i) in
    let t_p := tVar ("$p" ++ string_of_nat i) in

    (* Check if this is a recursive call to the [rep] block we're defining *)
    if eq_kername (inductive_mind ind) (inductive_mind (arg_inductive arg))
    then
      let t_rep :=
        tVar ("$rep" ++ string_of_nat (inductive_ind (arg_inductive arg))) in
      ret (tApp t_rep [ t_g ; t_arg; t_p ])
    else
      (* not a recursive call, find the right [Rep] instance *)
      inst_ty <- generate_Rep_instance_type ind one ;;
      (* TODO fix this for special [Rep] instances *)
      t_ins <- instance_term inst_ty ;;
      ret (tApp <% @rep %> [ make_tInd (arg_inductive arg)
                           ; t_ins ; t_g ; t_arg; t_p ])
  in
  arg_props <- monad_map make_arg_prop (enumerate_nat args) ;;
  base <- make_prop_base ;;
  ret (fold_right t_and base arg_props).

(* Takes in the info for a single constructor of a type, generates the branches
   of a match expression for that constructor. *)
Definition ctor_to_branch
    (ind : inductive)
      (* the type we're generating for *)
    (one : one_inductive_body)
      (* the single type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctor : ctor_info)
      (* a single constructor to generate for *)
    : TemplateMonad (nat * named_term) :=
  let kn : kername := inductive_mind ind in
  mut <- tmQuoteInductive kn ;;
  let ctx : list dissected_type :=
      mapi (fun i _ => dInd {| inductive_mind := kn ; inductive_ind := i |})
           (ind_bodies mut) in
  params <- ty_params <$> get_ty_info (inductive_mind ind) ;;
  let '(dissected_args, dissected_res) :=
      dissect_types params ctx (ctor_type ctor) in
  (* tmPrint (dissected_args, dissected_res) ;; *)
  args <- handle_dissected_args dissected_args O ;;
  prop <- make_prop ind one ctor args ;;
  let t := make_lambdas args (make_exists args prop) in
  ret (ctor_arity ctor, t).

(* Generates a reified match expression *)
Definition matchmaker
    (ind : inductive)
      (* description of the type we're generating for *)
    (one : one_inductive_body)
      (* the single type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctors : list ctor_info)
      (* constructors we're generating match branches for *)
    : TemplateMonad named_term :=
  branches <- monad_map (ctor_to_branch ind one tau) ctors ;;
  ret (tCase (ind, 0)
             (tLambda (nNamed "$y"%string) tau <% Prop %>)
             (tVar "$x")
             branches).


(* Make a single record to use in a [tFix].
   For mutually inductive types, we want to build them all once,
   and define all the [Rep] instances with that. *)
Definition make_fix_single
           (tau : term) (* fully applied type constructor *)
           (ind : inductive)
           (one : one_inductive_body) : TemplateMonad (BasicAst.def named_term) :=
  let this_name := nNamed ("$rep" ++ string_of_nat (inductive_ind ind)) in
  prop <- matchmaker ind one tau (process_ctors (ind_ctors one)) ;;
  let body :=
      (tLambda (nNamed "$g"%string) <% graph %>
        (tLambda (nNamed "$x"%string) tau
          (tLambda (nNamed "$p"%string) <% mtype %> prop))) in
  ret {| dname := this_name
       ; dtype := tProd (nNamed "$g"%string)
                       <% graph %>
                       (tProd (nNamed "$x"%string)
                               tau
                               (tProd (nNamed "$p"%string)
                                     <% mtype %>
                                     <% Prop %>))
       ; dbody := body
       ; rarg := 1 |}.

(* Remove all the initial consecutive π-type quantifiers from a [term]. *)
Fixpoint strip_quantifiers (t : named_term) : named_term :=
  match t with
  | tProd _ _ rest => strip_quantifiers rest
  | x => x
  end.

(* Get binder names and binding types for all
   initial consecutive π-type quantifiers in an [any_term]. *)
Fixpoint get_quantifiers (t : any_term) : list (name * any_term) :=
  match t with
  | tProd n ty rest => (n, ty) :: get_quantifiers rest
  | x => nil
  end.

(* Given binder names and binding types, add binders to the base [named_term].
   Can be used to add λs (with [tLambda]) or πs (with [tProd]). *)
Fixpoint build_quantifiers
         (binder : name -> named_term -> named_term -> named_term)
         (l : list (name * named_term))
         (base : named_term) : named_term :=
  match l with
  | nil => base
  | (n, t) :: rest => binder n t (build_quantifiers binder rest base)
  end.

Definition add_instances (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  (* Build the single function definitions for each of
     the mutually recursive types. *)
  singles <- monad_map_i
               (fun i one =>
                  (* FIXME get rid of repeated computation here *)
                  let ind := {| inductive_mind := kn ; inductive_ind := i |} in
                  quantified <- generate_instance_type ind one (fun _ => id) id ;;
                  quantified_named <- DB.undeBruijn [] quantified ;;
                  let tau := strip_quantifiers quantified_named in
                  make_fix_single tau {| inductive_mind := kn ; inductive_ind := i |} one)
               (ind_bodies mut) ;;

  (* Loop over each mutually recursive type again *)
  monad_map_i
    (fun i one =>
       let ind := {| inductive_mind := kn ; inductive_ind := i |} in
       (* This gives us something like
          [forall (A : Type) (n : nat), vec A n] *)
       quantified <- generate_instance_type ind one (fun _ => id) id ;;
       (* Now what can we do with this?
          Let's start by going to its named representation. *)
       quantified_named <- DB.undeBruijn [] quantified ;;

       (* The reified type of the fully applied type constructor,
          but with free variables! *)
       let tau := strip_quantifiers quantified_named in
       let fn_ty := tProd (nNamed "$g"%string)
                          <% graph %>
                          (tProd (nNamed "$x"%string)
                                 tau
                                 (tProd (nNamed "$p"%string)
                                        <% mtype %>
                                        <% Prop %>)) in
       let quantifiers := get_quantifiers quantified_named in
       let prog_named : named_term :=
           build_quantifiers tLambda quantifiers
                             (tApp <% @Build_Rep %>
                                   [tau; tFix singles i]) in
       (* tmEval all prog_named >>= tmPrint ;; *)

       (* Convert generated program from named to de Bruijn representation *)
       prog <- DB.deBruijn prog_named ;;

       (* If need be, here's the reified type of our [Rep] instance: *)
       instance_ty <-
            tmUnquoteTyped Type
              (build_quantifiers tProd quantifiers
                                (tApp <% Rep %> [quantified])) ;;

       instance <- tmUnquote prog ;;
       (* Remove [tmEval] when MetaCoq issue 455 is fixed: *)
       (* https://github.com/MetaCoq/metacoq/issues/455 *)
       name <- tmFreshName =<< tmEval all ("Rep_" ++ ind_name one)%string ;;

       (* This is sort of a hack. I couldn't use [tmUnquoteTyped] above
          because of a mysterious type error. (Coq's type errors in monadic
          contexts are just wild.) Therefore I had to [tmUnquote] it to get
          a Σ-type. But when you project the second field out of that,
          the type doesn't get evaluated to [Rep _], it stays as
          [my_projT2 {| ... |}]. The same thing goes for the first projection,
          which is the type of the second projection. When the user prints
          their [Rep] instance, Coq shows the unevaluated version.
          But we don't want to evaluate it [all] the way, that would unfold
          the references to other instances of [Rep]. We only want to get
          the head normal form with [hnf].
          We have to do this both for the instance body and its type. *)
       tmEval hnf (my_projT2 instance) >>=
         tmDefinitionRed_ false name (Some hnf) ;;

       (* Declare the new definition a type class instance *)
       mp <- tmCurrentModPath tt ;;
       tmExistingInstance (ConstRef (mp, name)) ;;

       let fake_kn := (fst kn, ind_name one) in
       tmMsg ("Added Rep instance for " ++ string_of_kername fake_kn) ;;
       ret tt) (ind_bodies mut) ;;
  ret tt.

(* Derives a [Rep] instance for the type constructor [Tau] *)
(*    and the types its definition depends on. *)
Definition rep_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  missing <- find_missing_instances env ;;
  monad_iter add_instances (rev missing).



(* Playground: *)


(* Instance Rep_nat : Rep nat := *)
(*   {| rep _ _ _ := False |}. *)
(* Instance Rep_list {A} `{Rep A} : Rep (list A) := *)
(*   {| rep _ _ _ := False |}. *)

(* Check <% forall A `{Rep A}, Rep (list A)%>. *)
(* Check <% forall A, Rep A -> Rep (list A)%>. *)
(* MetaCoq Run (o <- tmInferInstance (Some all) (forall A, Rep A -> Rep (list A)) ;; *)
(*              tmPrint o). *)




Check <%% le %%>.
(* Let's see it in action: *)
MetaCoq Run (rep_gen unit).
Print Rep_unit.
(* fitting_index g p (enum 0) [] *)

(* MetaCoq Run (rep_gen bool). *)
(* Print Rep_bool. *)

Print name.
Check <%% list %%>.

Inductive T (n : nat) (eq : n = 0) : nat -> Type :=
| C : T n eq (n + n).

Instance Rep_T n eq n' : Rep (T n eq n') :=
  {| rep g x p :=
       match x with
       | C => False
       end
  |}.

Check <%% T %%>.
Check (fun (t : T 0 (eq_refl 0) 0) => match t with C => true end).

Fixpoint rep0 (g : graph) (x : nat) (p : mtype) {struct x} : Prop :=
  match x with
  | 0 => fitting_index g p (enum 0) []
  | S arg0 =>
      exists p0 : mtype, rep0 g arg0 p0 /\ fitting_index g p (boxed 0 1) [p0]
  end.
(* Instance Rep_nat : Rep nat := @Build_Rep nat rep0. *)

MetaCoq Run (rep_gen nat).
Print Rep_nat.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A O
| vcons : forall n, A -> vec A n -> vec A (S n).

Instance Rep_vec (A : Type) (Rep_A : Rep A) (n : nat) : Rep (vec A n) :=
  let fix rep_vec (n : nat) (g : graph) (x : vec A n) (p : mtype) {struct x} : Prop :=
    match x with
    | vnil => fitting_index g p (enum 0) []
    | vcons arg0 arg1 arg2 =>
        exists p0 p1 p2 : mtype,
          @rep nat Rep_nat g arg0 p0 /\
          @rep A Rep_A g arg1 p1 /\
          rep_vec arg0 g arg2 p2 /\
          fitting_index g p (boxed 0 3) [p0; p1; p2]
    end
  in @Build_Rep (vec A n) (rep_vec n).

Inductive fin : nat -> Set :=
| F1 : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).

Inductive fin' : Set :=
| F1' : forall {n : nat}, fin'
| FS' : forall {n : nat}, fin' -> fin'.
Check <%% fin %%>.

(* Inductive T (x : unit) : Type := *)
(* | C : T x. *)
(* Check <%% T %%>. *)
MetaCoq Run (rep_gen fin').
(* Print Rep_fin'. *)

Instance Rep_fin (n : nat) : Rep (fin n) :=
  let fix rep_fin (n : nat) (g : graph) (x : fin n) (p : mtype) {struct x} : Prop :=
    match x with
    | @F1 arg0 =>
        exists p0 : mtype, rep g arg0 p0 /\ fitting_index g p (boxed 0 1) [p0]
    | @FS arg0 arg1 =>
        exists p0 p1 : mtype,
          rep g arg0 p0 /\
          rep_fin arg0 g arg1 p1 /\ fitting_index g p (boxed 1 2) [p0; p1]
    end in @Build_Rep (fin n) (rep_fin n).

MetaCoq Run (rep_gen fin).
(* Print Rep_fin. *)

MetaCoq Run (rep_gen list).
(* Print Rep_list. *)

Inductive rgx : Type :=
| empty   : rgx
| epsilon : rgx
| literal : string -> rgx
| or      : rgx -> rgx -> rgx
| and     : rgx -> rgx -> rgx
| star    : rgx -> rgx.

(* MetaCoq Run (rep_gen rgx). *)
(* Print Rep_rgx. *)

Inductive R1 :=
| r1 : R1
with R2 :=
| r2 : R2.

(* MetaCoq Run (rep_gen R1). *)
(* Print Rep_R1. *)

Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.

MetaCoq Run (rep_gen T1).
(* Print Rep_T1. *)

Inductive param_and_index (a b : nat) : a < b -> Type :=
| foo : forall (pf : a < b), param_and_index a b pf.

(* MetaCoq Run (rep_gen param_and_index). *)
(* Print Rep_param_and_index. *)

Inductive indexed : nat -> Type :=
| bar : indexed O.

(* MetaCoq Run (rep_gen indexed). *)
(* Print Rep_indexed. *)
