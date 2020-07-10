type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q -> XI (add p q)
               | XO q -> XO (add p q)
               | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p -> (match y with
               | XI q -> XI (add_carry p q)
               | XO q -> XO (add_carry p q)
               | XH -> XI (succ p))
    | XO p -> (match y with
               | XI q -> XO (add_carry p q)
               | XO q -> XI (add p q)
               | XH -> XO (succ p))
    | XH -> (match y with
             | XI q -> XI (succ q)
             | XO q -> XO (succ q)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred : positive -> positive **)

  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module Coq__1 = struct
 (** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)
 let rec map f = function
 | Nil -> Nil
 | Cons (a, t0) -> Cons ((f a), (map f t0))
end
include Coq__1

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

(** val peq : positive -> positive -> sumbool **)

let peq =
  Pos.eq_dec

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some y -> Some (f y)
| None -> None

module PTree =
 struct
  type elt = positive

  (** val elt_eq : positive -> positive -> sumbool **)

  let elt_eq =
    peq

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val get : positive -> 'a1 t -> 'a1 option **)

  let rec get i = function
  | Leaf -> None
  | Node (l, o, r) -> (match i with
                       | XI ii -> get ii r
                       | XO ii -> get ii l
                       | XH -> o)

  (** val set : positive -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec set i v = function
  | Leaf ->
    (match i with
     | XI ii -> Node (Leaf, None, (set ii v Leaf))
     | XO ii -> Node ((set ii v Leaf), None, Leaf)
     | XH -> Node (Leaf, (Some v), Leaf))
  | Node (l, o, r) ->
    (match i with
     | XI ii -> Node (l, o, (set ii v r))
     | XO ii -> Node ((set ii v l), o, r)
     | XH -> Node (l, (Some v), r))

  (** val remove : positive -> 'a1 t -> 'a1 t **)

  let rec remove i m =
    match i with
    | XI ii ->
      (match m with
       | Leaf -> Leaf
       | Node (l, o, r) ->
         (match l with
          | Leaf ->
            (match o with
             | Some _ -> Node (l, o, (remove ii r))
             | None ->
               (match remove ii r with
                | Leaf -> Leaf
                | Node (t0, o0, t1) -> Node (Leaf, None, (Node (t0, o0, t1)))))
          | Node (_, _, _) -> Node (l, o, (remove ii r))))
    | XO ii ->
      (match m with
       | Leaf -> Leaf
       | Node (l, o, r) ->
         (match o with
          | Some _ -> Node ((remove ii l), o, r)
          | None ->
            (match r with
             | Leaf ->
               (match remove ii l with
                | Leaf -> Leaf
                | Node (t0, o0, t1) -> Node ((Node (t0, o0, t1)), None, Leaf))
             | Node (_, _, _) -> Node ((remove ii l), o, r))))
    | XH ->
      (match m with
       | Leaf -> Leaf
       | Node (l, _, r) ->
         (match l with
          | Leaf -> (match r with
                     | Leaf -> Leaf
                     | Node (_, _, _) -> Node (l, None, r))
          | Node (_, _, _) -> Node (l, None, r)))

  (** val bempty : 'a1 t -> bool **)

  let rec bempty = function
  | Leaf -> True
  | Node (l, o, r) ->
    (match o with
     | Some _ -> False
     | None -> (match bempty l with
                | True -> bempty r
                | False -> False))

  (** val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec beq beqA m1 m2 =
    match m1 with
    | Leaf -> bempty m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> bempty m1
       | Node (l2, o2, r2) ->
         (match match match o1 with
                      | Some y1 -> (match o2 with
                                    | Some y2 -> beqA y1 y2
                                    | None -> False)
                      | None -> (match o2 with
                                 | Some _ -> False
                                 | None -> True) with
                | True -> beq beqA l1 l2
                | False -> False with
          | True -> beq beqA r1 r2
          | False -> False))

  (** val prev_append : positive -> positive -> positive **)

  let rec prev_append i j =
    match i with
    | XI i' -> prev_append i' (XI j)
    | XO i' -> prev_append i' (XO j)
    | XH -> j

  (** val prev : positive -> positive **)

  let prev i =
    prev_append i XH

  (** val xmap : (positive -> 'a1 -> 'a2) -> 'a1 t -> positive -> 'a2 t **)

  let rec xmap f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmap f l (XO i)), (match o with
                                | Some x -> Some (f (prev i) x)
                                | None -> None), (xmap f r (XI i)))

  (** val map : (positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    xmap f m XH

  (** val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map1 f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> Node ((map1 f l), (option_map f o), (map1 f r))

  (** val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t **)

  let coq_Node' l x r =
    match l with
    | Leaf ->
      (match x with
       | Some _ -> Node (l, x, r)
       | None -> (match r with
                  | Leaf -> Leaf
                  | Node (_, _, _) -> Node (l, x, r)))
    | Node (_, _, _) -> Node (l, x, r)

  (** val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t **)

  let rec filter1 pred0 = function
  | Leaf -> Leaf
  | Node (l, o, r) ->
    coq_Node' (filter1 pred0 l)
      (match o with
       | Some x -> (match pred0 x with
                    | True -> o
                    | False -> None)
       | None -> None) (filter1 pred0 r)

  (** val xcombine_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec xcombine_l f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_l f l) (f o None) (xcombine_l f r)

  (** val xcombine_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec xcombine_r f = function
  | Leaf -> Leaf
  | Node (l, o, r) -> coq_Node' (xcombine_r f l) (f None o) (xcombine_r f r)

  (** val combine : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec combine f m1 m2 =
    match m1 with
    | Leaf -> xcombine_r f m2
    | Node (l1, o1, r1) ->
      (match m2 with
       | Leaf -> xcombine_l f m1
       | Node (l2, o2, r2) -> coq_Node' (combine f l1 l2) (f o1 o2) (combine f r1 r2))

  (** val xelements : 'a1 t -> positive -> (positive, 'a1) prod list -> (positive, 'a1) prod list **)

  let rec xelements m i k =
    match m with
    | Leaf -> k
    | Node (l, o, r) ->
      (match o with
       | Some x -> xelements l (XO i) (Cons ((Pair ((prev i), x)), (xelements r (XI i) k)))
       | None -> xelements l (XO i) (xelements r (XI i) k))

  (** val elements : 'a1 t -> (positive, 'a1) prod list **)

  let elements m =
    xelements m XH Nil

  (** val xkeys : 'a1 t -> positive -> positive list **)

  let xkeys m i =
    Coq__1.map fst (xelements m i Nil)

  (** val xfold : ('a2 -> positive -> 'a1 -> 'a2) -> positive -> 'a1 t -> 'a2 -> 'a2 **)

  let rec xfold f i m v =
    match m with
    | Leaf -> v
    | Node (l, o, r) ->
      (match o with
       | Some x -> xfold f (XI i) r (f (xfold f (XO i) l v) (prev i) x)
       | None -> xfold f (XI i) r (xfold f (XO i) l v))

  (** val fold : ('a2 -> positive -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m v =
    xfold f XH m v

  (** val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold1 f m v =
    match m with
    | Leaf -> v
    | Node (l, o, r) -> (match o with
                         | Some x -> fold1 f r (f (fold1 f l v) x)
                         | None -> fold1 f r (fold1 f l v))
 end

module M = PTree

(** val set_lists : M.elt list -> 'a1 list -> 'a1 M.t -> 'a1 M.t option **)

let rec set_lists xs vs rho =
  match xs with
  | Nil -> (match vs with
            | Nil -> Some rho
            | Cons (_, _) -> None)
  | Cons (x, xs') ->
    (match vs with
     | Nil -> None
     | Cons (v, vs') -> (match set_lists xs' vs' rho with
                         | Some rho' -> Some (M.set x v rho')
                         | None -> None))

type ident = string

type name =
| NAnon
| NNamed of ident

module Coq_M = PTree

type 'x pM = 'x PTree.tree

type var = Coq_M.elt

type fun_tag = Coq_M.elt

type ind_tag = Coq_M.elt

type ctor_tag = Coq_M.elt

type ctor_ty_info = { ctor_name : name; ctor_ind_name : name; ctor_ind_tag : ind_tag; ctor_arity : n;
                      ctor_ordinal : n }

type ctor_env = ctor_ty_info pM

type fun_ty_info = (n, n list) prod

type fun_env = fun_ty_info pM

type name_env = name pM

type comp_data = { next_var : var; nect_ctor_tag : ctor_tag; next_ind_tag : ind_tag; next_fun_tag : fun_tag;
                   cenv : ctor_env; fenv : fun_env; nenv : name_env; log : string list }

(** val apply_r : Coq_M.elt Coq_M.t -> positive -> Coq_M.elt **)

let apply_r sigma y =
  match Coq_M.get y sigma with
  | Some v -> v
  | None -> y

(** val apply_r_list : Coq_M.elt Coq_M.t -> positive list -> Coq_M.elt list **)

let apply_r_list sigma ys =
  map (apply_r sigma) ys

type 'u univD = __

type 'u frame_t = __

type ('u, 'f) frames_t' =
| Frames_nil of 'u
| Frames_cons of 'u * 'u * 'u * 'f * ('u, 'f) frames_t'

type 'u frames_t = ('u, 'u frame_t) frames_t'

type ('u, 'p) preserves_S = { preserve_S_up : ('u -> 'u -> 'u frames_t -> 'u frame_t -> 'u univD -> 'p -> 'p);
                              preserve_S_dn : ('u -> 'u -> 'u frames_t -> 'u frame_t -> 'u univD -> 'p -> 'p) }

type 'u trivial_R_C = unit0

type 'u trivial_delay_t = unit0

type ('u, 's) s_plain = 's

type ('u, 's1, 's2) s_prod = ('s1, 's2) prod

type ('u, 'st) result = { resTree : 'u univD; resState : 'st }

type ('u, 'r_C, 'st) rw_for = 'r_C -> 'st -> ('u, 'st) result

type fuel = positive

type ('u, 'd, 'r_C, 'st) rewriter = fuel -> 'u -> 'u frames_t -> 'u univD -> 'd -> ('u, 'r_C, 'st) rw_for

type var0 = positive
  (* singleton inductive, whose constructor was mk_var *)

type fun_tag0 = positive
  (* singleton inductive, whose constructor was mk_fun_tag *)

type ctor_tag0 = positive
  (* singleton inductive, whose constructor was mk_ctor_tag *)

type prim = positive
  (* singleton inductive, whose constructor was mk_prim *)

(** val un_var : var0 -> positive **)

let un_var pat =
  pat

type exp =
| Econstr of var0 * ctor_tag0 * var0 list * exp
| Ecase of var0 * (ctor_tag0, exp) prod list
| Eproj of var0 * ctor_tag0 * n * var0 * exp
| Eletapp of var0 * var0 * fun_tag0 * var0 list * exp
| Efun of fundef list * exp
| Eapp of var0 * fun_tag0 * var0 list
| Eprim of var0 * prim * var0 list * exp
| Ehalt of var0
and fundef =
| Ffun of var0 * fun_tag0 * var0 list * exp

type exp_univ =
| Exp_univ_prod_ctor_tag_exp
| Exp_univ_list_prod_ctor_tag_exp
| Exp_univ_fundef
| Exp_univ_list_fundef
| Exp_univ_exp
| Exp_univ_var
| Exp_univ_fun_tag
| Exp_univ_ctor_tag
| Exp_univ_prim
| Exp_univ_N
| Exp_univ_list_var

type exp_frame_t =
| Pair_ctor_tag_exp0 of exp
| Pair_ctor_tag_exp1 of ctor_tag0
| Cons_prod_ctor_tag_exp0 of (ctor_tag0, exp) prod list
| Cons_prod_ctor_tag_exp1 of (ctor_tag0, exp) prod
| Ffun0 of fun_tag0 * var0 list * exp
| Ffun1 of var0 * var0 list * exp
| Ffun2 of var0 * fun_tag0 * exp
| Ffun3 of var0 * fun_tag0 * var0 list
| Cons_fundef0 of fundef list
| Cons_fundef1 of fundef
| Econstr0 of ctor_tag0 * var0 list * exp
| Econstr1 of var0 * var0 list * exp
| Econstr2 of var0 * ctor_tag0 * exp
| Econstr3 of var0 * ctor_tag0 * var0 list
| Ecase0 of (ctor_tag0, exp) prod list
| Ecase1 of var0
| Eproj0 of ctor_tag0 * n * var0 * exp
| Eproj1 of var0 * n * var0 * exp
| Eproj2 of var0 * ctor_tag0 * var0 * exp
| Eproj3 of var0 * ctor_tag0 * n * exp
| Eproj4 of var0 * ctor_tag0 * n * var0
| Eletapp0 of var0 * fun_tag0 * var0 list * exp
| Eletapp1 of var0 * fun_tag0 * var0 list * exp
| Eletapp2 of var0 * var0 * var0 list * exp
| Eletapp3 of var0 * var0 * fun_tag0 * exp
| Eletapp4 of var0 * var0 * fun_tag0 * var0 list
| Efun0 of exp
| Efun1 of fundef list
| Eapp0 of fun_tag0 * var0 list
| Eapp1 of var0 * var0 list
| Eapp2 of var0 * fun_tag0
| Eprim0 of prim * var0 list * exp
| Eprim1 of var0 * var0 list * exp
| Eprim2 of var0 * prim * exp
| Eprim3 of var0 * prim * var0 list
| Ehalt0

module Coq0_M = Coq_M

(** val strip_vars : var0 list -> var list **)

let strip_vars =
  map (fun pat -> pat)

type fundefs = fundef list

type ('a, 'b) iso = { isoAofB : ('b -> 'a); isoBofA : ('a -> 'b) }

(** val iso_var : (var0, var) iso **)

let iso_var =
  { isoAofB = (fun x -> x); isoBofA = un_var }

(** val iso_vars : (var0 list, var list) iso **)

let iso_vars =
  { isoAofB = (map (fun x -> x)); isoBofA = strip_vars }

type 'a inhabited = 'a

(** val inhabitant : 'a1 inhabited -> 'a1 **)

let inhabitant inhabited0 =
  inhabited0

(** val inhabited_pos : positive inhabited **)

let inhabited_pos =
  XH

(** val inhabited_var : var0 inhabited **)

let inhabited_var =
  inhabitant inhabited_pos

(** val inhabited_fun_tag : fun_tag0 inhabited **)

let inhabited_fun_tag =
  inhabitant inhabited_pos

(** val inhabited_list : 'a1 list inhabited **)

let inhabited_list =
  Nil

(** val inhabited_exp : exp inhabited **)

let inhabited_exp =
  Ehalt (inhabitant inhabited_var)

(** val inhabited_fundef : fundef inhabited **)

let inhabited_fundef =
  Ffun ((inhabitant inhabited_var), (inhabitant inhabited_fun_tag), (inhabitant inhabited_list),
    (inhabitant inhabited_exp))

(** val gensym : var -> (var, var0) prod **)

let gensym x =
  Pair ((Pos.add x XH), (iso_var.isoAofB x))

(** val gensyms : var -> 'a1 list -> (var, var0 list) prod **)

let rec gensyms x = function
| Nil -> Pair (x, Nil)
| Cons (_, xs0) -> let Pair (x', xs') = gensyms (Pos.add x XH) xs0 in Pair (x', (Cons (x, xs')))

type s_fresh = var

type s_uniq = __

type r_map = var M.tree

(** val fun_name : fundef -> var0 **)

let fun_name = function
| Ffun (f, _, _, _) -> f

(** val apply_r' : r_map -> var0 -> var0 **)

let apply_r' _UU03c3_ x =
  iso_var.isoAofB (apply_r _UU03c3_ (iso_var.isoBofA x))

(** val apply_r_list' : r_map -> var0 list -> var0 list **)

let apply_r_list' _UU03c3_ xs =
  map (apply_r' _UU03c3_) xs

(** val rename_all' : r_map -> exp -> exp **)

let rec rename_all' _UU03c3_ = function
| Econstr (x, t0, ys, e') -> Econstr (x, t0, (apply_r_list' _UU03c3_ ys), (rename_all' _UU03c3_ e'))
| Ecase (v, cl) ->
  Ecase ((apply_r' _UU03c3_ v), (map (fun p -> let Pair (k, e0) = p in Pair (k, (rename_all' _UU03c3_ e0))) cl))
| Eproj (v, t0, n0, y, e') -> Eproj (v, t0, n0, (apply_r' _UU03c3_ y), (rename_all' _UU03c3_ e'))
| Eletapp (x, f, ft, ys, e') ->
  Eletapp (x, (apply_r' _UU03c3_ f), ft, (apply_r_list' _UU03c3_ ys), (rename_all' _UU03c3_ e'))
| Efun (fl, e') ->
  Efun ((map (fun fd -> let Ffun (v', t0, ys, e0) = fd in Ffun (v', t0, ys, (rename_all' _UU03c3_ e0))) fl),
    (rename_all' _UU03c3_ e'))
| Eapp (f, t0, ys) -> Eapp ((apply_r' _UU03c3_ f), t0, (apply_r_list' _UU03c3_ ys))
| Eprim (x, f, ys, e') -> Eprim (x, f, (apply_r_list' _UU03c3_ ys), (rename_all' _UU03c3_ e'))
| Ehalt v -> Ehalt (apply_r' _UU03c3_ v)

type fun_map = ((fun_tag0, var0 list) prod, exp) prod M.tree

(** val add_fundefs : fundefs -> fun_map -> fun_map **)

let rec add_fundefs fds _UU03c1_ =
  match fds with
  | Nil -> _UU03c1_
  | Cons (f0, fds0) ->
    let Ffun (f, ft, xs, e) = f0 in M.set (iso_var.isoBofA f) (Pair ((Pair (ft, xs)), e)) (add_fundefs fds0 _UU03c1_)

type inlineHeuristic = __inlineHeuristic Lazy.t
and __inlineHeuristic =
| Build_InlineHeuristic of (fundefs -> exp -> inlineHeuristic) * (fundefs -> exp -> inlineHeuristic)
   * (var0 -> fun_tag0 -> var0 list -> exp -> inlineHeuristic) * (var0 -> fun_tag0 -> var0 list -> bool)
   * (var0 -> fun_tag0 -> var0 list -> inlineHeuristic) * (var0 -> fun_tag0 -> var0 list -> bool)
   * (var0 -> fun_tag0 -> var0 list -> inlineHeuristic)

(** val update_funDef1 : inlineHeuristic -> fundefs -> exp -> inlineHeuristic **)

let update_funDef1 i =
  let Build_InlineHeuristic (update_funDef3, _, _, _, _, _, _) = Lazy.force i in update_funDef3

(** val update_funDef2 : inlineHeuristic -> fundefs -> exp -> inlineHeuristic **)

let update_funDef2 i =
  let Build_InlineHeuristic (_, update_funDef3, _, _, _, _, _) = Lazy.force i in update_funDef3

(** val update_inFun : inlineHeuristic -> var0 -> fun_tag0 -> var0 list -> exp -> inlineHeuristic **)

let update_inFun i =
  let Build_InlineHeuristic (_, _, update_inFun0, _, _, _, _) = Lazy.force i in update_inFun0

(** val decide_App : inlineHeuristic -> var0 -> fun_tag0 -> var0 list -> bool **)

let decide_App i =
  let Build_InlineHeuristic (_, _, _, decide_App0, _, _, _) = Lazy.force i in decide_App0

(** val update_App : inlineHeuristic -> var0 -> fun_tag0 -> var0 list -> inlineHeuristic **)

let update_App i =
  let Build_InlineHeuristic (_, _, _, _, update_App0, _, _) = Lazy.force i in update_App0

(** val freshen_fd' :
    (positive -> r_map -> exp -> (positive, exp) prod) -> positive -> r_map -> fundef -> (positive, fundef) prod **)

let freshen_fd' freshen_exp0 next _UU03c3_ = function
| Ffun (f, ft, xs, e) ->
  let Pair (next0, xs') = gensyms next xs in
  (match set_lists (iso_vars.isoBofA xs) (iso_vars.isoBofA xs') _UU03c3_ with
   | Some _UU03c3_0 ->
     let Pair (next1, e0) = freshen_exp0 next0 _UU03c3_0 e in
     Pair (next1, (Ffun ((iso_var.isoAofB (apply_r _UU03c3_ (iso_var.isoBofA f))), ft, xs', e0)))
   | None -> Pair (next0, (inhabitant inhabited_fundef)))

(** val freshen_fds' :
    (positive -> r_map -> exp -> (positive, exp) prod) -> positive -> r_map -> fundef list -> (positive, fundef
    list) prod **)

let rec freshen_fds' freshen_exp0 next _UU03c3_ = function
| Nil -> Pair (next, Nil)
| Cons (fd, fds0) ->
  let Pair (next0, fd0) = freshen_fd' freshen_exp0 next _UU03c3_ fd in
  let Pair (next1, fds1) = freshen_fds' freshen_exp0 next0 _UU03c3_ fds0 in Pair (next1, (Cons (fd0, fds1)))

(** val freshen_ce' :
    (positive -> r_map -> exp -> (positive, exp) prod) -> positive -> r_map -> (ctor_tag0, exp) prod -> (positive,
    (ctor_tag0, exp) prod) prod **)

let freshen_ce' freshen_exp0 next _UU03c3_ = function
| Pair (c, e) -> let Pair (next0, e0) = freshen_exp0 next _UU03c3_ e in Pair (next0, (Pair (c, e0)))

(** val freshen_ces' :
    (positive -> r_map -> exp -> (positive, exp) prod) -> positive -> r_map -> (ctor_tag0, exp) prod list ->
    (positive, (ctor_tag0, exp) prod list) prod **)

let rec freshen_ces' freshen_exp0 next _UU03c3_ = function
| Nil -> Pair (next, Nil)
| Cons (ce, ces0) ->
  let Pair (next0, ce0) = freshen_ce' freshen_exp0 next _UU03c3_ ce in
  let Pair (next1, ces1) = freshen_ces' freshen_exp0 next0 _UU03c3_ ces0 in Pair (next1, (Cons (ce0, ces1)))

(** val freshen_exp : positive -> r_map -> exp -> (positive, exp) prod **)

let rec freshen_exp next _UU03c3_ = function
| Econstr (x, c, ys, e0) ->
  let Pair (next0, x') = gensym next in
  let Pair (next1, e1) = freshen_exp next0 (Coq0_M.set (iso_var.isoBofA x) (iso_var.isoBofA x') _UU03c3_) e0 in
  Pair (next1, (Econstr (x', c, (iso_vars.isoAofB (apply_r_list _UU03c3_ (iso_vars.isoBofA ys))), e1)))
| Ecase (x, ces) ->
  let Pair (next0, ces0) = freshen_ces' freshen_exp next _UU03c3_ ces in
  Pair (next0, (Ecase ((iso_var.isoAofB (apply_r _UU03c3_ (iso_var.isoBofA x))), ces0)))
| Eproj (x, c, n0, y, e0) ->
  let Pair (next0, x') = gensym next in
  let Pair (next1, e1) = freshen_exp next0 (Coq0_M.set (iso_var.isoBofA x) (iso_var.isoBofA x') _UU03c3_) e0 in
  Pair (next1, (Eproj (x', c, n0, (iso_var.isoAofB (apply_r _UU03c3_ (iso_var.isoBofA y))), e1)))
| Eletapp (x, f, ft, ys, e0) ->
  let Pair (next0, x') = gensym next in
  let Pair (next1, e1) = freshen_exp next0 (Coq0_M.set (iso_var.isoBofA x) (iso_var.isoBofA x') _UU03c3_) e0 in
  Pair (next1, (Eletapp (x', (iso_var.isoAofB (apply_r _UU03c3_ (iso_var.isoBofA f))), ft,
  (iso_vars.isoAofB (apply_r_list _UU03c3_ (iso_vars.isoBofA ys))), e1)))
| Efun (fds, e0) ->
  let fs = map fun_name fds in
  let Pair (next0, fs') = gensyms next fs in
  (match set_lists (iso_vars.isoBofA fs) (iso_vars.isoBofA fs') _UU03c3_ with
   | Some _UU03c3_0 ->
     let Pair (next1, fds0) = freshen_fds' freshen_exp next0 _UU03c3_0 fds in
     let Pair (next2, e1) = freshen_exp next1 _UU03c3_0 e0 in Pair (next2, (Efun (fds0, e1)))
   | None -> Pair (next0, (Efun (Nil, e0))))
| Eapp (f, ft, xs) ->
  Pair (next, (Eapp ((iso_var.isoAofB (apply_r _UU03c3_ (iso_var.isoBofA f))), ft,
    (iso_vars.isoAofB (apply_r_list _UU03c3_ (iso_vars.isoBofA xs))))))
| Eprim (x, p, ys, e0) ->
  let Pair (next0, x') = gensym next in
  let Pair (next1, e1) = freshen_exp next0 (Coq0_M.set (iso_var.isoBofA x) (iso_var.isoBofA x') _UU03c3_) e0 in
  Pair (next1, (Eprim (x', p, (iso_vars.isoAofB (apply_r_list _UU03c3_ (iso_vars.isoBofA ys))), e1)))
| Ehalt x -> Pair (next, (Ehalt (iso_var.isoAofB (apply_r _UU03c3_ (iso_var.isoBofA x)))))

(** val update_next_var : var -> comp_data -> comp_data **)

let update_next_var next cdata =
  let { next_var = _; nect_ctor_tag = c; next_ind_tag = i; next_fun_tag = f; cenv = e; fenv = fenv0; nenv = names;
    log = log0 } = cdata
  in
  { next_var = next; nect_ctor_tag = c; next_ind_tag = i; next_fun_tag = f; cenv = e; fenv = fenv0; nenv = names;
  log = log0 }

type s_fns = fun_map

(** val remove_fundefs : fundefs -> fun_map -> fun_map **)

let rec remove_fundefs fds _UU03c1_ =
  match fds with
  | Nil -> _UU03c1_
  | Cons (f0, fds0) -> let Ffun (f, _, _, _) = f0 in Coq0_M.remove (iso_var.isoBofA f) (remove_fundefs fds0 _UU03c1_)

(** val preserves_S_S_fns : (exp_univ, s_fns) preserves_S **)

let preserves_S_S_fns =
  { preserve_S_up = (fun _ _ _ f e h ->
    match Obj.magic f with
    | Cons_fundef0 _ -> let Ffun (f0, x, x0, x1) = Obj.magic e in Coq0_M.set f0 (Pair ((Pair (x, x0)), x1)) h
    | Efun0 _ -> remove_fundefs (Obj.magic e) h
    | Efun1 l -> remove_fundefs l h
    | _ -> h); preserve_S_dn = (fun _ _ _ f e h ->
    match Obj.magic f with
    | Cons_fundef0 _ -> let Ffun (f0, _, _, _) = Obj.magic e in Coq0_M.remove f0 h
    | Efun0 _ -> add_fundefs (Obj.magic e) h
    | Efun1 l -> add_fundefs l h
    | _ -> h) }

type s_IH = inlineHeuristic
  (* singleton inductive, whose constructor was mk_IH *)

type s_inline =
  (exp_univ, (exp_univ, (exp_univ, (exp_univ, (exp_univ, comp_data) s_plain, s_IH) s_prod, s_fresh) s_prod, s_fns)
  s_prod, s_uniq) s_prod

(** val rw_inline : (exp_univ, exp_univ trivial_delay_t, exp_univ trivial_R_C, s_inline) rewriter **)

let rec rw_inline x a c e _ r s =
  match x with
  | XI _ ->
    (match a with
     | Exp_univ_prod_ctor_tag_exp ->
       let Pair (c0, e0) = Obj.magic e in
       let { resTree = x0; resState = s0 } =
         Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_prod_ctor_tag_exp,
           Exp_univ_exp, (Obj.magic (Pair_ctor_tag_exp1 c0)), c)) e0 Tt r
           (let f = Obj.magic (Pair_ctor_tag_exp1 c0) in
            let x0 = Obj.magic e0 in
            let Pair (s1, _) =
              let f0 = Obj.magic (Pair_ctor_tag_exp0 e0) in
              let x1 = Obj.magic c0 in
              let Pair (s1, _) = s in
              Pair
              ((let Pair (s2, s3) = s1 in
                Pair
                ((let Pair (s4, s5) = s2 in
                  Pair
                  ((let Pair (s6, s7) = s4 in
                    Pair (s6,
                    (match Obj.magic f0 with
                     | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x1)
                     | Efun0 e1 -> update_funDef1 s7 (Obj.magic x1) e1
                     | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                     | _ -> s7))), s5)),
                (preserves_S_S_fns.preserve_S_dn Exp_univ_ctor_tag Exp_univ_prod_ctor_tag_exp c f0 x1 s3))), __)
            in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair
              ((let Pair (s4, s5) = s2 in
                Pair
                ((let Pair (s6, s7) = s4 in
                  Pair (s6,
                  (match Obj.magic f with
                   | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x0)
                   | Efun0 e1 -> update_funDef1 s7 (Obj.magic x0) e1
                   | Efun1 l -> update_funDef2 s7 l (Obj.magic x0)
                   | _ -> s7))), s5)),
              (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_prod_ctor_tag_exp c f x0
                (preserves_S_S_fns.preserve_S_up Exp_univ_ctor_tag Exp_univ_prod_ctor_tag_exp c
                  (Obj.magic (Pair_ctor_tag_exp0 e0)) (Obj.magic c0) s3)))), __))
       in
       { resTree = (Obj.magic (Pair (c0, x0))); resState =
       (let Pair (s1, _) = s0 in
        Pair
        ((let Pair (s2, s3) = s1 in
          Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
          (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_prod_ctor_tag_exp c
            (Obj.magic (Pair_ctor_tag_exp1 c0)) x0 s3))), __)) }
     | Exp_univ_list_prod_ctor_tag_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (p, u) ->
           let pcte = Obj.magic p in
           let lpcte = Obj.magic u in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_inline (Pos.pred x) Exp_univ_prod_ctor_tag_exp (Frames_cons (Exp_univ_prod_ctor_tag_exp,
               Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, (Obj.magic (Cons_prod_ctor_tag_exp0 lpcte)), c)) pcte
               (Obj.magic Tt) r_C
               (let f = Obj.magic (Cons_prod_ctor_tag_exp0 lpcte) in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic pcte)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic pcte) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic pcte)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c f
                    pcte s3))), __))
           in
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))), c)) lpcte Tt r_C
               (let f = Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0)) in
                let x1 = Obj.magic lpcte in
                let Pair (s1, _) = s0 in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c
                    f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c
                      (Obj.magic (Cons_prod_ctor_tag_exp0 lpcte)) x0 s3)))), __))
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
             (let Pair (s2, _) = s1 in
              Pair
              ((let Pair (s3, s4) = s2 in
                Pair ((let Pair (s5, s6) = s3 in Pair ((let Pair (s7, s8) = s5 in Pair (s7, s8)), s6)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_list_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c
                  (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))) x1 s4))), __)) }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_fundef ->
       let Ffun (f, ft, xs, e0) = Obj.magic e in
       let { resTree = x2; resState = s0 } =
         Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_fundef, Exp_univ_exp,
           (Obj.magic (Ffun3 (f, ft, xs))), c)) e0 Tt r
           (let f0 = Obj.magic (Ffun3 (f, ft, xs)) in
            let x0 = Obj.magic e0 in
            let Pair (s1, _) =
              let f1 = Obj.magic (Ffun2 (f, ft, e0)) in
              let x1 = Obj.magic xs in
              let Pair (s1, _) =
                let f2 = Obj.magic (Ffun1 (f, xs, e0)) in
                let x2 = Obj.magic ft in
                let Pair (s1, _) =
                  let f3 = Obj.magic (Ffun0 (ft, xs, e0)) in
                  let x3 = Obj.magic f in
                  let Pair (s1, _) = s in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f3 with
                         | Ffun3 (v, f4, l) -> update_inFun s7 v f4 l (Obj.magic x3)
                         | Efun0 e1 -> update_funDef1 s7 (Obj.magic x3) e1
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_fundef c f3 x3 s3))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f2 with
                       | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x2)
                       | Efun0 e1 -> update_funDef1 s7 (Obj.magic x2) e1
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_fundef c f2 x2
                    (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_fundef c (Obj.magic (Ffun0 (ft, xs, e0)))
                      (Obj.magic f) s3)))), __)
              in
              Pair
              ((let Pair (s2, s3) = s1 in
                Pair
                ((let Pair (s4, s5) = s2 in
                  Pair
                  ((let Pair (s6, s7) = s4 in
                    Pair (s6,
                    (match Obj.magic f1 with
                     | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x1)
                     | Efun0 e1 -> update_funDef1 s7 (Obj.magic x1) e1
                     | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                     | _ -> s7))), s5)),
                (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_fundef c f1 x1
                  (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_fundef c
                    (Obj.magic (Ffun1 (f, xs, e0))) (Obj.magic ft) s3)))), __)
            in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair
              ((let Pair (s4, s5) = s2 in
                Pair
                ((let Pair (s6, s7) = s4 in
                  Pair (s6,
                  (match Obj.magic f0 with
                   | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x0)
                   | Efun0 e1 -> update_funDef1 s7 (Obj.magic x0) e1
                   | Efun1 l -> update_funDef2 s7 l (Obj.magic x0)
                   | _ -> s7))), s5)),
              (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_fundef c f0 x0
                (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_fundef c (Obj.magic (Ffun2 (f, ft, e0)))
                  (Obj.magic xs) s3)))), __))
       in
       { resTree = (Obj.magic (Ffun (f, ft, xs, (Obj.magic x2)))); resState =
       (let Pair (s1, _) = s0 in
        Pair
        ((let Pair (s2, s3) = s1 in
          Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
          (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_fundef c (Obj.magic (Ffun3 (f, ft, xs))) x2 s3))),
        __)) }
     | Exp_univ_list_fundef ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (f, u) ->
           let f0 = Obj.magic f in
           let lf = Obj.magic u in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_inline (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
               Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c)) f0 (Obj.magic Tt) r_C
               (let f1 = Obj.magic (Cons_fundef0 lf) in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f1 with
                       | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic f0)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic f0) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic f0)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_fundef Exp_univ_list_fundef c f1 f0 s3))), __))
           in
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
               Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C
               (let f1 = Obj.magic (Cons_fundef1 (Obj.magic x0)) in
                let x1 = Obj.magic lf in
                let Pair (s1, _) = s0 in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f1 with
                       | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_fundef Exp_univ_list_fundef c f1 x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_fundef Exp_univ_list_fundef c
                      (Obj.magic (Cons_fundef0 lf)) x0 s3)))), __))
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
             (let Pair (s2, _) = s1 in
              Pair
              ((let Pair (s3, s4) = s2 in
                Pair ((let Pair (s5, s6) = s3 in Pair ((let Pair (s7, s8) = s5 in Pair (s7, s8)), s6)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_list_fundef Exp_univ_list_fundef c
                  (Obj.magic (Cons_fundef1 (Obj.magic x0))) x1 s4))), __)) }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Econstr (x0, c0, ys, u) ->
           let { resTree = x2; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Econstr3 (x0, c0, ys))), c)) u Tt r
               (let f = Obj.magic (Econstr3 (x0, c0, ys)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Econstr2 (x0, c0, u)) in
                  let x2 = Obj.magic ys in
                  let Pair (s1, _) =
                    let f1 = Obj.magic (Econstr1 (x0, ys, u)) in
                    let x3 = Obj.magic c0 in
                    let Pair (s1, _) =
                      let f2 = Obj.magic (Econstr0 (c0, ys, u)) in
                      let x4 = Obj.magic x0 in
                      let Pair (s1, _) = s in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f2 with
                             | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 x4 s3))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f1 with
                           | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_ctor_tag Exp_univ_exp c f1 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                          (Obj.magic (Econstr0 (c0, ys, u))) (Obj.magic x0) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_ctor_tag Exp_univ_exp c
                        (Obj.magic (Econstr1 (x0, ys, u))) (Obj.magic c0) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                      (Obj.magic (Econstr2 (x0, c0, u))) (Obj.magic ys) s3)))), __))
           in
           { resTree = (Obj.magic (Econstr (x0, c0, ys, (Obj.magic x2)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Econstr3 (x0, c0, ys))) x2 s3))),
            __)) }
         | Ecase (x0, ces) ->
           let { resTree = x1; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase1 x0)), c)) ces Tt r
               (let f = Obj.magic (Ecase1 x0) in
                let x1 = Obj.magic ces in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Ecase0 ces) in
                  let x2 = Obj.magic x0 in
                  let Pair (s1, _) = s in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)), (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f0 x2 s3))),
                  __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_prod_ctor_tag_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic (Ecase0 ces))
                      (Obj.magic x0) s3)))), __))
           in
           { resTree = (Obj.magic (Ecase (x0, (Obj.magic x1)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_list_prod_ctor_tag_exp Exp_univ_exp c
                (Obj.magic (Ecase1 x0)) x1 s3))), __)) }
         | Eproj (x0, c0, n0, y, u) ->
           let { resTree = x3; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eproj4 (x0, c0, n0, y))), c)) u Tt r
               (let f = Obj.magic (Eproj4 (x0, c0, n0, y)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Eproj3 (x0, c0, n0, u)) in
                  let x2 = Obj.magic y in
                  let Pair (s1, _) =
                    let f1 = Obj.magic (Eproj2 (x0, c0, y, u)) in
                    let x3 = Obj.magic n0 in
                    let Pair (s1, _) =
                      let f2 = Obj.magic (Eproj1 (x0, n0, y, u)) in
                      let x4 = Obj.magic c0 in
                      let Pair (s1, _) =
                        let f3 = Obj.magic (Eproj0 (c0, n0, y, u)) in
                        let x5 = Obj.magic x0 in
                        let Pair (s1, _) = s in
                        Pair
                        ((let Pair (s2, s3) = s1 in
                          Pair
                          ((let Pair (s4, s5) = s2 in
                            Pair
                            ((let Pair (s6, s7) = s4 in
                              Pair (s6,
                              (match Obj.magic f3 with
                               | Ffun3 (v, f4, l) -> update_inFun s7 v f4 l (Obj.magic x5)
                               | Efun0 e0 -> update_funDef1 s7 (Obj.magic x5) e0
                               | Efun1 l -> update_funDef2 s7 l (Obj.magic x5)
                               | _ -> s7))), s5)),
                          (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f3 x5 s3))), __)
                      in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f2 with
                             | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_ctor_tag Exp_univ_exp c f2 x4
                          (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                            (Obj.magic (Eproj0 (c0, n0, y, u))) (Obj.magic x0) s3)))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f1 with
                           | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_N Exp_univ_exp c f1 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_ctor_tag Exp_univ_exp c
                          (Obj.magic (Eproj1 (x0, n0, y, u))) (Obj.magic c0) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f0 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_N Exp_univ_exp c (Obj.magic (Eproj2 (x0, c0, y, u)))
                        (Obj.magic n0) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                      (Obj.magic (Eproj3 (x0, c0, n0, u))) (Obj.magic y) s3)))), __))
           in
           { resTree = (Obj.magic (Eproj (x0, c0, n0, y, (Obj.magic x3)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Eproj4 (x0, c0, n0, y))) x3
                s3))), __)) }
         | Eletapp (x0, f, ft, ys, u) ->
           let { resTree = x3; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eletapp4 (x0, f, ft, ys))), c)) u Tt r
               (let f0 = Obj.magic (Eletapp4 (x0, f, ft, ys)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f1 = Obj.magic (Eletapp3 (x0, f, ft, u)) in
                  let x2 = Obj.magic ys in
                  let Pair (s1, _) =
                    let f2 = Obj.magic (Eletapp2 (x0, f, ys, u)) in
                    let x3 = Obj.magic ft in
                    let Pair (s1, _) =
                      let f3 = Obj.magic (Eletapp1 (x0, ft, ys, u)) in
                      let x4 = Obj.magic f in
                      let Pair (s1, _) =
                        let f4 = Obj.magic (Eletapp0 (f, ft, ys, u)) in
                        let x5 = Obj.magic x0 in
                        let Pair (s1, _) = s in
                        Pair
                        ((let Pair (s2, s3) = s1 in
                          Pair
                          ((let Pair (s4, s5) = s2 in
                            Pair
                            ((let Pair (s6, s7) = s4 in
                              Pair (s6,
                              (match Obj.magic f4 with
                               | Ffun3 (v, f5, l) -> update_inFun s7 v f5 l (Obj.magic x5)
                               | Efun0 e0 -> update_funDef1 s7 (Obj.magic x5) e0
                               | Efun1 l -> update_funDef2 s7 l (Obj.magic x5)
                               | _ -> s7))), s5)),
                          (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f4 x5 s3))), __)
                      in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f3 with
                             | Ffun3 (v, f4, l) -> update_inFun s7 v f4 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f3 x4
                          (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                            (Obj.magic (Eletapp0 (f, ft, ys, u))) (Obj.magic x0) s3)))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f2 with
                           | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f2 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                          (Obj.magic (Eletapp1 (x0, ft, ys, u))) (Obj.magic f) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f1 with
                         | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f1 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                        (Obj.magic (Eletapp2 (x0, f, ys, u))) (Obj.magic ft) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f0 with
                       | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f0 x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                      (Obj.magic (Eletapp3 (x0, f, ft, u))) (Obj.magic ys) s3)))), __))
           in
           { resTree = (Obj.magic (Eletapp (x0, f, ft, ys, (Obj.magic x3)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Eletapp4 (x0, f, ft, ys))) x3
                s3))), __)) }
         | Efun (fds, u) ->
           let lf = Obj.magic fds in
           let e0 = Obj.magic u in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_inline (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef, Exp_univ_exp,
               Exp_univ_exp, (Obj.magic (Efun0 e0)), c)) lf (Obj.magic Tt) r_C
               (let f = Obj.magic (Efun0 e0) in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic lf)
                       | Efun0 e1 -> update_funDef1 s7 (Obj.magic lf) e1
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic lf)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_fundef Exp_univ_exp c f lf s3))), __))
           in
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Efun1 (Obj.magic x0))), c)) e0 Tt r_C
               (let f = Obj.magic (Efun1 (Obj.magic x0)) in
                let x1 = Obj.magic e0 in
                let Pair (s1, _) = s0 in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e1 -> update_funDef1 s7 (Obj.magic x1) e1
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_fundef Exp_univ_exp c (Obj.magic (Efun0 e0)) x0
                      s3)))), __))
           in
           Obj.magic { resTree = (Obj.magic (Efun ((Obj.magic x0), (Obj.magic x1)))); resState =
             (let Pair (s2, _) = s1 in
              Pair
              ((let Pair (s3, s4) = s2 in
                Pair ((let Pair (s5, s6) = s3 in Pair ((let Pair (s7, s8) = s5 in Pair (s7, s8)), s6)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Efun1 (Obj.magic x0))) x1
                  s4))), __)) }
         | Eapp (f, ft, xs) ->
           let Pair (s0, _) = s in
           let Pair (s1, x0) = s0 in
           let Pair (s2, x1) = s1 in
           let Pair (cdata, s3) = s2 in
           (match Coq0_M.get (iso_var.isoBofA f) x0 with
            | Some p ->
              let Pair (p0, x2) = p in
              let Pair (ft0, xs0) = p0 in
              (match decide_App s3 f ft0 xs with
               | True ->
                 (match set_lists (iso_vars.isoBofA xs0) (iso_vars.isoBofA xs) Coq0_M.empty with
                  | Some _UU03c3_ ->
                    let Pair (fresh', e') = freshen_exp x1 Coq0_M.empty x2 in
                    let { resTree = x'; resState = s' } =
                      rw_inline (Pos.pred x) Exp_univ_exp c (Obj.magic rename_all' _UU03c3_ e') (Obj.magic Tt)
                        (Obj.magic Tt)
                        (Obj.magic (Pair ((Pair ((Pair ((Pair ((update_next_var fresh' cdata),
                          (update_App s3 f ft0 xs))), fresh')), x0)), __)))
                    in
                    Obj.magic { resTree = x'; resState = s' }
                  | None ->
                    let v0 = Obj.magic f in
                    let ft1 = Obj.magic ft in
                    let lv0 = Obj.magic xs in
                    Obj.magic { resTree = (Obj.magic (Eapp ((Obj.magic v0), ft1, lv0))); resState =
                      (let Pair (s4, _) =
                         let f0 = Obj.magic (Eapp2 ((Obj.magic v0), ft1)) in
                         let x3 = Obj.magic lv0 in
                         let Pair (s4, _) =
                           let f1 = Obj.magic (Eapp1 ((Obj.magic v0), lv0)) in
                           let x4 = Obj.magic ft1 in
                           let Pair (s4, _) =
                             let f2 = Obj.magic (Eapp0 (ft1, lv0)) in
                             let Pair (s4, _) = Obj.magic s in
                             Pair
                             ((let Pair (s5, s6) = s4 in
                               Pair
                               ((let Pair (s7, s8) = s5 in
                                 Pair
                                 ((let Pair (s9, s10) = s7 in
                                   Pair (s9,
                                   (match Obj.magic f2 with
                                    | Ffun3 (v, f3, l) -> update_inFun s10 v f3 l (Obj.magic v0)
                                    | Efun0 e0 -> update_funDef1 s10 (Obj.magic v0) e0
                                    | Efun1 l -> update_funDef2 s10 l (Obj.magic v0)
                                    | _ -> s10))), s8)),
                               (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 v0 s6))), __)
                           in
                           Pair
                           ((let Pair (s5, s6) = s4 in
                             Pair
                             ((let Pair (s7, s8) = s5 in
                               Pair
                               ((let Pair (s9, s10) = s7 in
                                 Pair (s9,
                                 (match Obj.magic f1 with
                                  | Ffun3 (v, f2, l) -> update_inFun s10 v f2 l (Obj.magic x4)
                                  | Efun0 e0 -> update_funDef1 s10 (Obj.magic x4) e0
                                  | Efun1 l -> update_funDef2 s10 l (Obj.magic x4)
                                  | _ -> s10))), s8)),
                             (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f1 x4
                               (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                                 (Obj.magic (Eapp0 (ft1, lv0))) v0 s6)))), __)
                         in
                         Pair
                         ((let Pair (s5, s6) = s4 in
                           Pair
                           ((let Pair (s7, s8) = s5 in
                             Pair
                             ((let Pair (s9, s10) = s7 in
                               Pair (s9,
                               (match Obj.magic f0 with
                                | Ffun3 (v, f1, l) -> update_inFun s10 v f1 l (Obj.magic x3)
                                | Efun0 e0 -> update_funDef1 s10 (Obj.magic x3) e0
                                | Efun1 l -> update_funDef2 s10 l (Obj.magic x3)
                                | _ -> s10))), s8)),
                           (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x3
                             (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                               (Obj.magic (Eapp1 ((Obj.magic v0), lv0))) (Obj.magic ft1) s6)))), __)
                       in
                       Pair
                       ((let Pair (s5, s6) = s4 in
                         Pair ((let Pair (s7, s8) = s5 in Pair ((let Pair (s9, s10) = s7 in Pair (s9, s10)), s8)),
                         (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                           (Obj.magic (Eapp2 ((Obj.magic v0), ft1))) (Obj.magic lv0) s6))), __)) })
               | False ->
                 let v0 = Obj.magic f in
                 let ft1 = Obj.magic ft in
                 let lv0 = Obj.magic xs in
                 Obj.magic { resTree = (Obj.magic (Eapp ((Obj.magic v0), ft1, lv0))); resState =
                   (let Pair (s4, _) =
                      let f0 = Obj.magic (Eapp2 ((Obj.magic v0), ft1)) in
                      let x3 = Obj.magic lv0 in
                      let Pair (s4, _) =
                        let f1 = Obj.magic (Eapp1 ((Obj.magic v0), lv0)) in
                        let x4 = Obj.magic ft1 in
                        let Pair (s4, _) =
                          let f2 = Obj.magic (Eapp0 (ft1, lv0)) in
                          let Pair (s4, _) = Obj.magic s in
                          Pair
                          ((let Pair (s5, s6) = s4 in
                            Pair
                            ((let Pair (s7, s8) = s5 in
                              Pair
                              ((let Pair (s9, s10) = s7 in
                                Pair (s9,
                                (match Obj.magic f2 with
                                 | Ffun3 (v, f3, l) -> update_inFun s10 v f3 l (Obj.magic v0)
                                 | Efun0 e0 -> update_funDef1 s10 (Obj.magic v0) e0
                                 | Efun1 l -> update_funDef2 s10 l (Obj.magic v0)
                                 | _ -> s10))), s8)),
                            (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 v0 s6))), __)
                        in
                        Pair
                        ((let Pair (s5, s6) = s4 in
                          Pair
                          ((let Pair (s7, s8) = s5 in
                            Pair
                            ((let Pair (s9, s10) = s7 in
                              Pair (s9,
                              (match Obj.magic f1 with
                               | Ffun3 (v, f2, l) -> update_inFun s10 v f2 l (Obj.magic x4)
                               | Efun0 e0 -> update_funDef1 s10 (Obj.magic x4) e0
                               | Efun1 l -> update_funDef2 s10 l (Obj.magic x4)
                               | _ -> s10))), s8)),
                          (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f1 x4
                            (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                              (Obj.magic (Eapp0 (ft1, lv0))) v0 s6)))), __)
                      in
                      Pair
                      ((let Pair (s5, s6) = s4 in
                        Pair
                        ((let Pair (s7, s8) = s5 in
                          Pair
                          ((let Pair (s9, s10) = s7 in
                            Pair (s9,
                            (match Obj.magic f0 with
                             | Ffun3 (v, f1, l) -> update_inFun s10 v f1 l (Obj.magic x3)
                             | Efun0 e0 -> update_funDef1 s10 (Obj.magic x3) e0
                             | Efun1 l -> update_funDef2 s10 l (Obj.magic x3)
                             | _ -> s10))), s8)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x3
                          (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                            (Obj.magic (Eapp1 ((Obj.magic v0), lv0))) (Obj.magic ft1) s6)))), __)
                    in
                    Pair
                    ((let Pair (s5, s6) = s4 in
                      Pair ((let Pair (s7, s8) = s5 in Pair ((let Pair (s9, s10) = s7 in Pair (s9, s10)), s8)),
                      (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                        (Obj.magic (Eapp2 ((Obj.magic v0), ft1))) (Obj.magic lv0) s6))), __)) })
            | None ->
              let v0 = Obj.magic f in
              let ft0 = Obj.magic ft in
              let lv0 = Obj.magic xs in
              Obj.magic { resTree = (Obj.magic (Eapp ((Obj.magic v0), ft0, lv0))); resState =
                (let Pair (s4, _) =
                   let f0 = Obj.magic (Eapp2 ((Obj.magic v0), ft0)) in
                   let x2 = Obj.magic lv0 in
                   let Pair (s4, _) =
                     let f1 = Obj.magic (Eapp1 ((Obj.magic v0), lv0)) in
                     let x3 = Obj.magic ft0 in
                     let Pair (s4, _) =
                       let f2 = Obj.magic (Eapp0 (ft0, lv0)) in
                       let Pair (s4, _) = Obj.magic s in
                       Pair
                       ((let Pair (s5, s6) = s4 in
                         Pair
                         ((let Pair (s7, s8) = s5 in
                           Pair
                           ((let Pair (s9, s10) = s7 in
                             Pair (s9,
                             (match Obj.magic f2 with
                              | Ffun3 (v, f3, l) -> update_inFun s10 v f3 l (Obj.magic v0)
                              | Efun0 e0 -> update_funDef1 s10 (Obj.magic v0) e0
                              | Efun1 l -> update_funDef2 s10 l (Obj.magic v0)
                              | _ -> s10))), s8)),
                         (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 v0 s6))), __)
                     in
                     Pair
                     ((let Pair (s5, s6) = s4 in
                       Pair
                       ((let Pair (s7, s8) = s5 in
                         Pair
                         ((let Pair (s9, s10) = s7 in
                           Pair (s9,
                           (match Obj.magic f1 with
                            | Ffun3 (v, f2, l) -> update_inFun s10 v f2 l (Obj.magic x3)
                            | Efun0 e0 -> update_funDef1 s10 (Obj.magic x3) e0
                            | Efun1 l -> update_funDef2 s10 l (Obj.magic x3)
                            | _ -> s10))), s8)),
                       (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f1 x3
                         (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic (Eapp0 (ft0, lv0)))
                           v0 s6)))), __)
                   in
                   Pair
                   ((let Pair (s5, s6) = s4 in
                     Pair
                     ((let Pair (s7, s8) = s5 in
                       Pair
                       ((let Pair (s9, s10) = s7 in
                         Pair (s9,
                         (match Obj.magic f0 with
                          | Ffun3 (v, f1, l) -> update_inFun s10 v f1 l (Obj.magic x2)
                          | Efun0 e0 -> update_funDef1 s10 (Obj.magic x2) e0
                          | Efun1 l -> update_funDef2 s10 l (Obj.magic x2)
                          | _ -> s10))), s8)),
                     (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x2
                       (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                         (Obj.magic (Eapp1 ((Obj.magic v0), lv0))) (Obj.magic ft0) s6)))), __)
                 in
                 Pair
                 ((let Pair (s5, s6) = s4 in
                   Pair ((let Pair (s7, s8) = s5 in Pair ((let Pair (s9, s10) = s7 in Pair (s9, s10)), s8)),
                   (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                     (Obj.magic (Eapp2 ((Obj.magic v0), ft0))) (Obj.magic lv0) s6))), __)) })
         | Eprim (x0, p, ys, u) ->
           let { resTree = x2; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eprim3 (x0, p, ys))), c)) u Tt r
               (let f = Obj.magic (Eprim3 (x0, p, ys)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Eprim2 (x0, p, u)) in
                  let x2 = Obj.magic ys in
                  let Pair (s1, _) =
                    let f1 = Obj.magic (Eprim1 (x0, ys, u)) in
                    let x3 = Obj.magic p in
                    let Pair (s1, _) =
                      let f2 = Obj.magic (Eprim0 (p, ys, u)) in
                      let x4 = Obj.magic x0 in
                      let Pair (s1, _) = s in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f2 with
                             | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 x4 s3))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f1 with
                           | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_prim Exp_univ_exp c f1 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic (Eprim0 (p, ys, u)))
                          (Obj.magic x0) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_prim Exp_univ_exp c (Obj.magic (Eprim1 (x0, ys, u)))
                        (Obj.magic p) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                      (Obj.magic (Eprim2 (x0, p, u))) (Obj.magic ys) s3)))), __))
           in
           { resTree = (Obj.magic (Eprim (x0, p, ys, (Obj.magic x2)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Eprim3 (x0, p, ys))) x2 s3))),
            __)) }
         | Ehalt x0 ->
           let v0 = Obj.magic x0 in
           Obj.magic { resTree = (Obj.magic (Ehalt (Obj.magic v0))); resState =
             (let Pair (s1, _) =
                let f = Obj.magic Ehalt0 in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic v0)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic v0) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic v0)
                       | _ -> s7))), s5)), (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f v0 s3))),
                __)
              in
              Pair
              ((let Pair (s2, s3) = s1 in
                Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic Ehalt0) v0 s3))), __)) }
       in
       { resTree = e'; resState = s' }
     | _ -> { resTree = e; resState = s })
  | XO _ ->
    (match a with
     | Exp_univ_prod_ctor_tag_exp ->
       let Pair (c0, e0) = Obj.magic e in
       let { resTree = x0; resState = s0 } =
         Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_prod_ctor_tag_exp,
           Exp_univ_exp, (Obj.magic (Pair_ctor_tag_exp1 c0)), c)) e0 Tt r
           (let f = Obj.magic (Pair_ctor_tag_exp1 c0) in
            let x0 = Obj.magic e0 in
            let Pair (s1, _) =
              let f0 = Obj.magic (Pair_ctor_tag_exp0 e0) in
              let x1 = Obj.magic c0 in
              let Pair (s1, _) = s in
              Pair
              ((let Pair (s2, s3) = s1 in
                Pair
                ((let Pair (s4, s5) = s2 in
                  Pair
                  ((let Pair (s6, s7) = s4 in
                    Pair (s6,
                    (match Obj.magic f0 with
                     | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x1)
                     | Efun0 e1 -> update_funDef1 s7 (Obj.magic x1) e1
                     | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                     | _ -> s7))), s5)),
                (preserves_S_S_fns.preserve_S_dn Exp_univ_ctor_tag Exp_univ_prod_ctor_tag_exp c f0 x1 s3))), __)
            in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair
              ((let Pair (s4, s5) = s2 in
                Pair
                ((let Pair (s6, s7) = s4 in
                  Pair (s6,
                  (match Obj.magic f with
                   | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x0)
                   | Efun0 e1 -> update_funDef1 s7 (Obj.magic x0) e1
                   | Efun1 l -> update_funDef2 s7 l (Obj.magic x0)
                   | _ -> s7))), s5)),
              (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_prod_ctor_tag_exp c f x0
                (preserves_S_S_fns.preserve_S_up Exp_univ_ctor_tag Exp_univ_prod_ctor_tag_exp c
                  (Obj.magic (Pair_ctor_tag_exp0 e0)) (Obj.magic c0) s3)))), __))
       in
       { resTree = (Obj.magic (Pair (c0, x0))); resState =
       (let Pair (s1, _) = s0 in
        Pair
        ((let Pair (s2, s3) = s1 in
          Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
          (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_prod_ctor_tag_exp c
            (Obj.magic (Pair_ctor_tag_exp1 c0)) x0 s3))), __)) }
     | Exp_univ_list_prod_ctor_tag_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (p, u) ->
           let pcte = Obj.magic p in
           let lpcte = Obj.magic u in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_inline (Pos.pred x) Exp_univ_prod_ctor_tag_exp (Frames_cons (Exp_univ_prod_ctor_tag_exp,
               Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, (Obj.magic (Cons_prod_ctor_tag_exp0 lpcte)), c)) pcte
               (Obj.magic Tt) r_C
               (let f = Obj.magic (Cons_prod_ctor_tag_exp0 lpcte) in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic pcte)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic pcte) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic pcte)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c f
                    pcte s3))), __))
           in
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))), c)) lpcte Tt r_C
               (let f = Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0)) in
                let x1 = Obj.magic lpcte in
                let Pair (s1, _) = s0 in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c
                    f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c
                      (Obj.magic (Cons_prod_ctor_tag_exp0 lpcte)) x0 s3)))), __))
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
             (let Pair (s2, _) = s1 in
              Pair
              ((let Pair (s3, s4) = s2 in
                Pair ((let Pair (s5, s6) = s3 in Pair ((let Pair (s7, s8) = s5 in Pair (s7, s8)), s6)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_list_prod_ctor_tag_exp Exp_univ_list_prod_ctor_tag_exp c
                  (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))) x1 s4))), __)) }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_fundef ->
       let Ffun (f, ft, xs, e0) = Obj.magic e in
       let { resTree = x2; resState = s0 } =
         Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_fundef, Exp_univ_exp,
           (Obj.magic (Ffun3 (f, ft, xs))), c)) e0 Tt r
           (let f0 = Obj.magic (Ffun3 (f, ft, xs)) in
            let x0 = Obj.magic e0 in
            let Pair (s1, _) =
              let f1 = Obj.magic (Ffun2 (f, ft, e0)) in
              let x1 = Obj.magic xs in
              let Pair (s1, _) =
                let f2 = Obj.magic (Ffun1 (f, xs, e0)) in
                let x2 = Obj.magic ft in
                let Pair (s1, _) =
                  let f3 = Obj.magic (Ffun0 (ft, xs, e0)) in
                  let x3 = Obj.magic f in
                  let Pair (s1, _) = s in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f3 with
                         | Ffun3 (v, f4, l) -> update_inFun s7 v f4 l (Obj.magic x3)
                         | Efun0 e1 -> update_funDef1 s7 (Obj.magic x3) e1
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_fundef c f3 x3 s3))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f2 with
                       | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x2)
                       | Efun0 e1 -> update_funDef1 s7 (Obj.magic x2) e1
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_fundef c f2 x2
                    (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_fundef c (Obj.magic (Ffun0 (ft, xs, e0)))
                      (Obj.magic f) s3)))), __)
              in
              Pair
              ((let Pair (s2, s3) = s1 in
                Pair
                ((let Pair (s4, s5) = s2 in
                  Pair
                  ((let Pair (s6, s7) = s4 in
                    Pair (s6,
                    (match Obj.magic f1 with
                     | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x1)
                     | Efun0 e1 -> update_funDef1 s7 (Obj.magic x1) e1
                     | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                     | _ -> s7))), s5)),
                (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_fundef c f1 x1
                  (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_fundef c
                    (Obj.magic (Ffun1 (f, xs, e0))) (Obj.magic ft) s3)))), __)
            in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair
              ((let Pair (s4, s5) = s2 in
                Pair
                ((let Pair (s6, s7) = s4 in
                  Pair (s6,
                  (match Obj.magic f0 with
                   | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x0)
                   | Efun0 e1 -> update_funDef1 s7 (Obj.magic x0) e1
                   | Efun1 l -> update_funDef2 s7 l (Obj.magic x0)
                   | _ -> s7))), s5)),
              (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_fundef c f0 x0
                (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_fundef c (Obj.magic (Ffun2 (f, ft, e0)))
                  (Obj.magic xs) s3)))), __))
       in
       { resTree = (Obj.magic (Ffun (f, ft, xs, (Obj.magic x2)))); resState =
       (let Pair (s1, _) = s0 in
        Pair
        ((let Pair (s2, s3) = s1 in
          Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
          (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_fundef c (Obj.magic (Ffun3 (f, ft, xs))) x2 s3))),
        __)) }
     | Exp_univ_list_fundef ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (f, u) ->
           let f0 = Obj.magic f in
           let lf = Obj.magic u in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_inline (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
               Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c)) f0 (Obj.magic Tt) r_C
               (let f1 = Obj.magic (Cons_fundef0 lf) in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f1 with
                       | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic f0)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic f0) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic f0)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_fundef Exp_univ_list_fundef c f1 f0 s3))), __))
           in
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
               Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C
               (let f1 = Obj.magic (Cons_fundef1 (Obj.magic x0)) in
                let x1 = Obj.magic lf in
                let Pair (s1, _) = s0 in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f1 with
                       | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_fundef Exp_univ_list_fundef c f1 x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_fundef Exp_univ_list_fundef c
                      (Obj.magic (Cons_fundef0 lf)) x0 s3)))), __))
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
             (let Pair (s2, _) = s1 in
              Pair
              ((let Pair (s3, s4) = s2 in
                Pair ((let Pair (s5, s6) = s3 in Pair ((let Pair (s7, s8) = s5 in Pair (s7, s8)), s6)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_list_fundef Exp_univ_list_fundef c
                  (Obj.magic (Cons_fundef1 (Obj.magic x0))) x1 s4))), __)) }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Econstr (x0, c0, ys, u) ->
           let { resTree = x2; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Econstr3 (x0, c0, ys))), c)) u Tt r
               (let f = Obj.magic (Econstr3 (x0, c0, ys)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Econstr2 (x0, c0, u)) in
                  let x2 = Obj.magic ys in
                  let Pair (s1, _) =
                    let f1 = Obj.magic (Econstr1 (x0, ys, u)) in
                    let x3 = Obj.magic c0 in
                    let Pair (s1, _) =
                      let f2 = Obj.magic (Econstr0 (c0, ys, u)) in
                      let x4 = Obj.magic x0 in
                      let Pair (s1, _) = s in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f2 with
                             | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 x4 s3))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f1 with
                           | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_ctor_tag Exp_univ_exp c f1 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                          (Obj.magic (Econstr0 (c0, ys, u))) (Obj.magic x0) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_ctor_tag Exp_univ_exp c
                        (Obj.magic (Econstr1 (x0, ys, u))) (Obj.magic c0) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                      (Obj.magic (Econstr2 (x0, c0, u))) (Obj.magic ys) s3)))), __))
           in
           { resTree = (Obj.magic (Econstr (x0, c0, ys, (Obj.magic x2)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Econstr3 (x0, c0, ys))) x2 s3))),
            __)) }
         | Ecase (x0, ces) ->
           let { resTree = x1; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase1 x0)), c)) ces Tt r
               (let f = Obj.magic (Ecase1 x0) in
                let x1 = Obj.magic ces in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Ecase0 ces) in
                  let x2 = Obj.magic x0 in
                  let Pair (s1, _) = s in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)), (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f0 x2 s3))),
                  __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_prod_ctor_tag_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic (Ecase0 ces))
                      (Obj.magic x0) s3)))), __))
           in
           { resTree = (Obj.magic (Ecase (x0, (Obj.magic x1)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_list_prod_ctor_tag_exp Exp_univ_exp c
                (Obj.magic (Ecase1 x0)) x1 s3))), __)) }
         | Eproj (x0, c0, n0, y, u) ->
           let { resTree = x3; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eproj4 (x0, c0, n0, y))), c)) u Tt r
               (let f = Obj.magic (Eproj4 (x0, c0, n0, y)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Eproj3 (x0, c0, n0, u)) in
                  let x2 = Obj.magic y in
                  let Pair (s1, _) =
                    let f1 = Obj.magic (Eproj2 (x0, c0, y, u)) in
                    let x3 = Obj.magic n0 in
                    let Pair (s1, _) =
                      let f2 = Obj.magic (Eproj1 (x0, n0, y, u)) in
                      let x4 = Obj.magic c0 in
                      let Pair (s1, _) =
                        let f3 = Obj.magic (Eproj0 (c0, n0, y, u)) in
                        let x5 = Obj.magic x0 in
                        let Pair (s1, _) = s in
                        Pair
                        ((let Pair (s2, s3) = s1 in
                          Pair
                          ((let Pair (s4, s5) = s2 in
                            Pair
                            ((let Pair (s6, s7) = s4 in
                              Pair (s6,
                              (match Obj.magic f3 with
                               | Ffun3 (v, f4, l) -> update_inFun s7 v f4 l (Obj.magic x5)
                               | Efun0 e0 -> update_funDef1 s7 (Obj.magic x5) e0
                               | Efun1 l -> update_funDef2 s7 l (Obj.magic x5)
                               | _ -> s7))), s5)),
                          (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f3 x5 s3))), __)
                      in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f2 with
                             | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_ctor_tag Exp_univ_exp c f2 x4
                          (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                            (Obj.magic (Eproj0 (c0, n0, y, u))) (Obj.magic x0) s3)))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f1 with
                           | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_N Exp_univ_exp c f1 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_ctor_tag Exp_univ_exp c
                          (Obj.magic (Eproj1 (x0, n0, y, u))) (Obj.magic c0) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f0 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_N Exp_univ_exp c (Obj.magic (Eproj2 (x0, c0, y, u)))
                        (Obj.magic n0) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                      (Obj.magic (Eproj3 (x0, c0, n0, u))) (Obj.magic y) s3)))), __))
           in
           { resTree = (Obj.magic (Eproj (x0, c0, n0, y, (Obj.magic x3)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Eproj4 (x0, c0, n0, y))) x3
                s3))), __)) }
         | Eletapp (x0, f, ft, ys, u) ->
           let { resTree = x3; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eletapp4 (x0, f, ft, ys))), c)) u Tt r
               (let f0 = Obj.magic (Eletapp4 (x0, f, ft, ys)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f1 = Obj.magic (Eletapp3 (x0, f, ft, u)) in
                  let x2 = Obj.magic ys in
                  let Pair (s1, _) =
                    let f2 = Obj.magic (Eletapp2 (x0, f, ys, u)) in
                    let x3 = Obj.magic ft in
                    let Pair (s1, _) =
                      let f3 = Obj.magic (Eletapp1 (x0, ft, ys, u)) in
                      let x4 = Obj.magic f in
                      let Pair (s1, _) =
                        let f4 = Obj.magic (Eletapp0 (f, ft, ys, u)) in
                        let x5 = Obj.magic x0 in
                        let Pair (s1, _) = s in
                        Pair
                        ((let Pair (s2, s3) = s1 in
                          Pair
                          ((let Pair (s4, s5) = s2 in
                            Pair
                            ((let Pair (s6, s7) = s4 in
                              Pair (s6,
                              (match Obj.magic f4 with
                               | Ffun3 (v, f5, l) -> update_inFun s7 v f5 l (Obj.magic x5)
                               | Efun0 e0 -> update_funDef1 s7 (Obj.magic x5) e0
                               | Efun1 l -> update_funDef2 s7 l (Obj.magic x5)
                               | _ -> s7))), s5)),
                          (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f4 x5 s3))), __)
                      in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f3 with
                             | Ffun3 (v, f4, l) -> update_inFun s7 v f4 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f3 x4
                          (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                            (Obj.magic (Eletapp0 (f, ft, ys, u))) (Obj.magic x0) s3)))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f2 with
                           | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f2 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                          (Obj.magic (Eletapp1 (x0, ft, ys, u))) (Obj.magic f) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f1 with
                         | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f1 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                        (Obj.magic (Eletapp2 (x0, f, ys, u))) (Obj.magic ft) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f0 with
                       | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f0 x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                      (Obj.magic (Eletapp3 (x0, f, ft, u))) (Obj.magic ys) s3)))), __))
           in
           { resTree = (Obj.magic (Eletapp (x0, f, ft, ys, (Obj.magic x3)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Eletapp4 (x0, f, ft, ys))) x3
                s3))), __)) }
         | Efun (fds, u) ->
           let lf = Obj.magic fds in
           let e0 = Obj.magic u in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_inline (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef, Exp_univ_exp,
               Exp_univ_exp, (Obj.magic (Efun0 e0)), c)) lf (Obj.magic Tt) r_C
               (let f = Obj.magic (Efun0 e0) in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic lf)
                       | Efun0 e1 -> update_funDef1 s7 (Obj.magic lf) e1
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic lf)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_list_fundef Exp_univ_exp c f lf s3))), __))
           in
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Efun1 (Obj.magic x0))), c)) e0 Tt r_C
               (let f = Obj.magic (Efun1 (Obj.magic x0)) in
                let x1 = Obj.magic e0 in
                let Pair (s1, _) = s0 in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e1 -> update_funDef1 s7 (Obj.magic x1) e1
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_fundef Exp_univ_exp c (Obj.magic (Efun0 e0)) x0
                      s3)))), __))
           in
           Obj.magic { resTree = (Obj.magic (Efun ((Obj.magic x0), (Obj.magic x1)))); resState =
             (let Pair (s2, _) = s1 in
              Pair
              ((let Pair (s3, s4) = s2 in
                Pair ((let Pair (s5, s6) = s3 in Pair ((let Pair (s7, s8) = s5 in Pair (s7, s8)), s6)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Efun1 (Obj.magic x0))) x1
                  s4))), __)) }
         | Eapp (f, ft, xs) ->
           let Pair (s0, _) = s in
           let Pair (s1, x0) = s0 in
           let Pair (s2, x1) = s1 in
           let Pair (cdata, s3) = s2 in
           (match Coq0_M.get (iso_var.isoBofA f) x0 with
            | Some p ->
              let Pair (p0, x2) = p in
              let Pair (ft0, xs0) = p0 in
              (match decide_App s3 f ft0 xs with
               | True ->
                 (match set_lists (iso_vars.isoBofA xs0) (iso_vars.isoBofA xs) Coq0_M.empty with
                  | Some _UU03c3_ ->
                    let Pair (fresh', e') = freshen_exp x1 Coq0_M.empty x2 in
                    let { resTree = x'; resState = s' } =
                      rw_inline (Pos.pred x) Exp_univ_exp c (Obj.magic rename_all' _UU03c3_ e') (Obj.magic Tt)
                        (Obj.magic Tt)
                        (Obj.magic (Pair ((Pair ((Pair ((Pair ((update_next_var fresh' cdata),
                          (update_App s3 f ft0 xs))), fresh')), x0)), __)))
                    in
                    Obj.magic { resTree = x'; resState = s' }
                  | None ->
                    let v0 = Obj.magic f in
                    let ft1 = Obj.magic ft in
                    let lv0 = Obj.magic xs in
                    Obj.magic { resTree = (Obj.magic (Eapp ((Obj.magic v0), ft1, lv0))); resState =
                      (let Pair (s4, _) =
                         let f0 = Obj.magic (Eapp2 ((Obj.magic v0), ft1)) in
                         let x3 = Obj.magic lv0 in
                         let Pair (s4, _) =
                           let f1 = Obj.magic (Eapp1 ((Obj.magic v0), lv0)) in
                           let x4 = Obj.magic ft1 in
                           let Pair (s4, _) =
                             let f2 = Obj.magic (Eapp0 (ft1, lv0)) in
                             let Pair (s4, _) = Obj.magic s in
                             Pair
                             ((let Pair (s5, s6) = s4 in
                               Pair
                               ((let Pair (s7, s8) = s5 in
                                 Pair
                                 ((let Pair (s9, s10) = s7 in
                                   Pair (s9,
                                   (match Obj.magic f2 with
                                    | Ffun3 (v, f3, l) -> update_inFun s10 v f3 l (Obj.magic v0)
                                    | Efun0 e0 -> update_funDef1 s10 (Obj.magic v0) e0
                                    | Efun1 l -> update_funDef2 s10 l (Obj.magic v0)
                                    | _ -> s10))), s8)),
                               (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 v0 s6))), __)
                           in
                           Pair
                           ((let Pair (s5, s6) = s4 in
                             Pair
                             ((let Pair (s7, s8) = s5 in
                               Pair
                               ((let Pair (s9, s10) = s7 in
                                 Pair (s9,
                                 (match Obj.magic f1 with
                                  | Ffun3 (v, f2, l) -> update_inFun s10 v f2 l (Obj.magic x4)
                                  | Efun0 e0 -> update_funDef1 s10 (Obj.magic x4) e0
                                  | Efun1 l -> update_funDef2 s10 l (Obj.magic x4)
                                  | _ -> s10))), s8)),
                             (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f1 x4
                               (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                                 (Obj.magic (Eapp0 (ft1, lv0))) v0 s6)))), __)
                         in
                         Pair
                         ((let Pair (s5, s6) = s4 in
                           Pair
                           ((let Pair (s7, s8) = s5 in
                             Pair
                             ((let Pair (s9, s10) = s7 in
                               Pair (s9,
                               (match Obj.magic f0 with
                                | Ffun3 (v, f1, l) -> update_inFun s10 v f1 l (Obj.magic x3)
                                | Efun0 e0 -> update_funDef1 s10 (Obj.magic x3) e0
                                | Efun1 l -> update_funDef2 s10 l (Obj.magic x3)
                                | _ -> s10))), s8)),
                           (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x3
                             (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                               (Obj.magic (Eapp1 ((Obj.magic v0), lv0))) (Obj.magic ft1) s6)))), __)
                       in
                       Pair
                       ((let Pair (s5, s6) = s4 in
                         Pair ((let Pair (s7, s8) = s5 in Pair ((let Pair (s9, s10) = s7 in Pair (s9, s10)), s8)),
                         (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                           (Obj.magic (Eapp2 ((Obj.magic v0), ft1))) (Obj.magic lv0) s6))), __)) })
               | False ->
                 let v0 = Obj.magic f in
                 let ft1 = Obj.magic ft in
                 let lv0 = Obj.magic xs in
                 Obj.magic { resTree = (Obj.magic (Eapp ((Obj.magic v0), ft1, lv0))); resState =
                   (let Pair (s4, _) =
                      let f0 = Obj.magic (Eapp2 ((Obj.magic v0), ft1)) in
                      let x3 = Obj.magic lv0 in
                      let Pair (s4, _) =
                        let f1 = Obj.magic (Eapp1 ((Obj.magic v0), lv0)) in
                        let x4 = Obj.magic ft1 in
                        let Pair (s4, _) =
                          let f2 = Obj.magic (Eapp0 (ft1, lv0)) in
                          let Pair (s4, _) = Obj.magic s in
                          Pair
                          ((let Pair (s5, s6) = s4 in
                            Pair
                            ((let Pair (s7, s8) = s5 in
                              Pair
                              ((let Pair (s9, s10) = s7 in
                                Pair (s9,
                                (match Obj.magic f2 with
                                 | Ffun3 (v, f3, l) -> update_inFun s10 v f3 l (Obj.magic v0)
                                 | Efun0 e0 -> update_funDef1 s10 (Obj.magic v0) e0
                                 | Efun1 l -> update_funDef2 s10 l (Obj.magic v0)
                                 | _ -> s10))), s8)),
                            (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 v0 s6))), __)
                        in
                        Pair
                        ((let Pair (s5, s6) = s4 in
                          Pair
                          ((let Pair (s7, s8) = s5 in
                            Pair
                            ((let Pair (s9, s10) = s7 in
                              Pair (s9,
                              (match Obj.magic f1 with
                               | Ffun3 (v, f2, l) -> update_inFun s10 v f2 l (Obj.magic x4)
                               | Efun0 e0 -> update_funDef1 s10 (Obj.magic x4) e0
                               | Efun1 l -> update_funDef2 s10 l (Obj.magic x4)
                               | _ -> s10))), s8)),
                          (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f1 x4
                            (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c
                              (Obj.magic (Eapp0 (ft1, lv0))) v0 s6)))), __)
                      in
                      Pair
                      ((let Pair (s5, s6) = s4 in
                        Pair
                        ((let Pair (s7, s8) = s5 in
                          Pair
                          ((let Pair (s9, s10) = s7 in
                            Pair (s9,
                            (match Obj.magic f0 with
                             | Ffun3 (v, f1, l) -> update_inFun s10 v f1 l (Obj.magic x3)
                             | Efun0 e0 -> update_funDef1 s10 (Obj.magic x3) e0
                             | Efun1 l -> update_funDef2 s10 l (Obj.magic x3)
                             | _ -> s10))), s8)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x3
                          (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                            (Obj.magic (Eapp1 ((Obj.magic v0), lv0))) (Obj.magic ft1) s6)))), __)
                    in
                    Pair
                    ((let Pair (s5, s6) = s4 in
                      Pair ((let Pair (s7, s8) = s5 in Pair ((let Pair (s9, s10) = s7 in Pair (s9, s10)), s8)),
                      (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                        (Obj.magic (Eapp2 ((Obj.magic v0), ft1))) (Obj.magic lv0) s6))), __)) })
            | None ->
              let v0 = Obj.magic f in
              let ft0 = Obj.magic ft in
              let lv0 = Obj.magic xs in
              Obj.magic { resTree = (Obj.magic (Eapp ((Obj.magic v0), ft0, lv0))); resState =
                (let Pair (s4, _) =
                   let f0 = Obj.magic (Eapp2 ((Obj.magic v0), ft0)) in
                   let x2 = Obj.magic lv0 in
                   let Pair (s4, _) =
                     let f1 = Obj.magic (Eapp1 ((Obj.magic v0), lv0)) in
                     let x3 = Obj.magic ft0 in
                     let Pair (s4, _) =
                       let f2 = Obj.magic (Eapp0 (ft0, lv0)) in
                       let Pair (s4, _) = Obj.magic s in
                       Pair
                       ((let Pair (s5, s6) = s4 in
                         Pair
                         ((let Pair (s7, s8) = s5 in
                           Pair
                           ((let Pair (s9, s10) = s7 in
                             Pair (s9,
                             (match Obj.magic f2 with
                              | Ffun3 (v, f3, l) -> update_inFun s10 v f3 l (Obj.magic v0)
                              | Efun0 e0 -> update_funDef1 s10 (Obj.magic v0) e0
                              | Efun1 l -> update_funDef2 s10 l (Obj.magic v0)
                              | _ -> s10))), s8)),
                         (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 v0 s6))), __)
                     in
                     Pair
                     ((let Pair (s5, s6) = s4 in
                       Pair
                       ((let Pair (s7, s8) = s5 in
                         Pair
                         ((let Pair (s9, s10) = s7 in
                           Pair (s9,
                           (match Obj.magic f1 with
                            | Ffun3 (v, f2, l) -> update_inFun s10 v f2 l (Obj.magic x3)
                            | Efun0 e0 -> update_funDef1 s10 (Obj.magic x3) e0
                            | Efun1 l -> update_funDef2 s10 l (Obj.magic x3)
                            | _ -> s10))), s8)),
                       (preserves_S_S_fns.preserve_S_dn Exp_univ_fun_tag Exp_univ_exp c f1 x3
                         (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic (Eapp0 (ft0, lv0)))
                           v0 s6)))), __)
                   in
                   Pair
                   ((let Pair (s5, s6) = s4 in
                     Pair
                     ((let Pair (s7, s8) = s5 in
                       Pair
                       ((let Pair (s9, s10) = s7 in
                         Pair (s9,
                         (match Obj.magic f0 with
                          | Ffun3 (v, f1, l) -> update_inFun s10 v f1 l (Obj.magic x2)
                          | Efun0 e0 -> update_funDef1 s10 (Obj.magic x2) e0
                          | Efun1 l -> update_funDef2 s10 l (Obj.magic x2)
                          | _ -> s10))), s8)),
                     (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x2
                       (preserves_S_S_fns.preserve_S_up Exp_univ_fun_tag Exp_univ_exp c
                         (Obj.magic (Eapp1 ((Obj.magic v0), lv0))) (Obj.magic ft0) s6)))), __)
                 in
                 Pair
                 ((let Pair (s5, s6) = s4 in
                   Pair ((let Pair (s7, s8) = s5 in Pair ((let Pair (s9, s10) = s7 in Pair (s9, s10)), s8)),
                   (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                     (Obj.magic (Eapp2 ((Obj.magic v0), ft0))) (Obj.magic lv0) s6))), __)) })
         | Eprim (x0, p, ys, u) ->
           let { resTree = x2; resState = s0 } =
             Obj.magic rw_inline (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eprim3 (x0, p, ys))), c)) u Tt r
               (let f = Obj.magic (Eprim3 (x0, p, ys)) in
                let x1 = Obj.magic u in
                let Pair (s1, _) =
                  let f0 = Obj.magic (Eprim2 (x0, p, u)) in
                  let x2 = Obj.magic ys in
                  let Pair (s1, _) =
                    let f1 = Obj.magic (Eprim1 (x0, ys, u)) in
                    let x3 = Obj.magic p in
                    let Pair (s1, _) =
                      let f2 = Obj.magic (Eprim0 (p, ys, u)) in
                      let x4 = Obj.magic x0 in
                      let Pair (s1, _) = s in
                      Pair
                      ((let Pair (s2, s3) = s1 in
                        Pair
                        ((let Pair (s4, s5) = s2 in
                          Pair
                          ((let Pair (s6, s7) = s4 in
                            Pair (s6,
                            (match Obj.magic f2 with
                             | Ffun3 (v, f3, l) -> update_inFun s7 v f3 l (Obj.magic x4)
                             | Efun0 e0 -> update_funDef1 s7 (Obj.magic x4) e0
                             | Efun1 l -> update_funDef2 s7 l (Obj.magic x4)
                             | _ -> s7))), s5)),
                        (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f2 x4 s3))), __)
                    in
                    Pair
                    ((let Pair (s2, s3) = s1 in
                      Pair
                      ((let Pair (s4, s5) = s2 in
                        Pair
                        ((let Pair (s6, s7) = s4 in
                          Pair (s6,
                          (match Obj.magic f1 with
                           | Ffun3 (v, f2, l) -> update_inFun s7 v f2 l (Obj.magic x3)
                           | Efun0 e0 -> update_funDef1 s7 (Obj.magic x3) e0
                           | Efun1 l -> update_funDef2 s7 l (Obj.magic x3)
                           | _ -> s7))), s5)),
                      (preserves_S_S_fns.preserve_S_dn Exp_univ_prim Exp_univ_exp c f1 x3
                        (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic (Eprim0 (p, ys, u)))
                          (Obj.magic x0) s3)))), __)
                  in
                  Pair
                  ((let Pair (s2, s3) = s1 in
                    Pair
                    ((let Pair (s4, s5) = s2 in
                      Pair
                      ((let Pair (s6, s7) = s4 in
                        Pair (s6,
                        (match Obj.magic f0 with
                         | Ffun3 (v, f1, l) -> update_inFun s7 v f1 l (Obj.magic x2)
                         | Efun0 e0 -> update_funDef1 s7 (Obj.magic x2) e0
                         | Efun1 l -> update_funDef2 s7 l (Obj.magic x2)
                         | _ -> s7))), s5)),
                    (preserves_S_S_fns.preserve_S_dn Exp_univ_list_var Exp_univ_exp c f0 x2
                      (preserves_S_S_fns.preserve_S_up Exp_univ_prim Exp_univ_exp c (Obj.magic (Eprim1 (x0, ys, u)))
                        (Obj.magic p) s3)))), __)
                in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic x1)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic x1) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic x1)
                       | _ -> s7))), s5)),
                  (preserves_S_S_fns.preserve_S_dn Exp_univ_exp Exp_univ_exp c f x1
                    (preserves_S_S_fns.preserve_S_up Exp_univ_list_var Exp_univ_exp c
                      (Obj.magic (Eprim2 (x0, p, u))) (Obj.magic ys) s3)))), __))
           in
           { resTree = (Obj.magic (Eprim (x0, p, ys, (Obj.magic x2)))); resState =
           (let Pair (s1, _) = s0 in
            Pair
            ((let Pair (s2, s3) = s1 in
              Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
              (preserves_S_S_fns.preserve_S_up Exp_univ_exp Exp_univ_exp c (Obj.magic (Eprim3 (x0, p, ys))) x2 s3))),
            __)) }
         | Ehalt x0 ->
           let v0 = Obj.magic x0 in
           Obj.magic { resTree = (Obj.magic (Ehalt (Obj.magic v0))); resState =
             (let Pair (s1, _) =
                let f = Obj.magic Ehalt0 in
                let Pair (s1, _) = Obj.magic s in
                Pair
                ((let Pair (s2, s3) = s1 in
                  Pair
                  ((let Pair (s4, s5) = s2 in
                    Pair
                    ((let Pair (s6, s7) = s4 in
                      Pair (s6,
                      (match Obj.magic f with
                       | Ffun3 (v, f0, l) -> update_inFun s7 v f0 l (Obj.magic v0)
                       | Efun0 e0 -> update_funDef1 s7 (Obj.magic v0) e0
                       | Efun1 l -> update_funDef2 s7 l (Obj.magic v0)
                       | _ -> s7))), s5)), (preserves_S_S_fns.preserve_S_dn Exp_univ_var Exp_univ_exp c f v0 s3))),
                __)
              in
              Pair
              ((let Pair (s2, s3) = s1 in
                Pair ((let Pair (s4, s5) = s2 in Pair ((let Pair (s6, s7) = s4 in Pair (s6, s7)), s5)),
                (preserves_S_S_fns.preserve_S_up Exp_univ_var Exp_univ_exp c (Obj.magic Ehalt0) v0 s3))), __)) }
       in
       { resTree = e'; resState = s' }
     | _ -> { resTree = e; resState = s })
  | XH -> { resTree = e; resState = s }
