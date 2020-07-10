type __ = Obj.t

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
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
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

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)

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

module N =
 struct
  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' -> (match Coq_Pos.sub_mask n' m' with
                     | Coq_Pos.IsPos p -> Npos p
                     | _ -> N0))
 end

module Coq__1 = struct
 (** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)
 let rec map f = function
 | Nil -> Nil
 | Cons (a, t0) -> Cons ((f a), (map f t0))
end
include Coq__1

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

(** val peq : positive -> positive -> sumbool **)

let peq =
  Coq_Pos.eq_dec

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some y -> Some (f y)
| None -> None

(** val nthN : 'a1 list -> n -> 'a1 option **)

let rec nthN al n0 =
  match al with
  | Nil -> None
  | Cons (a, al') -> (match n0 with
                      | N0 -> Some a
                      | Npos _ -> nthN al' (N.sub n0 (Npos XH)))

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

module Coq_M = PTree

type var = Coq_M.elt

type fun_tag = Coq_M.elt

type ctor_tag = Coq_M.elt

(** val apply_r : Coq_M.elt Coq_M.t -> positive -> Coq_M.elt **)

let apply_r sigma y =
  match Coq_M.get y sigma with
  | Some v -> v
  | None -> y

type 'u univD = __

type 'u frame_t = __

type ('u, 'f) frames_t' =
| Frames_nil of 'u
| Frames_cons of 'u * 'u * 'u * 'f * ('u, 'f) frames_t'

type 'u frames_t = ('u, 'u frame_t) frames_t'

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

(** val un_fun_tag : fun_tag0 -> positive **)

let un_fun_tag pat =
  pat

(** val un_ctor_tag : ctor_tag0 -> positive **)

let un_ctor_tag pat =
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

type ('a, 'b) iso = { isoAofB : ('b -> 'a); isoBofA : ('a -> 'b) }

(** val iso_var : (var0, var) iso **)

let iso_var =
  { isoAofB = (fun x -> x); isoBofA = un_var }

(** val iso_fun_tag : (fun_tag0, fun_tag) iso **)

let iso_fun_tag =
  { isoAofB = (fun x -> x); isoBofA = un_fun_tag }

(** val iso_ctor_tag : (ctor_tag0, ctor_tag) iso **)

let iso_ctor_tag =
  { isoAofB = (fun x -> x); isoBofA = un_ctor_tag }

type r_map = var M.tree

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

type ctx_map = (ctor_tag0, var0 list) prod Coq0_M.tree

type r_ctors = ctx_map

type c_map = positive Coq0_M.tree

(** val census_var : (positive option -> positive option) -> r_map -> var0 -> c_map -> c_map **)

let census_var upd _UU03c3_ x _UU03b4_ =
  let x0 = iso_var.isoBofA (apply_r' _UU03c3_ x) in
  (match upd (Coq0_M.get x0 _UU03b4_) with
   | Some n0 -> Coq0_M.set x0 n0 _UU03b4_
   | None -> Coq0_M.remove x0 _UU03b4_)

(** val census_list : ('a1 -> c_map -> c_map) -> 'a1 list -> c_map -> c_map **)

let census_list census xs _UU03b4_ =
  fold_right census _UU03b4_ xs

(** val census_vars : (positive option -> positive option) -> r_map -> var0 list -> c_map -> c_map **)

let census_vars upd _UU03c3_ =
  census_list (census_var upd _UU03c3_)

(** val census_ces' : (exp -> c_map -> c_map) -> (ctor_tag0, exp) prod list -> c_map -> c_map **)

let census_ces' census_exp0 =
  census_list (fun pat _UU03b4_ -> let Pair (_, e) = pat in census_exp0 e _UU03b4_)

(** val census_fds' : (exp -> c_map -> c_map) -> fundef list -> c_map -> c_map **)

let census_fds' census_exp0 =
  census_list (fun pat _UU03b4_ -> let Ffun (_, _, _, e) = pat in census_exp0 e _UU03b4_)

(** val census_exp : (positive option -> positive option) -> r_map -> exp -> c_map -> c_map **)

let rec census_exp upd _UU03c3_ e _UU03b4_ =
  match e with
  | Econstr (_, _, ys, e0) -> census_vars upd _UU03c3_ ys (census_exp upd _UU03c3_ e0 _UU03b4_)
  | Ecase (x, ces) -> census_var upd _UU03c3_ x (census_ces' (census_exp upd _UU03c3_) ces _UU03b4_)
  | Eproj (_, _, _, y, e0) -> census_var upd _UU03c3_ y (census_exp upd _UU03c3_ e0 _UU03b4_)
  | Eletapp (_, f, _, ys, e0) ->
    census_var upd _UU03c3_ f (census_vars upd _UU03c3_ ys (census_exp upd _UU03c3_ e0 _UU03b4_))
  | Efun (fds, e0) -> census_fds' (census_exp upd _UU03c3_) fds (census_exp upd _UU03c3_ e0 _UU03b4_)
  | Eapp (f, _, xs) -> census_var upd _UU03c3_ f (census_vars upd _UU03c3_ xs _UU03b4_)
  | Eprim (_, _, ys, e0) -> census_vars upd _UU03c3_ ys (census_exp upd _UU03c3_ e0 _UU03b4_)
  | Ehalt x -> census_var upd _UU03c3_ x _UU03b4_

(** val census_ces :
    (positive option -> positive option) -> r_map -> (ctor_tag0, exp) prod list -> c_map -> c_map **)

let census_ces upd _UU03c3_ =
  census_ces' (census_exp upd _UU03c3_)

(** val pred_upd : positive option -> positive option **)

let pred_upd = function
| Some n1 -> (match n1 with
              | XH -> None
              | _ -> Some (Coq_Pos.pred n1))
| None -> None

type s_shrink = c_map

type r_shrink = r_ctors

type d_rename = r_map

(** val rename : exp_univ -> r_map -> exp_univ univD -> exp_univ univD **)

let rename a _UU03c3_ pat =
  match a with
  | Exp_univ_prod_ctor_tag_exp -> let Pair (c, e) = Obj.magic pat in Obj.magic (Pair (c, (rename_all' _UU03c3_ e)))
  | Exp_univ_list_prod_ctor_tag_exp ->
    Obj.magic map (fun pat0 -> let Pair (c, e) = pat0 in Pair (c, (rename_all' _UU03c3_ e))) pat
  | Exp_univ_fundef ->
    let Ffun (f, ft, xs, e) = Obj.magic pat in Obj.magic (Ffun (f, ft, xs, (rename_all' _UU03c3_ e)))
  | Exp_univ_list_fundef ->
    Obj.magic map (fun pat0 -> let Ffun (f, ft, xs, e) = pat0 in Ffun (f, ft, xs, (rename_all' _UU03c3_ e))) pat
  | Exp_univ_exp -> Obj.magic rename_all' _UU03c3_ pat
  | Exp_univ_var -> Obj.magic apply_r' _UU03c3_ pat
  | Exp_univ_list_var -> Obj.magic apply_r_list' _UU03c3_ pat
  | _ -> pat

(** val find_case : ctor_tag0 -> (ctor_tag0, exp) prod list -> exp option **)

let rec find_case c = function
| Nil -> None
| Cons (p, ces0) ->
  let Pair (c', e) = p in
  (match Coq_Pos.eqb (iso_ctor_tag.isoBofA c) (iso_ctor_tag.isoBofA c') with
   | True -> Some e
   | False -> find_case c ces0)

(** val census_case_pred : r_map -> ctor_tag0 -> (ctor_tag0, exp) prod list -> c_map -> c_map **)

let rec census_case_pred _UU03c3_ c ces _UU03b4_ =
  match ces with
  | Nil -> _UU03b4_
  | Cons (p, ces0) ->
    let Pair (c', e) = p in
    (match Coq_Pos.eqb (iso_ctor_tag.isoBofA c) (iso_ctor_tag.isoBofA c') with
     | True -> census_ces pred_upd _UU03c3_ ces0 _UU03b4_
     | False -> census_case_pred _UU03c3_ c ces0 (census_exp pred_upd _UU03c3_ e _UU03b4_))

(** val census_subst : var0 -> var0 -> c_map -> positive Coq0_M.t **)

let census_subst y x _UU03b4_ =
  let x0 = iso_var.isoBofA x in
  let y0 = iso_var.isoBofA y in
  (match Coq0_M.get x0 _UU03b4_ with
   | Some n0 ->
     (match Coq0_M.get y0 _UU03b4_ with
      | Some m -> Coq0_M.set y0 (Coq_Pos.add n0 m) (Coq0_M.remove x0 _UU03b4_)
      | None -> Coq0_M.set y0 n0 (Coq0_M.remove x0 _UU03b4_))
   | None -> _UU03b4_)

(** val rw_shrink : (exp_univ, d_rename, r_shrink, s_shrink) rewriter **)

let rec rw_shrink x a c e d r s =
  match x with
  | XI _ ->
    (match a with
     | Exp_univ_prod_ctor_tag_exp ->
       let Pair (c0, e0) = Obj.magic e in
       let { resTree = x0; resState = s0 } =
         rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_prod_ctor_tag_exp,
           Exp_univ_exp, (Obj.magic (Pair_ctor_tag_exp1 c0)), c)) e0 d r s
       in
       { resTree = (Obj.magic (Pair (c0, x0))); resState = s0 }
     | Exp_univ_list_prod_ctor_tag_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (p, u) ->
           let lpcte = Obj.magic u in
           let d1 = Obj.magic d in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_prod_ctor_tag_exp (Frames_cons (Exp_univ_prod_ctor_tag_exp,
               Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp0 (Obj.magic rename Exp_univ_list_prod_ctor_tag_exp d1 lpcte))),
               c)) (Obj.magic p) (Obj.magic d) r_C (Obj.magic s)
           in
           let { resTree = x1; resState = s1 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))), c)) lpcte d1 r_C s0
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState = s1 }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_fundef ->
       let { resTree = e'; resState = s' } =
         let Ffun (f, ft, xs, e0) = Obj.magic e in
         let v0 = Obj.magic f in
         let ft0 = Obj.magic iso_fun_tag.isoAofB ft in
         let lv0 = Obj.magic xs in
         let { resTree = x2; resState = s0 } =
           rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_fundef, Exp_univ_exp,
             (Obj.magic (Ffun3 (v0, ft0, lv0))), c)) (Obj.magic e0) (Obj.magic d) (Obj.magic r) (Obj.magic s)
         in
         Obj.magic { resTree = (Obj.magic (Ffun (v0, ft0, lv0, (Obj.magic x2)))); resState = s0 }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_list_fundef ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (f, u) ->
           let lf = Obj.magic u in
           let d1 = Obj.magic d in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
               Exp_univ_exp, (Obj.magic (Cons_fundef0 (Obj.magic rename Exp_univ_list_fundef d1 lf))), c))
               (Obj.magic f) (Obj.magic d) r_C (Obj.magic s)
           in
           let { resTree = x1; resState = s1 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
               Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf d1 r_C s0
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState = s1 }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Econstr (x0, c0, ys, u) ->
           (match Coq0_M.get x0 s with
            | Some _ ->
              let v0 = Obj.magic x0 in
              let ct0 = Obj.magic c0 in
              let lv0 = Obj.magic apply_r_list' d ys in
              let { resTree = x2; resState = s0 } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
                  (Obj.magic (Econstr3 (v0, ct0, lv0))), c)) (Obj.magic u) (Obj.magic d)
                  (Coq0_M.set v0 (Pair (ct0, lv0)) (Obj.magic r)) (Obj.magic s)
              in
              Obj.magic { resTree = (Obj.magic (Econstr (v0, ct0, lv0, (Obj.magic x2)))); resState = s0 }
            | None ->
              let { resTree = x'; resState = s' } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic d) (Obj.magic r)
                  (Obj.magic census_vars pred_upd d ys s)
              in
              Obj.magic { resTree = x'; resState = s' })
         | Ecase (x0, ces) ->
           (match Coq0_M.get (apply_r' d x0) r with
            | Some p ->
              let Pair (c0, _) = p in
              (match find_case c0 ces with
               | Some e0 ->
                 let { resTree = x'; resState = s' } =
                   rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic e0) (Obj.magic d) (Obj.magic r)
                     (Obj.magic census_case_pred d c0 ces (census_var pred_upd d x0 s))
                 in
                 Obj.magic { resTree = x'; resState = s' }
               | None ->
                 let v0 = Obj.magic apply_r' d x0 in
                 let { resTree = x1; resState = s0 } =
                   rw_shrink (Coq_Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
                     (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase1 v0)), c))
                     (Obj.magic ces) (Obj.magic d) (Obj.magic r) (Obj.magic s)
                 in
                 Obj.magic { resTree = (Obj.magic (Ecase (v0, (Obj.magic x1)))); resState = s0 })
            | None ->
              let v0 = Obj.magic apply_r' d x0 in
              let { resTree = x1; resState = s0 } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
                  (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase1 v0)), c))
                  (Obj.magic ces) (Obj.magic d) (Obj.magic r) (Obj.magic s)
              in
              Obj.magic { resTree = (Obj.magic (Ecase (v0, (Obj.magic x1)))); resState = s0 })
         | Eproj (x0, c0, n0, y, u) ->
           (match Coq0_M.get x0 s with
            | Some _ ->
              (match Coq0_M.get (apply_r' d y) r with
               | Some p ->
                 let Pair (_, ys) = p in
                 (match nthN ys n0 with
                  | Some y' ->
                    let { resTree = x'; resState = s' } =
                      rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic Coq0_M.set x0 y' d)
                        (Obj.magic r) (Obj.magic census_var pred_upd d y (census_subst y' x0 s))
                    in
                    Obj.magic { resTree = x'; resState = s' }
                  | None ->
                    let v0 = Obj.magic x0 in
                    let ct0 = Obj.magic c0 in
                    let n1 = Obj.magic n0 in
                    let v2 = Obj.magic apply_r' d y in
                    let { resTree = x3; resState = s0 } =
                      rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp,
                        Exp_univ_exp, (Obj.magic (Eproj4 (v0, ct0, n1, v2))), c)) (Obj.magic u) (Obj.magic d)
                        (Obj.magic r) (Obj.magic s)
                    in
                    Obj.magic { resTree = (Obj.magic (Eproj (v0, ct0, n1, v2, (Obj.magic x3)))); resState = s0 })
               | None ->
                 let v0 = Obj.magic x0 in
                 let ct0 = Obj.magic c0 in
                 let n1 = Obj.magic n0 in
                 let v2 = Obj.magic apply_r' d y in
                 let { resTree = x3; resState = s0 } =
                   rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
                     (Obj.magic (Eproj4 (v0, ct0, n1, v2))), c)) (Obj.magic u) (Obj.magic d) (Obj.magic r)
                     (Obj.magic s)
                 in
                 Obj.magic { resTree = (Obj.magic (Eproj (v0, ct0, n1, v2, (Obj.magic x3)))); resState = s0 })
            | None ->
              let { resTree = x'; resState = s' } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic d) (Obj.magic r)
                  (Obj.magic census_var pred_upd d y s)
              in
              Obj.magic { resTree = x'; resState = s' })
         | Eletapp (x0, f, ft, ys, u) ->
           let v0 = Obj.magic x0 in
           let v2 = Obj.magic apply_r' d f in
           let ft0 = Obj.magic ft in
           let lv0 = Obj.magic apply_r_list' d ys in
           let { resTree = x3; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eletapp4 (v0, v2, ft0, lv0))), c)) (Obj.magic u) (Obj.magic d) (Obj.magic r) (Obj.magic s)
           in
           Obj.magic { resTree = (Obj.magic (Eletapp (v0, v2, ft0, lv0, (Obj.magic x3)))); resState = s0 }
         | Efun (fds, u) ->
           let e0 = Obj.magic u in
           let d1 = Obj.magic d in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef, Exp_univ_exp,
               Exp_univ_exp, (Obj.magic (Efun0 (Obj.magic rename Exp_univ_exp d1 e0))), c)) (Obj.magic fds)
               (Obj.magic d) r_C (Obj.magic s)
           in
           let { resTree = x1; resState = s1 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Efun1 (Obj.magic x0))), c)) e0 d1 r_C s0
           in
           Obj.magic { resTree = (Obj.magic (Efun ((Obj.magic x0), (Obj.magic x1)))); resState = s1 }
         | Eapp (f, ft, xs) ->
           Obj.magic { resTree =
             (Obj.magic (Eapp ((Obj.magic apply_r' d f), (Obj.magic ft), (Obj.magic apply_r_list' d xs))));
             resState = (Obj.magic s) }
         | Eprim (x0, p, ys, u) ->
           (match Coq0_M.get x0 s with
            | Some _ ->
              let v0 = Obj.magic x0 in
              let p0 = Obj.magic p in
              let lv0 = Obj.magic apply_r_list' d ys in
              let { resTree = x2; resState = s0 } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
                  (Obj.magic (Eprim3 (v0, p0, lv0))), c)) (Obj.magic u) (Obj.magic d) (Obj.magic r) (Obj.magic s)
              in
              Obj.magic { resTree = (Obj.magic (Eprim (v0, p0, lv0, (Obj.magic x2)))); resState = s0 }
            | None ->
              let { resTree = x'; resState = s' } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic d) (Obj.magic r)
                  (Obj.magic census_vars pred_upd d ys s)
              in
              Obj.magic { resTree = x'; resState = s' })
         | Ehalt x0 ->
           Obj.magic { resTree = (Obj.magic (Ehalt (Obj.magic apply_r' d x0))); resState = (Obj.magic s) }
       in
       let { resTree = e''; resState = s'' } =
         match Obj.magic e' with
         | Econstr (x0, _, ys, u) ->
           (match Coq0_M.get x0 s' with
            | Some _ -> { resTree = e'; resState = s' }
            | None ->
              Obj.magic { resTree = (Obj.magic u); resState = (Obj.magic census_vars pred_upd Coq0_M.empty ys s') })
         | Ecase (_, _) -> { resTree = e'; resState = s' }
         | Eproj (x0, _, _, y, u) ->
           (match Coq0_M.get x0 s' with
            | Some _ -> { resTree = e'; resState = s' }
            | None ->
              Obj.magic { resTree = (Obj.magic u); resState = (Obj.magic census_var pred_upd Coq0_M.empty y s') })
         | Eletapp (_, _, _, _, _) -> { resTree = e'; resState = s' }
         | Efun (_, _) -> { resTree = e'; resState = s' }
         | Eapp (_, _, _) -> { resTree = e'; resState = s' }
         | Eprim (x0, _, ys, u) ->
           (match Coq0_M.get x0 s' with
            | Some _ -> { resTree = e'; resState = s' }
            | None ->
              Obj.magic { resTree = (Obj.magic u); resState = (Obj.magic census_vars pred_upd Coq0_M.empty ys s') })
         | Ehalt _ -> { resTree = e'; resState = s' }
       in
       { resTree = e''; resState = s'' }
     | x0 -> { resTree = (rename x0 d e); resState = s })
  | XO _ ->
    (match a with
     | Exp_univ_prod_ctor_tag_exp ->
       let Pair (c0, e0) = Obj.magic e in
       let { resTree = x0; resState = s0 } =
         rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_prod_ctor_tag_exp,
           Exp_univ_exp, (Obj.magic (Pair_ctor_tag_exp1 c0)), c)) e0 d r s
       in
       { resTree = (Obj.magic (Pair (c0, x0))); resState = s0 }
     | Exp_univ_list_prod_ctor_tag_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (p, u) ->
           let lpcte = Obj.magic u in
           let d1 = Obj.magic d in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_prod_ctor_tag_exp (Frames_cons (Exp_univ_prod_ctor_tag_exp,
               Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp0 (Obj.magic rename Exp_univ_list_prod_ctor_tag_exp d1 lpcte))),
               c)) (Obj.magic p) (Obj.magic d) r_C (Obj.magic s)
           in
           let { resTree = x1; resState = s1 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))), c)) lpcte d1 r_C s0
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState = s1 }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_fundef ->
       let { resTree = e'; resState = s' } =
         let Ffun (f, ft, xs, e0) = Obj.magic e in
         let v0 = Obj.magic f in
         let ft0 = Obj.magic iso_fun_tag.isoAofB ft in
         let lv0 = Obj.magic xs in
         let { resTree = x2; resState = s0 } =
           rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_fundef, Exp_univ_exp,
             (Obj.magic (Ffun3 (v0, ft0, lv0))), c)) (Obj.magic e0) (Obj.magic d) (Obj.magic r) (Obj.magic s)
         in
         Obj.magic { resTree = (Obj.magic (Ffun (v0, ft0, lv0, (Obj.magic x2)))); resState = s0 }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_list_fundef ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s }
         | Cons (f, u) ->
           let lf = Obj.magic u in
           let d1 = Obj.magic d in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
               Exp_univ_exp, (Obj.magic (Cons_fundef0 (Obj.magic rename Exp_univ_list_fundef d1 lf))), c))
               (Obj.magic f) (Obj.magic d) r_C (Obj.magic s)
           in
           let { resTree = x1; resState = s1 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
               Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf d1 r_C s0
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState = s1 }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Econstr (x0, c0, ys, u) ->
           (match Coq0_M.get x0 s with
            | Some _ ->
              let v0 = Obj.magic x0 in
              let ct0 = Obj.magic c0 in
              let lv0 = Obj.magic apply_r_list' d ys in
              let { resTree = x2; resState = s0 } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
                  (Obj.magic (Econstr3 (v0, ct0, lv0))), c)) (Obj.magic u) (Obj.magic d)
                  (Coq0_M.set v0 (Pair (ct0, lv0)) (Obj.magic r)) (Obj.magic s)
              in
              Obj.magic { resTree = (Obj.magic (Econstr (v0, ct0, lv0, (Obj.magic x2)))); resState = s0 }
            | None ->
              let { resTree = x'; resState = s' } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic d) (Obj.magic r)
                  (Obj.magic census_vars pred_upd d ys s)
              in
              Obj.magic { resTree = x'; resState = s' })
         | Ecase (x0, ces) ->
           (match Coq0_M.get (apply_r' d x0) r with
            | Some p ->
              let Pair (c0, _) = p in
              (match find_case c0 ces with
               | Some e0 ->
                 let { resTree = x'; resState = s' } =
                   rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic e0) (Obj.magic d) (Obj.magic r)
                     (Obj.magic census_case_pred d c0 ces (census_var pred_upd d x0 s))
                 in
                 Obj.magic { resTree = x'; resState = s' }
               | None ->
                 let v0 = Obj.magic apply_r' d x0 in
                 let { resTree = x1; resState = s0 } =
                   rw_shrink (Coq_Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
                     (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase1 v0)), c))
                     (Obj.magic ces) (Obj.magic d) (Obj.magic r) (Obj.magic s)
                 in
                 Obj.magic { resTree = (Obj.magic (Ecase (v0, (Obj.magic x1)))); resState = s0 })
            | None ->
              let v0 = Obj.magic apply_r' d x0 in
              let { resTree = x1; resState = s0 } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
                  (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase1 v0)), c))
                  (Obj.magic ces) (Obj.magic d) (Obj.magic r) (Obj.magic s)
              in
              Obj.magic { resTree = (Obj.magic (Ecase (v0, (Obj.magic x1)))); resState = s0 })
         | Eproj (x0, c0, n0, y, u) ->
           (match Coq0_M.get x0 s with
            | Some _ ->
              (match Coq0_M.get (apply_r' d y) r with
               | Some p ->
                 let Pair (_, ys) = p in
                 (match nthN ys n0 with
                  | Some y' ->
                    let { resTree = x'; resState = s' } =
                      rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic Coq0_M.set x0 y' d)
                        (Obj.magic r) (Obj.magic census_var pred_upd d y (census_subst y' x0 s))
                    in
                    Obj.magic { resTree = x'; resState = s' }
                  | None ->
                    let v0 = Obj.magic x0 in
                    let ct0 = Obj.magic c0 in
                    let n1 = Obj.magic n0 in
                    let v2 = Obj.magic apply_r' d y in
                    let { resTree = x3; resState = s0 } =
                      rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp,
                        Exp_univ_exp, (Obj.magic (Eproj4 (v0, ct0, n1, v2))), c)) (Obj.magic u) (Obj.magic d)
                        (Obj.magic r) (Obj.magic s)
                    in
                    Obj.magic { resTree = (Obj.magic (Eproj (v0, ct0, n1, v2, (Obj.magic x3)))); resState = s0 })
               | None ->
                 let v0 = Obj.magic x0 in
                 let ct0 = Obj.magic c0 in
                 let n1 = Obj.magic n0 in
                 let v2 = Obj.magic apply_r' d y in
                 let { resTree = x3; resState = s0 } =
                   rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
                     (Obj.magic (Eproj4 (v0, ct0, n1, v2))), c)) (Obj.magic u) (Obj.magic d) (Obj.magic r)
                     (Obj.magic s)
                 in
                 Obj.magic { resTree = (Obj.magic (Eproj (v0, ct0, n1, v2, (Obj.magic x3)))); resState = s0 })
            | None ->
              let { resTree = x'; resState = s' } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic d) (Obj.magic r)
                  (Obj.magic census_var pred_upd d y s)
              in
              Obj.magic { resTree = x'; resState = s' })
         | Eletapp (x0, f, ft, ys, u) ->
           let v0 = Obj.magic x0 in
           let v2 = Obj.magic apply_r' d f in
           let ft0 = Obj.magic ft in
           let lv0 = Obj.magic apply_r_list' d ys in
           let { resTree = x3; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eletapp4 (v0, v2, ft0, lv0))), c)) (Obj.magic u) (Obj.magic d) (Obj.magic r) (Obj.magic s)
           in
           Obj.magic { resTree = (Obj.magic (Eletapp (v0, v2, ft0, lv0, (Obj.magic x3)))); resState = s0 }
         | Efun (fds, u) ->
           let e0 = Obj.magic u in
           let d1 = Obj.magic d in
           let r_C = Obj.magic r in
           let { resTree = x0; resState = s0 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef, Exp_univ_exp,
               Exp_univ_exp, (Obj.magic (Efun0 (Obj.magic rename Exp_univ_exp d1 e0))), c)) (Obj.magic fds)
               (Obj.magic d) r_C (Obj.magic s)
           in
           let { resTree = x1; resState = s1 } =
             rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Efun1 (Obj.magic x0))), c)) e0 d1 r_C s0
           in
           Obj.magic { resTree = (Obj.magic (Efun ((Obj.magic x0), (Obj.magic x1)))); resState = s1 }
         | Eapp (f, ft, xs) ->
           Obj.magic { resTree =
             (Obj.magic (Eapp ((Obj.magic apply_r' d f), (Obj.magic ft), (Obj.magic apply_r_list' d xs))));
             resState = (Obj.magic s) }
         | Eprim (x0, p, ys, u) ->
           (match Coq0_M.get x0 s with
            | Some _ ->
              let v0 = Obj.magic x0 in
              let p0 = Obj.magic p in
              let lv0 = Obj.magic apply_r_list' d ys in
              let { resTree = x2; resState = s0 } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
                  (Obj.magic (Eprim3 (v0, p0, lv0))), c)) (Obj.magic u) (Obj.magic d) (Obj.magic r) (Obj.magic s)
              in
              Obj.magic { resTree = (Obj.magic (Eprim (v0, p0, lv0, (Obj.magic x2)))); resState = s0 }
            | None ->
              let { resTree = x'; resState = s' } =
                rw_shrink (Coq_Pos.pred x) Exp_univ_exp c (Obj.magic u) (Obj.magic d) (Obj.magic r)
                  (Obj.magic census_vars pred_upd d ys s)
              in
              Obj.magic { resTree = x'; resState = s' })
         | Ehalt x0 ->
           Obj.magic { resTree = (Obj.magic (Ehalt (Obj.magic apply_r' d x0))); resState = (Obj.magic s) }
       in
       let { resTree = e''; resState = s'' } =
         match Obj.magic e' with
         | Econstr (x0, _, ys, u) ->
           (match Coq0_M.get x0 s' with
            | Some _ -> { resTree = e'; resState = s' }
            | None ->
              Obj.magic { resTree = (Obj.magic u); resState = (Obj.magic census_vars pred_upd Coq0_M.empty ys s') })
         | Ecase (_, _) -> { resTree = e'; resState = s' }
         | Eproj (x0, _, _, y, u) ->
           (match Coq0_M.get x0 s' with
            | Some _ -> { resTree = e'; resState = s' }
            | None ->
              Obj.magic { resTree = (Obj.magic u); resState = (Obj.magic census_var pred_upd Coq0_M.empty y s') })
         | Eletapp (_, _, _, _, _) -> { resTree = e'; resState = s' }
         | Efun (_, _) -> { resTree = e'; resState = s' }
         | Eapp (_, _, _) -> { resTree = e'; resState = s' }
         | Eprim (x0, _, ys, u) ->
           (match Coq0_M.get x0 s' with
            | Some _ -> { resTree = e'; resState = s' }
            | None ->
              Obj.magic { resTree = (Obj.magic u); resState = (Obj.magic census_vars pred_upd Coq0_M.empty ys s') })
         | Ehalt _ -> { resTree = e'; resState = s' }
       in
       { resTree = e''; resState = s'' }
     | x0 -> { resTree = (rename x0 d e); resState = s })
  | XH -> { resTree = (rename a d e); resState = s }
