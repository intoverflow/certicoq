type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val max : nat -> nat -> nat **)

let rec max n0 m =
  match n0 with
  | O -> m
  | S n' -> (match m with
             | O -> n0
             | S m' -> S (max n' m'))

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

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p -> (match y with
               | XI q -> compare_cont r p q
               | XO q -> compare_cont Gt p q
               | XH -> Gt)
    | XO p -> (match y with
               | XI q -> compare_cont Lt p q
               | XO q -> compare_cont r p q
               | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

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

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

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
  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')
 end

module Coq_N =
 struct
  (** val succ : n -> n **)

  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Pos.succ p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Pos.succ p

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p
 end

module Coq__2 = struct
 (** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)
 let rec map f = function
 | Nil -> Nil
 | Cons (a, t0) -> Cons ((f a), (map f t0))
end
include Coq__2

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

(** val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec combine l l' =
  match l with
  | Nil -> Nil
  | Cons (x, tl) -> (match l' with
                     | Nil -> Nil
                     | Cons (y, tl') -> Cons ((Pair (x, y)), (combine tl tl')))

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

type ident = string

type name =
| NAnon
| NNamed of ident

type 'm monad = { ret : (__ -> __ -> 'm); bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 monad -> 'a2 -> 'a1 **)

let ret monad0 x =
  Obj.magic monad0.ret __ x

(** val bind : 'a1 monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind monad0 x x0 =
  Obj.magic monad0.bind __ __ x x0

type 'm pMonad = { pret : (__ -> __ -> __ -> 'm); pbind : (__ -> __ -> __ -> 'm -> (__ -> 'm) -> 'm) }

type ('m, 'x) monP = __

(** val pbind : 'a1 pMonad -> ('a1, 'a3) monP -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let pbind pMonad0 pu x x0 =
  Obj.magic pMonad0.pbind __ __ pu x x0

(** val pMonad_Monad : 'a1 monad -> 'a1 pMonad **)

let pMonad_Monad m =
  { pret = (fun _ -> Obj.magic (fun _ x -> ret m x)); pbind = (fun _ _ -> Obj.magic (fun _ c f -> bind m c f)) }

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
    Coq__2.map fst (xelements m i Nil)

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

type 'u univD = __

type 'u frame_t = __

type ('u, 'f) frames_t' =
| Frames_nil of 'u
| Frames_cons of 'u * 'u * 'u * 'f * ('u, 'f) frames_t'

type 'u frames_t = ('u, 'u frame_t) frames_t'

type 'u trivial_delay_t = unit0

type ('u, 'r) r_plain = 'r

type ('u, 's) s_plain = 's

type ('u, 's1, 's2) s_prod = ('s1, 's2) prod

type ('u, 'st) result = { resTree : 'u univD; resState : 'st }

type ('u, 'r_C, 'st) rw_for = 'r_C -> 'st -> ('u, 'st) result

type fuel = positive

type ('u, 'd, 'r_C, 'st) rewriter = fuel -> 'u -> 'u frames_t -> 'u univD -> 'd -> ('u, 'r_C, 'st) rw_for

(** val fromN : n -> nat -> n list **)

let rec fromN n0 = function
| O -> Nil
| S m' -> Cons (n0, (fromN (Coq_N.succ n0) m'))

module M = PTree

module Coq_M = PTree

type 'x pM = 'x PTree.tree

type var = Coq_M.elt

type fun_tag = Coq_M.elt

type ind_tag = Coq_M.elt

type ctor_tag = Coq_M.elt

type prim = Coq_M.elt

type exp =
| Econstr of var * ctor_tag * var list * exp
| Ecase of var * (ctor_tag, exp) prod list
| Eproj of var * ctor_tag * n * var * exp
| Eletapp of var * var * fun_tag * var list * exp
| Efun of fundefs * exp
| Eapp of var * fun_tag * var list
| Eprim of var * prim * var list * exp
| Ehalt of var
and fundefs =
| Fcons of var * fun_tag * var list * exp * fundefs
| Fnil

type ctor_ty_info = { ctor_name : name; ctor_ind_name : name; ctor_ind_tag : ind_tag; ctor_arity : n;
                      ctor_ordinal : n }

type ctor_env = ctor_ty_info pM

type fun_ty_info = (n, n list) prod

type fun_env = fun_ty_info pM

type name_env = name M.tree

(** val add_entry : name_env -> var -> var -> string -> name_env **)

let add_entry nenv0 x x_origin suff =
  match M.get x_origin nenv0 with
  | Some n0 ->
    (match n0 with
     | NAnon ->
       M.set x (NNamed
         (append (String ((Ascii (True, False, False, False, False, True, True, False)), (String ((Ascii (False,
           True, True, True, False, True, True, False)), (String ((Ascii (True, True, True, True, False, True, True,
           False)), (String ((Ascii (False, True, True, True, False, True, True, False)), EmptyString)))))))) suff))
         nenv0
     | NNamed s0 -> M.set x (NNamed (append s0 suff)) nenv0)
  | None ->
    M.set x (NNamed
      (append (String ((Ascii (True, False, False, False, False, True, True, False)), (String ((Ascii (False, True,
        True, True, False, True, True, False)), (String ((Ascii (True, True, True, True, False, True, True, False)),
        (String ((Ascii (False, True, True, True, False, True, True, False)), EmptyString)))))))) suff)) nenv0

(** val eq_var : positive -> positive -> bool **)

let eq_var =
  Pos.eqb

(** val occurs_in_vars : var -> var list -> bool **)

let rec occurs_in_vars k = function
| Nil -> False
| Cons (x, xs1) -> (match eq_var k x with
                    | True -> True
                    | False -> occurs_in_vars k xs1)

(** val occurs_in_arms' : (var -> exp -> bool) -> var -> (ctor_tag, exp) prod list -> bool **)

let rec occurs_in_arms' occurs_in_exp0 k = function
| Nil -> False
| Cons (p, arms1) ->
  let Pair (_, e) = p in
  (match occurs_in_exp0 k e with
   | True -> True
   | False -> occurs_in_arms' occurs_in_exp0 k arms1)

(** val occurs_in_exp : var -> exp -> bool **)

let rec occurs_in_exp k = function
| Econstr (z, _, xs, e1) ->
  (match match eq_var z k with
         | True -> True
         | False -> occurs_in_vars k xs with
   | True -> True
   | False -> occurs_in_exp k e1)
| Ecase (x, arms) -> (match eq_var k x with
                      | True -> True
                      | False -> occurs_in_arms' occurs_in_exp k arms)
| Eproj (z, _, _, x, e1) ->
  (match match eq_var z k with
         | True -> True
         | False -> eq_var k x with
   | True -> True
   | False -> occurs_in_exp k e1)
| Eletapp (z, f, _, xs, e1) ->
  (match match match eq_var z k with
               | True -> True
               | False -> eq_var f k with
         | True -> True
         | False -> occurs_in_vars k xs with
   | True -> True
   | False -> occurs_in_exp k e1)
| Efun (fds, e0) -> (match occurs_in_fundefs k fds with
                     | True -> True
                     | False -> occurs_in_exp k e0)
| Eapp (x, _, xs) -> (match eq_var k x with
                      | True -> True
                      | False -> occurs_in_vars k xs)
| Eprim (z, _, xs, e1) ->
  (match match eq_var z k with
         | True -> True
         | False -> occurs_in_vars k xs with
   | True -> True
   | False -> occurs_in_exp k e1)
| Ehalt x -> eq_var x k

(** val occurs_in_fundefs : var -> fundefs -> bool **)

and occurs_in_fundefs k = function
| Fcons (z, _, zs, e, fds1) ->
  (match match match eq_var z k with
               | True -> True
               | False -> occurs_in_vars k zs with
         | True -> True
         | False -> occurs_in_exp k e with
   | True -> True
   | False -> occurs_in_fundefs k fds1)
| Fnil -> False

type var0 = positive
  (* singleton inductive, whose constructor was mk_var *)

type fun_tag0 = positive
  (* singleton inductive, whose constructor was mk_fun_tag *)

type ctor_tag0 = positive
  (* singleton inductive, whose constructor was mk_ctor_tag *)

type prim0 = positive
  (* singleton inductive, whose constructor was mk_prim *)

(** val un_var : var0 -> positive **)

let un_var pat =
  pat

type exp0 =
| Econstr0 of var0 * ctor_tag0 * var0 list * exp0
| Ecase0 of var0 * (ctor_tag0, exp0) prod list
| Eproj0 of var0 * ctor_tag0 * n * var0 * exp0
| Eletapp0 of var0 * var0 * fun_tag0 * var0 list * exp0
| Efun0 of fundef list * exp0
| Eapp0 of var0 * fun_tag0 * var0 list
| Eprim0 of var0 * prim0 * var0 list * exp0
| Ehalt0 of var0
and fundef =
| Ffun of var0 * fun_tag0 * var0 list * exp0

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
| Pair_ctor_tag_exp0 of exp0
| Pair_ctor_tag_exp1 of ctor_tag0
| Cons_prod_ctor_tag_exp0 of (ctor_tag0, exp0) prod list
| Cons_prod_ctor_tag_exp1 of (ctor_tag0, exp0) prod
| Ffun0 of fun_tag0 * var0 list * exp0
| Ffun1 of var0 * var0 list * exp0
| Ffun2 of var0 * fun_tag0 * exp0
| Ffun3 of var0 * fun_tag0 * var0 list
| Cons_fundef0 of fundef list
| Cons_fundef1 of fundef
| Econstr1 of ctor_tag0 * var0 list * exp0
| Econstr2 of var0 * var0 list * exp0
| Econstr3 of var0 * ctor_tag0 * exp0
| Econstr4 of var0 * ctor_tag0 * var0 list
| Ecase1 of (ctor_tag0, exp0) prod list
| Ecase2 of var0
| Eproj1 of ctor_tag0 * n * var0 * exp0
| Eproj2 of var0 * n * var0 * exp0
| Eproj3 of var0 * ctor_tag0 * var0 * exp0
| Eproj4 of var0 * ctor_tag0 * n * exp0
| Eproj5 of var0 * ctor_tag0 * n * var0
| Eletapp1 of var0 * fun_tag0 * var0 list * exp0
| Eletapp2 of var0 * fun_tag0 * var0 list * exp0
| Eletapp3 of var0 * var0 * var0 list * exp0
| Eletapp4 of var0 * var0 * fun_tag0 * exp0
| Eletapp5 of var0 * var0 * fun_tag0 * var0 list
| Efun1 of exp0
| Efun2 of fundef list
| Eapp1 of fun_tag0 * var0 list
| Eapp2 of var0 * var0 list
| Eapp3 of var0 * fun_tag0
| Eprim1 of prim0 * var0 list * exp0
| Eprim2 of var0 * var0 list * exp0
| Eprim3 of var0 * prim0 * exp0
| Eprim4 of var0 * prim0 * var0 list
| Ehalt1

module Coq0_M = Coq_M

(** val strip_vars : var0 list -> var list **)

let strip_vars =
  map (fun pat -> pat)

type fundefs0 = fundef list

(** val fundefs_of_proto' : (exp0 -> exp) -> fundef list -> fundefs **)

let fundefs_of_proto' exp_of_proto0 =
  fold_right (fun pat fds ->
    let Ffun (f0, ft0, xs, e) = pat in Fcons (f0, ft0, (strip_vars xs), (exp_of_proto0 e), fds)) Fnil

(** val ce_of_proto' : (exp0 -> exp) -> (ctor_tag0, exp0) prod -> (ctor_tag, exp) prod **)

let ce_of_proto' exp_of_proto0 = function
| Pair (c0, e) -> Pair (c0, (exp_of_proto0 e))

(** val ces_of_proto' : (exp0 -> exp) -> (ctor_tag0, exp0) prod list -> (ctor_tag, exp) prod list **)

let ces_of_proto' exp_of_proto0 =
  map (ce_of_proto' exp_of_proto0)

(** val exp_of_proto : exp0 -> exp **)

let rec exp_of_proto = function
| Econstr0 (x0, c0, ys, e0) -> Econstr (x0, c0, (strip_vars ys), (exp_of_proto e0))
| Ecase0 (x0, ces) -> Ecase (x0, (ces_of_proto' exp_of_proto ces))
| Eproj0 (x0, c0, n0, y0, e0) -> Eproj (x0, c0, n0, y0, (exp_of_proto e0))
| Eletapp0 (x0, f0, ft0, ys, e0) -> Eletapp (x0, f0, ft0, (strip_vars ys), (exp_of_proto e0))
| Efun0 (fds, e0) -> Efun ((fundefs_of_proto' exp_of_proto fds), (exp_of_proto e0))
| Eapp0 (f0, ft0, xs) -> Eapp (f0, ft0, (strip_vars xs))
| Eprim0 (x0, p0, ys, e0) -> Eprim (x0, p0, (strip_vars ys), (exp_of_proto e0))
| Ehalt0 x0 -> Ehalt x0

(** val proto_of_exp : exp -> exp0 **)

let rec proto_of_exp = function
| Econstr (x, c, ys, e0) -> Econstr0 (x, c, (map (fun x0 -> x0) ys), (proto_of_exp e0))
| Ecase (x, ces) -> Ecase0 (x, (map (fun pat -> let Pair (c, e0) = pat in Pair (c, (proto_of_exp e0))) ces))
| Eproj (x, c, n0, y, e0) -> Eproj0 (x, c, n0, y, (proto_of_exp e0))
| Eletapp (x, f, ft, ys, e0) -> Eletapp0 (x, f, ft, (map (fun x0 -> x0) ys), (proto_of_exp e0))
| Efun (fds, e0) -> Efun0 ((proto_of_fundefs fds), (proto_of_exp e0))
| Eapp (f, ft, ys) -> Eapp0 (f, ft, (map (fun x -> x) ys))
| Eprim (x, p, ys, e0) -> Eprim0 (x, p, (map (fun x0 -> x0) ys), (proto_of_exp e0))
| Ehalt x -> Ehalt0 x

(** val proto_of_fundefs : fundefs -> fundefs0 **)

and proto_of_fundefs = function
| Fcons (f, ft, xs, e, fds0) ->
  Cons ((Ffun (f, ft, (map (fun x -> x) xs), (proto_of_exp e))), (proto_of_fundefs fds0))
| Fnil -> Nil

type ('a, 'b) iso = { isoAofB : ('b -> 'a); isoBofA : ('a -> 'b) }

(** val iso_var : (var0, var) iso **)

let iso_var =
  { isoAofB = (fun x -> x); isoBofA = un_var }

(** val iso_vars : (var0 list, var list) iso **)

let iso_vars =
  { isoAofB = (map (fun x -> x)); isoBofA = strip_vars }

(** val iso_exp : (exp0, exp) iso **)

let iso_exp =
  { isoAofB = proto_of_exp; isoBofA = exp_of_proto }

(** val gensyms : var -> 'a1 list -> (var, var0 list) prod **)

let rec gensyms x = function
| Nil -> Pair (x, Nil)
| Cons (_, xs0) -> let Pair (x', xs') = gensyms (Pos.add x XH) xs0 in Pair (x', (Cons (x, xs')))

type s_fresh = var

type 'a error =
| Err of string
| Ret of 'a

type ('m, 'a) errorT = 'm

(** val monadErrorT : 'a1 monad -> ('a1, __) errorT monad **)

let monadErrorT hM =
  { ret = (fun _ x -> ret hM (Ret x)); bind = (fun _ _ m f ->
    bind hM m (fun r -> match r with
                        | Err s0 -> ret hM (Err s0)
                        | Ret a -> f a)) }

type ('r, 'w, 'a) state = 'r -> 'w -> ('a, 'w) prod
  (* singleton inductive, whose constructor was State *)

(** val runState : ('a1, 'a2, 'a3) state -> 'a1 -> 'a2 -> ('a3, 'a2) prod **)

let runState s0 =
  s0

(** val monadState : ('a1, 'a2, __) state monad **)

let monadState =
  { ret = (fun _ x _ w -> Pair (x, w)); bind = (fun _ _ m f r w ->
    let Pair (a, w') = runState m r w in runState (f a) r w') }

type ('r, 'w, 'a) compM = ('r, 'w, 'a error) state

(** val get0 : ('a1, 'a2, 'a2) compM **)

let get0 _ w =
  Pair ((Ret w), w)

(** val put : 'a2 -> ('a1, 'a2, unit0) compM **)

let put w _ _ =
  Pair ((Ret Tt), w)

type name_env0 = name pM

type comp_data = { next_var : var; nect_ctor_tag : ctor_tag; next_ind_tag : ind_tag; next_fun_tag : fun_tag;
                   cenv : ctor_env; fenv : fun_env; nenv : name_env0; log : string list }

type ('s, 'a) compM' = (unit0, (comp_data, 's) prod, 'a) compM

(** val get_ftag : n -> ('a1, fun_tag) compM' **)

let get_ftag arity =
  pbind (pMonad_Monad (monadErrorT (Obj.magic monadState))) (Obj.magic __) (Obj.magic get0) (fun p ->
    let Pair (y, st0) = p in
    let { next_var = x; nect_ctor_tag = c; next_ind_tag = i; next_fun_tag = f; cenv = e; fenv = fenv0; nenv = names;
      log = log0 } = y
    in
    pbind (pMonad_Monad (monadErrorT (Obj.magic monadState))) (Obj.magic __)
      (Obj.magic put (Pair ({ next_var = x; nect_ctor_tag = c; next_ind_tag = i; next_fun_tag = (Pos.add f XH);
        cenv = e; fenv = (Coq_M.set f (Pair (arity, (fromN N0 (Coq_N.to_nat arity)))) fenv0); nenv = names; log =
        log0 }, st0))) (fun _ -> ret (monadErrorT (Obj.magic monadState)) f))

(** val set_name : var -> var -> string -> comp_data -> comp_data **)

let set_name old_var new_var suff cdata =
  let { next_var = _; nect_ctor_tag = c; next_ind_tag = i; next_fun_tag = f; cenv = e; fenv = fenv0; nenv = names;
    log = log0 } = cdata
  in
  { next_var = (Pos.add XH (Pos.max old_var new_var)); nect_ctor_tag = c; next_ind_tag = i; next_fun_tag = f; cenv =
  e; fenv = fenv0; nenv = (add_entry names new_var old_var suff); log = log0 }

(** val set_names_lst : var list -> var list -> string -> comp_data -> comp_data **)

let set_names_lst olds news suff cdata =
  fold_right (fun pat cdata0 -> let Pair (old, new0) = pat in set_name old new0 suff cdata0) cdata
    (combine olds news)

type r_C = (exp_univ, bool) r_plain

type st = (nat, nat pM) prod

type arity_map = fun_tag0 pM

type local_map = bool pM

type s_misc = ((((bool, arity_map) prod, local_map) prod, st) prod, comp_data) prod

(** val get_fun_tag : n -> s_misc -> (fun_tag0, s_misc) prod **)

let get_fun_tag n0 ms = match ms with
| Pair (p, cdata) ->
  let Pair (p0, s0) = p in
  let Pair (p1, lm) = p0 in
  let Pair (b, aenv) = p1 in
  let n' = Coq_N.succ_pos n0 in
  (match Coq0_M.get n' aenv with
   | Some ft -> Pair (ft, ms)
   | None ->
     let Pair (mft, p2) = runState (get_ftag n0) Tt (Pair (cdata, Tt)) in
     let Pair (cdata0, _) = p2 in
     (match mft with
      | Err _ -> Pair (XH, ms)
      | Ret ft -> Pair (ft, (Pair ((Pair ((Pair ((Pair (b, (Coq0_M.set n' ft aenv))), lm)), s0)), cdata0)))))

type s = (exp_univ, (exp_univ, s_misc) s_plain, s_fresh) s_prod

(** val metadata_update :
    var0 -> var0 -> var0 -> nat -> var0 list -> var0 list -> var0 list -> var0 list -> s_misc -> s_misc **)

let metadata_update f g f1 fp_numargs fv gv fv1 gv1 = function
| Pair (p, cdata) ->
  let Pair (p0, s0) = p in
  let Pair (p1, lm) = p0 in
  let Pair (_, aenv) = p1 in
  Pair ((Pair ((Pair ((Pair (True, aenv)), (Coq0_M.set (iso_var.isoBofA g) True lm))), (Pair
  ((max (fst s0) fp_numargs),
  (Coq0_M.set (iso_var.isoBofA f) (S O) (Coq0_M.set (iso_var.isoBofA g) (S (S O)) (snd s0))))))),
  (set_name (iso_var.isoBofA f) (iso_var.isoBofA f1) (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True, False)), (String ((Ascii (False, True,
    True, True, False, True, True, False)), (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)), (String ((Ascii (False, True, False,
    False, True, True, True, False)), (String ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (True, False, False, True, False, True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False, True, True, False)),
    EmptyString))))))))))))))))))))
    (set_names_lst (iso_vars.isoBofA fv) (iso_vars.isoBofA fv1) EmptyString
      (set_names_lst (iso_vars.isoBofA gv) (iso_vars.isoBofA gv1) EmptyString cdata))))

(** val rw_uncurry : (exp_univ, exp_univ trivial_delay_t, r_C, s) rewriter **)

let rec rw_uncurry x a c e _ r s0 =
  match x with
  | XI _ ->
    (match a with
     | Exp_univ_prod_ctor_tag_exp ->
       let Pair (c0, e0) = Obj.magic e in
       let { resTree = x0; resState = s1 } =
         Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_prod_ctor_tag_exp,
           Exp_univ_exp, (Obj.magic (Pair_ctor_tag_exp1 c0)), c)) e0 Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
       in
       { resTree = (Obj.magic (Pair (c0, x0))); resState = (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
     | Exp_univ_list_prod_ctor_tag_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s0 }
         | Cons (p, u) ->
           let lpcte = Obj.magic u in
           let r_C0 = Obj.magic r in
           let { resTree = x0; resState = s1 } =
             rw_uncurry (Pos.pred x) Exp_univ_prod_ctor_tag_exp (Frames_cons (Exp_univ_prod_ctor_tag_exp,
               Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, (Obj.magic (Cons_prod_ctor_tag_exp0 lpcte)), c))
               (Obj.magic p) (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
           in
           let { resTree = x1; resState = s2 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))), c)) lpcte Tt r_C0 s1
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
             (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_fundef ->
       let Ffun (f, ft, xs, e0) = Obj.magic e in
       let { resTree = x2; resState = s1 } =
         Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_fundef, Exp_univ_exp,
           (Obj.magic (Ffun3 (f, ft, xs))), c)) e0 Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
       in
       { resTree = (Obj.magic (Ffun (f, ft, xs, (Obj.magic x2)))); resState =
       (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
     | Exp_univ_list_fundef ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s0 }
         | Cons (f, u) ->
           let Ffun (f0, ft, xs, e0) = f in
           (match e0 with
            | Efun0 (fds, e1) ->
              (match fds with
               | Nil ->
                 let lf = Obj.magic u in
                 let r_C0 = Obj.magic r in
                 let { resTree = x0; resState = s1 } =
                   rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
                     Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                     (Obj.magic (Ffun (f0, ft, xs, (Efun0 (Nil, e1))))) (Obj.magic Tt) r_C0
                     (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                 in
                 let { resTree = x1; resState = s2 } =
                   Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                     Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                 in
                 Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                   (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
               | Cons (f1, l) ->
                 let Ffun (f2, ft0, xs0, e2) = f1 in
                 (match l with
                  | Nil ->
                    (match e1 with
                     | Eapp0 (f3, ft1, xs1) ->
                       (match xs with
                        | Nil ->
                          let lf = Obj.magic u in
                          let r_C0 = Obj.magic r in
                          let { resTree = x0; resState = s1 } =
                            rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                              Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                              (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)), (Eapp0
                                (f3, ft1, xs1))))))) (Obj.magic Tt) r_C0
                              (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                          in
                          let { resTree = x1; resState = s2 } =
                            Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                              (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                              (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                          in
                          Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                            (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
                        | Cons (v, l0) ->
                          (match xs1 with
                           | Nil ->
                             let lf = Obj.magic u in
                             let r_C0 = Obj.magic r in
                             let { resTree = x0; resState = s1 } =
                               rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                 Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                 (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)),
                                   Nil)), (Eapp0 (f3, ft1, Nil))))))) (Obj.magic Tt) r_C0
                                 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                             in
                             let { resTree = x1; resState = s2 } =
                               Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                 (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                 (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                             in
                             Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                               (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
                           | Cons (v0, l1) ->
                             (match l1 with
                              | Nil ->
                                (match eq_var v f3 with
                                 | True ->
                                   (match eq_var f2 v0 with
                                    | True ->
                                      let Pair (ms, s1) = s0 in
                                      let Pair (p, _) = ms in
                                      let Pair (p0, _) = p in
                                      let Pair (p1, x0) = p0 in
                                      let Pair (b, _) = p1 in
                                      (match match r with
                                             | True ->
                                               negb (match Coq0_M.get f2 x0 with
                                                     | Some b0 -> b0
                                                     | None -> False)
                                             | False -> False with
                                       | True ->
                                         (match occurs_in_exp f2 (iso_exp.isoBofA e2) with
                                          | True ->
                                            let lf = Obj.magic u in
                                            let r_C0 = Obj.magic r in
                                            let { resTree = x1; resState = s2 } =
                                              rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                                Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)),
                                                c))
                                                (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2,
                                                  ft0, xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil)))))))))
                                                (Obj.magic Tt) r_C0
                                                (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                            in
                                            let { resTree = x2; resState = s3 } =
                                              Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                                (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s2
                                            in
                                            Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2))));
                                              resState = (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                          | False ->
                                            (match occurs_in_exp v (iso_exp.isoBofA e2) with
                                             | True ->
                                               let lf = Obj.magic u in
                                               let r_C0 = Obj.magic r in
                                               let { resTree = x1; resState = s2 } =
                                                 rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons
                                                   (Exp_univ_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef0 lf)), c))
                                                   (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun
                                                     (f2, ft0, xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0,
                                                     Nil))))))))) (Obj.magic Tt) r_C0
                                                   (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                               in
                                               let { resTree = x2; resState = s3 } =
                                                 Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                                   (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s2
                                               in
                                               Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2))));
                                                 resState = (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                             | False ->
                                               let Pair (ft2, ms') =
                                                 get_fun_tag (N.of_nat (add (length l0) (length xs0))) ms
                                               in
                                               let Pair (next_x0, gv1) = gensyms s1 xs0 in
                                               let Pair (next_x1, fv1) = gensyms next_x0 l0 in
                                               let f4 = Obj.magic f0 in
                                               let f5 = Obj.magic next_x1 in
                                               let ft3 = Obj.magic ft in
                                               let ft4 = Obj.magic ft2 in
                                               let k = Obj.magic v in
                                               let kt = Obj.magic ft1 in
                                               let fv = Obj.magic l0 in
                                               let fv2 = Obj.magic fv1 in
                                               let g = Obj.magic f2 in
                                               let gt = Obj.magic ft0 in
                                               let gv = Obj.magic xs0 in
                                               let gv2 = Obj.magic gv1 in
                                               let ge = Obj.magic e2 in
                                               let { resTree = x1; resState = s2 } =
                                                 rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                                   (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef1 (Ffun (f5, ft4, (app gv fv), ge)))),
                                                   (Frames_cons (Exp_univ_list_fundef, Exp_univ_list_fundef,
                                                   Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef1 (Ffun (f4, ft3, (Cons (k, fv2)), (Efun0
                                                     ((Cons ((Ffun (g, gt, gv2, (Eapp0 (f5, ft4, (app gv2 fv2))))),
                                                     Nil)), (Eapp0 (k, kt, (Cons (g, Nil)))))))))), c))))
                                                   (Obj.magic u) (Obj.magic Tt) (Obj.magic b)
                                                   (let Pair (s2, s3) =
                                                      Obj.magic (Pair
                                                        ((metadata_update f0 (iso_var.isoAofB f2)
                                                           (iso_var.isoAofB next_x1) (add (length l0) (length xs0))
                                                           l0 xs0 fv1 gv1 ms'), (Pos.add next_x1 XH)))
                                                    in
                                                    Pair (s2, s3))
                                               in
                                               Obj.magic { resTree =
                                                 (Obj.magic (Cons ((Ffun (f4, ft3, (Cons (k, fv2)), (Efun0 ((Cons
                                                   ((Ffun (g, gt, gv2, (Eapp0 (f5, ft4, (app gv2 fv2))))), Nil)),
                                                   (Eapp0 (k, kt, (Cons (g, Nil)))))))),
                                                   (Obj.magic (Cons ((Ffun (f5, ft4, (app gv fv), ge)),
                                                     (Obj.magic x1))))))); resState = s2 }))
                                       | False ->
                                         let lf = Obj.magic u in
                                         let r_C0 = Obj.magic r in
                                         let { resTree = x1; resState = s2 } =
                                           rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                             Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                             (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2,
                                               ft0, xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil)))))))))
                                             (Obj.magic Tt) r_C0 (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                         in
                                         let { resTree = x2; resState = s3 } =
                                           Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                             (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                             (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s2
                                         in
                                         Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                                           (let Pair (s4, s5) = s3 in Pair (s4, s5)) })
                                    | False ->
                                      let lf = Obj.magic u in
                                      let r_C0 = Obj.magic r in
                                      let { resTree = x0; resState = s1 } =
                                        rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                          Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                          (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0,
                                            xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil)))))))))
                                          (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                                      in
                                      let { resTree = x1; resState = s2 } =
                                        Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                          (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                          (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                                      in
                                      Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                                        (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                                 | False ->
                                   let lf = Obj.magic u in
                                   let r_C0 = Obj.magic r in
                                   let { resTree = x0; resState = s1 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                       Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                       (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                         e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil))))))))) (Obj.magic Tt) r_C0
                                       (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                                   in
                                   let { resTree = x1; resState = s2 } =
                                     Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                                   in
                                   Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                                     (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                              | Cons (v1, l2) ->
                                let lf = Obj.magic u in
                                let r_C0 = Obj.magic r in
                                let { resTree = x0; resState = s1 } =
                                  rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                    Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                    (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                      e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, (Cons (v1, l2)))))))))))
                                    (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                                in
                                let { resTree = x1; resState = s2 } =
                                  Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                    (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                    (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                                in
                                Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                                  (let Pair (s3, s4) = s2 in Pair (s3, s4)) })))
                     | Ehalt0 x0 ->
                       (match xs with
                        | Nil ->
                          (match eq_var f2 x0 with
                           | True ->
                             let Pair (ms, s1) = s0 in
                             let Pair (p, _) = ms in
                             let Pair (p0, _) = p in
                             let Pair (p1, x1) = p0 in
                             let Pair (b, _) = p1 in
                             (match match negb r with
                                    | True -> negb (match Coq0_M.get f2 x1 with
                                                    | Some b0 -> b0
                                                    | None -> False)
                                    | False -> False with
                              | True ->
                                (match occurs_in_exp f2 (iso_exp.isoBofA e2) with
                                 | True ->
                                   let lf = Obj.magic u in
                                   let r_C0 = Obj.magic r in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                       Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                       (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)),
                                         Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                       (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                   in
                                   let { resTree = x3; resState = s3 } =
                                     Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                   in
                                   Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                     (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                 | False ->
                                   let Pair (ft1, ms') = get_fun_tag (N.of_nat (add (length Nil) (length xs0))) ms in
                                   let Pair (next_x0, gv1) = gensyms s1 xs0 in
                                   let Pair (next_x1, fv1) = gensyms next_x0 Nil in
                                   let f3 = Obj.magic f0 in
                                   let f4 = Obj.magic next_x1 in
                                   let ft2 = Obj.magic ft in
                                   let ft3 = Obj.magic ft1 in
                                   let fv = Obj.magic Nil in
                                   let fv2 = Obj.magic fv1 in
                                   let g = Obj.magic f2 in
                                   let gt = Obj.magic ft0 in
                                   let gv = Obj.magic xs0 in
                                   let gv2 = Obj.magic gv1 in
                                   let ge = Obj.magic e2 in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f4, ft3, (app gv fv), ge)))), (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt,
                                         gv2, (Eapp0 (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))))), c))))
                                       (Obj.magic u) (Obj.magic Tt) (Obj.magic b)
                                       (let Pair (s2, s3) =
                                          Obj.magic (Pair
                                            ((metadata_update f0 (iso_var.isoAofB f2) (iso_var.isoAofB next_x1)
                                               (add (length Nil) (length xs0)) Nil xs0 fv1 gv1 ms'),
                                            (Pos.add next_x1 XH)))
                                        in
                                        Pair (s2, s3))
                                   in
                                   Obj.magic { resTree =
                                     (Obj.magic (Cons ((Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt, gv2, (Eapp0
                                       (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))),
                                       (Obj.magic (Cons ((Ffun (f4, ft3, (app gv fv), ge)), (Obj.magic x2)))))));
                                     resState = s2 })
                              | False ->
                                let lf = Obj.magic u in
                                let r_C0 = Obj.magic r in
                                let { resTree = x2; resState = s2 } =
                                  rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                    Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                    (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)),
                                      (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                    (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                in
                                let { resTree = x3; resState = s3 } =
                                  Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                    (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                    (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                in
                                Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                  (let Pair (s4, s5) = s3 in Pair (s4, s5)) })
                           | False ->
                             let lf = Obj.magic u in
                             let r_C0 = Obj.magic r in
                             let { resTree = x1; resState = s1 } =
                               rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                 Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                 (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)),
                                   (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                             in
                             let { resTree = x2; resState = s2 } =
                               Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                 (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                 (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s1
                             in
                             Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                               (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                        | Cons (v, l0) ->
                          (match eq_var f2 x0 with
                           | True ->
                             let Pair (ms, s1) = s0 in
                             let Pair (p, _) = ms in
                             let Pair (p0, _) = p in
                             let Pair (p1, x1) = p0 in
                             let Pair (b, _) = p1 in
                             (match match negb r with
                                    | True -> negb (match Coq0_M.get f2 x1 with
                                                    | Some b0 -> b0
                                                    | None -> False)
                                    | False -> False with
                              | True ->
                                (match occurs_in_exp f2 (iso_exp.isoBofA e2) with
                                 | True ->
                                   let lf = Obj.magic u in
                                   let r_C0 = Obj.magic r in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                       Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                       (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                         e2)), Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                       (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                   in
                                   let { resTree = x3; resState = s3 } =
                                     Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                   in
                                   Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                     (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                 | False ->
                                   let Pair (ft1, ms') =
                                     get_fun_tag (N.of_nat (add (length (Cons (v, l0))) (length xs0))) ms
                                   in
                                   let Pair (next_x0, gv1) = gensyms s1 xs0 in
                                   let Pair (next_x1, fv1) = gensyms next_x0 (Cons (v, l0)) in
                                   let f3 = Obj.magic f0 in
                                   let f4 = Obj.magic next_x1 in
                                   let ft2 = Obj.magic ft in
                                   let ft3 = Obj.magic ft1 in
                                   let fv = Obj.magic (Cons (v, l0)) in
                                   let fv2 = Obj.magic fv1 in
                                   let g = Obj.magic f2 in
                                   let gt = Obj.magic ft0 in
                                   let gv = Obj.magic xs0 in
                                   let gv2 = Obj.magic gv1 in
                                   let ge = Obj.magic e2 in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f4, ft3, (app gv fv), ge)))), (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt,
                                         gv2, (Eapp0 (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))))), c))))
                                       (Obj.magic u) (Obj.magic Tt) (Obj.magic b)
                                       (let Pair (s2, s3) =
                                          Obj.magic (Pair
                                            ((metadata_update f0 (iso_var.isoAofB f2) (iso_var.isoAofB next_x1)
                                               (add (length (Cons (v, l0))) (length xs0)) (Cons (v, l0)) xs0 fv1 gv1
                                               ms'), (Pos.add next_x1 XH)))
                                        in
                                        Pair (s2, s3))
                                   in
                                   Obj.magic { resTree =
                                     (Obj.magic (Cons ((Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt, gv2, (Eapp0
                                       (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))),
                                       (Obj.magic (Cons ((Ffun (f4, ft3, (app gv fv), ge)), (Obj.magic x2)))))));
                                     resState = s2 })
                              | False ->
                                let lf = Obj.magic u in
                                let r_C0 = Obj.magic r in
                                let { resTree = x2; resState = s2 } =
                                  rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                    Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                    (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                      e2)), Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                    (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                in
                                let { resTree = x3; resState = s3 } =
                                  Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                    (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                    (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                in
                                Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                  (let Pair (s4, s5) = s3 in Pair (s4, s5)) })
                           | False ->
                             let lf = Obj.magic u in
                             let r_C0 = Obj.magic r in
                             let { resTree = x1; resState = s1 } =
                               rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                 Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                 (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)),
                                   Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                             in
                             let { resTree = x2; resState = s2 } =
                               Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                 (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                 (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s1
                             in
                             Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                               (let Pair (s3, s4) = s2 in Pair (s3, s4)) }))
                     | x0 ->
                       let lf = Obj.magic u in
                       let r_C0 = Obj.magic r in
                       let { resTree = x1; resState = s1 } =
                         rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                           Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                           (Obj.magic (Ffun (f0, ft, xs, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)), x0)))))
                           (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                       in
                       let { resTree = x2; resState = s2 } =
                         Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                           Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt
                           r_C0 s1
                       in
                       Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                         (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                  | Cons (f3, l0) ->
                    let lf = Obj.magic u in
                    let r_C0 = Obj.magic r in
                    let { resTree = x0; resState = s1 } =
                      rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
                        Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                        (Obj.magic (Ffun (f0, ft, xs, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), (Cons (f3, l0)))),
                          e1))))) (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                    in
                    let { resTree = x1; resState = s2 } =
                      Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                        Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt
                        r_C0 s1
                    in
                    Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                      (let Pair (s3, s4) = s2 in Pair (s3, s4)) }))
            | x0 ->
              let lf = Obj.magic u in
              let r_C0 = Obj.magic r in
              let { resTree = x1; resState = s1 } =
                rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
                  Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c)) (Obj.magic (Ffun (f0, ft, xs, x0)))
                  (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
              in
              let { resTree = x2; resState = s2 } =
                Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                  Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s1
              in
              Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
       in
       { resTree = e'; resState = s' }
     | Exp_univ_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Econstr0 (x0, c0, ys, u) ->
           let { resTree = x2; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Econstr4 (x0, c0, ys))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Econstr0 (x0, c0, ys, (Obj.magic x2)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Ecase0 (x0, ces) ->
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase2 x0)), c)) ces Tt r
               (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Ecase0 (x0, (Obj.magic x1)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Eproj0 (x0, c0, n0, y, u) ->
           let { resTree = x3; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eproj5 (x0, c0, n0, y))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Eproj0 (x0, c0, n0, y, (Obj.magic x3)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Eletapp0 (x0, f, ft, ys, u) ->
           let { resTree = x3; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eletapp5 (x0, f, ft, ys))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Eletapp0 (x0, f, ft, ys, (Obj.magic x3)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Efun0 (fds, u) ->
           let e0 = Obj.magic u in
           let r_C0 = Obj.magic r in
           let { resTree = x0; resState = s1 } =
             rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef, Exp_univ_exp,
               Exp_univ_exp, (Obj.magic (Efun1 e0)), c)) (Obj.magic fds) (Obj.magic Tt) r_C0
               (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
           in
           let { resTree = x1; resState = s2 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Efun2 (Obj.magic x0))), c)) e0 Tt r_C0 s1
           in
           Obj.magic { resTree = (Obj.magic (Efun0 ((Obj.magic x0), (Obj.magic x1)))); resState =
             (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
         | Eapp0 (f, ft, xs) ->
           Obj.magic { resTree = (Obj.magic (Eapp0 ((Obj.magic f), (Obj.magic ft), (Obj.magic xs)))); resState =
             (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2)) }
         | Eprim0 (x0, p, ys, u) ->
           let { resTree = x2; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eprim4 (x0, p, ys))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Eprim0 (x0, p, ys, (Obj.magic x2)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Ehalt0 x0 ->
           Obj.magic { resTree = (Obj.magic (Ehalt0 (Obj.magic x0))); resState =
             (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2)) }
       in
       { resTree = e'; resState = s' }
     | _ -> { resTree = e; resState = s0 })
  | XO _ ->
    (match a with
     | Exp_univ_prod_ctor_tag_exp ->
       let Pair (c0, e0) = Obj.magic e in
       let { resTree = x0; resState = s1 } =
         Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_prod_ctor_tag_exp,
           Exp_univ_exp, (Obj.magic (Pair_ctor_tag_exp1 c0)), c)) e0 Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
       in
       { resTree = (Obj.magic (Pair (c0, x0))); resState = (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
     | Exp_univ_list_prod_ctor_tag_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s0 }
         | Cons (p, u) ->
           let lpcte = Obj.magic u in
           let r_C0 = Obj.magic r in
           let { resTree = x0; resState = s1 } =
             rw_uncurry (Pos.pred x) Exp_univ_prod_ctor_tag_exp (Frames_cons (Exp_univ_prod_ctor_tag_exp,
               Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, (Obj.magic (Cons_prod_ctor_tag_exp0 lpcte)), c))
               (Obj.magic p) (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
           in
           let { resTree = x1; resState = s2 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               (Obj.magic (Cons_prod_ctor_tag_exp1 (Obj.magic x0))), c)) lpcte Tt r_C0 s1
           in
           Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
             (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
       in
       { resTree = e'; resState = s' }
     | Exp_univ_fundef ->
       let Ffun (f, ft, xs, e0) = Obj.magic e in
       let { resTree = x2; resState = s1 } =
         Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_fundef, Exp_univ_exp,
           (Obj.magic (Ffun3 (f, ft, xs))), c)) e0 Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
       in
       { resTree = (Obj.magic (Ffun (f, ft, xs, (Obj.magic x2)))); resState =
       (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
     | Exp_univ_list_fundef ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Nil -> { resTree = (Obj.magic Nil); resState = s0 }
         | Cons (f, u) ->
           let Ffun (f0, ft, xs, e0) = f in
           (match e0 with
            | Efun0 (fds, e1) ->
              (match fds with
               | Nil ->
                 let lf = Obj.magic u in
                 let r_C0 = Obj.magic r in
                 let { resTree = x0; resState = s1 } =
                   rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
                     Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                     (Obj.magic (Ffun (f0, ft, xs, (Efun0 (Nil, e1))))) (Obj.magic Tt) r_C0
                     (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                 in
                 let { resTree = x1; resState = s2 } =
                   Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                     Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                 in
                 Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                   (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
               | Cons (f1, l) ->
                 let Ffun (f2, ft0, xs0, e2) = f1 in
                 (match l with
                  | Nil ->
                    (match e1 with
                     | Eapp0 (f3, ft1, xs1) ->
                       (match xs with
                        | Nil ->
                          let lf = Obj.magic u in
                          let r_C0 = Obj.magic r in
                          let { resTree = x0; resState = s1 } =
                            rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                              Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                              (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)), (Eapp0
                                (f3, ft1, xs1))))))) (Obj.magic Tt) r_C0
                              (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                          in
                          let { resTree = x1; resState = s2 } =
                            Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                              (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                              (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                          in
                          Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                            (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
                        | Cons (v, l0) ->
                          (match xs1 with
                           | Nil ->
                             let lf = Obj.magic u in
                             let r_C0 = Obj.magic r in
                             let { resTree = x0; resState = s1 } =
                               rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                 Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                 (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)),
                                   Nil)), (Eapp0 (f3, ft1, Nil))))))) (Obj.magic Tt) r_C0
                                 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                             in
                             let { resTree = x1; resState = s2 } =
                               Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                 (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                 (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                             in
                             Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                               (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
                           | Cons (v0, l1) ->
                             (match l1 with
                              | Nil ->
                                (match eq_var v f3 with
                                 | True ->
                                   (match eq_var f2 v0 with
                                    | True ->
                                      let Pair (ms, s1) = s0 in
                                      let Pair (p, _) = ms in
                                      let Pair (p0, _) = p in
                                      let Pair (p1, x0) = p0 in
                                      let Pair (b, _) = p1 in
                                      (match match r with
                                             | True ->
                                               negb (match Coq0_M.get f2 x0 with
                                                     | Some b0 -> b0
                                                     | None -> False)
                                             | False -> False with
                                       | True ->
                                         (match occurs_in_exp f2 (iso_exp.isoBofA e2) with
                                          | True ->
                                            let lf = Obj.magic u in
                                            let r_C0 = Obj.magic r in
                                            let { resTree = x1; resState = s2 } =
                                              rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                                Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)),
                                                c))
                                                (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2,
                                                  ft0, xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil)))))))))
                                                (Obj.magic Tt) r_C0
                                                (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                            in
                                            let { resTree = x2; resState = s3 } =
                                              Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                                (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s2
                                            in
                                            Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2))));
                                              resState = (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                          | False ->
                                            (match occurs_in_exp v (iso_exp.isoBofA e2) with
                                             | True ->
                                               let lf = Obj.magic u in
                                               let r_C0 = Obj.magic r in
                                               let { resTree = x1; resState = s2 } =
                                                 rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons
                                                   (Exp_univ_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef0 lf)), c))
                                                   (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun
                                                     (f2, ft0, xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0,
                                                     Nil))))))))) (Obj.magic Tt) r_C0
                                                   (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                               in
                                               let { resTree = x2; resState = s3 } =
                                                 Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                                   (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s2
                                               in
                                               Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2))));
                                                 resState = (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                             | False ->
                                               let Pair (ft2, ms') =
                                                 get_fun_tag (N.of_nat (add (length l0) (length xs0))) ms
                                               in
                                               let Pair (next_x0, gv1) = gensyms s1 xs0 in
                                               let Pair (next_x1, fv1) = gensyms next_x0 l0 in
                                               let f4 = Obj.magic f0 in
                                               let f5 = Obj.magic next_x1 in
                                               let ft3 = Obj.magic ft in
                                               let ft4 = Obj.magic ft2 in
                                               let k = Obj.magic v in
                                               let kt = Obj.magic ft1 in
                                               let fv = Obj.magic l0 in
                                               let fv2 = Obj.magic fv1 in
                                               let g = Obj.magic f2 in
                                               let gt = Obj.magic ft0 in
                                               let gv = Obj.magic xs0 in
                                               let gv2 = Obj.magic gv1 in
                                               let ge = Obj.magic e2 in
                                               let { resTree = x1; resState = s2 } =
                                                 rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                                   (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef1 (Ffun (f5, ft4, (app gv fv), ge)))),
                                                   (Frames_cons (Exp_univ_list_fundef, Exp_univ_list_fundef,
                                                   Exp_univ_exp,
                                                   (Obj.magic (Cons_fundef1 (Ffun (f4, ft3, (Cons (k, fv2)), (Efun0
                                                     ((Cons ((Ffun (g, gt, gv2, (Eapp0 (f5, ft4, (app gv2 fv2))))),
                                                     Nil)), (Eapp0 (k, kt, (Cons (g, Nil)))))))))), c))))
                                                   (Obj.magic u) (Obj.magic Tt) (Obj.magic b)
                                                   (let Pair (s2, s3) =
                                                      Obj.magic (Pair
                                                        ((metadata_update f0 (iso_var.isoAofB f2)
                                                           (iso_var.isoAofB next_x1) (add (length l0) (length xs0))
                                                           l0 xs0 fv1 gv1 ms'), (Pos.add next_x1 XH)))
                                                    in
                                                    Pair (s2, s3))
                                               in
                                               Obj.magic { resTree =
                                                 (Obj.magic (Cons ((Ffun (f4, ft3, (Cons (k, fv2)), (Efun0 ((Cons
                                                   ((Ffun (g, gt, gv2, (Eapp0 (f5, ft4, (app gv2 fv2))))), Nil)),
                                                   (Eapp0 (k, kt, (Cons (g, Nil)))))))),
                                                   (Obj.magic (Cons ((Ffun (f5, ft4, (app gv fv), ge)),
                                                     (Obj.magic x1))))))); resState = s2 }))
                                       | False ->
                                         let lf = Obj.magic u in
                                         let r_C0 = Obj.magic r in
                                         let { resTree = x1; resState = s2 } =
                                           rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                             Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                             (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2,
                                               ft0, xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil)))))))))
                                             (Obj.magic Tt) r_C0 (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                         in
                                         let { resTree = x2; resState = s3 } =
                                           Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                             (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                             (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s2
                                         in
                                         Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                                           (let Pair (s4, s5) = s3 in Pair (s4, s5)) })
                                    | False ->
                                      let lf = Obj.magic u in
                                      let r_C0 = Obj.magic r in
                                      let { resTree = x0; resState = s1 } =
                                        rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                          Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                          (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0,
                                            xs0, e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil)))))))))
                                          (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                                      in
                                      let { resTree = x1; resState = s2 } =
                                        Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                          (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                          (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                                      in
                                      Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                                        (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                                 | False ->
                                   let lf = Obj.magic u in
                                   let r_C0 = Obj.magic r in
                                   let { resTree = x0; resState = s1 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                       Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                       (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                         e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, Nil))))))))) (Obj.magic Tt) r_C0
                                       (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                                   in
                                   let { resTree = x1; resState = s2 } =
                                     Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                                   in
                                   Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                                     (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                              | Cons (v1, l2) ->
                                let lf = Obj.magic u in
                                let r_C0 = Obj.magic r in
                                let { resTree = x0; resState = s1 } =
                                  rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                    Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                    (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                      e2)), Nil)), (Eapp0 (f3, ft1, (Cons (v0, (Cons (v1, l2)))))))))))
                                    (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                                in
                                let { resTree = x1; resState = s2 } =
                                  Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                    (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                    (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt r_C0 s1
                                in
                                Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                                  (let Pair (s3, s4) = s2 in Pair (s3, s4)) })))
                     | Ehalt0 x0 ->
                       (match xs with
                        | Nil ->
                          (match eq_var f2 x0 with
                           | True ->
                             let Pair (ms, s1) = s0 in
                             let Pair (p, _) = ms in
                             let Pair (p0, _) = p in
                             let Pair (p1, x1) = p0 in
                             let Pair (b, _) = p1 in
                             (match match negb r with
                                    | True -> negb (match Coq0_M.get f2 x1 with
                                                    | Some b0 -> b0
                                                    | None -> False)
                                    | False -> False with
                              | True ->
                                (match occurs_in_exp f2 (iso_exp.isoBofA e2) with
                                 | True ->
                                   let lf = Obj.magic u in
                                   let r_C0 = Obj.magic r in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                       Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                       (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)),
                                         Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                       (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                   in
                                   let { resTree = x3; resState = s3 } =
                                     Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                   in
                                   Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                     (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                 | False ->
                                   let Pair (ft1, ms') = get_fun_tag (N.of_nat (add (length Nil) (length xs0))) ms in
                                   let Pair (next_x0, gv1) = gensyms s1 xs0 in
                                   let Pair (next_x1, fv1) = gensyms next_x0 Nil in
                                   let f3 = Obj.magic f0 in
                                   let f4 = Obj.magic next_x1 in
                                   let ft2 = Obj.magic ft in
                                   let ft3 = Obj.magic ft1 in
                                   let fv = Obj.magic Nil in
                                   let fv2 = Obj.magic fv1 in
                                   let g = Obj.magic f2 in
                                   let gt = Obj.magic ft0 in
                                   let gv = Obj.magic xs0 in
                                   let gv2 = Obj.magic gv1 in
                                   let ge = Obj.magic e2 in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f4, ft3, (app gv fv), ge)))), (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt,
                                         gv2, (Eapp0 (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))))), c))))
                                       (Obj.magic u) (Obj.magic Tt) (Obj.magic b)
                                       (let Pair (s2, s3) =
                                          Obj.magic (Pair
                                            ((metadata_update f0 (iso_var.isoAofB f2) (iso_var.isoAofB next_x1)
                                               (add (length Nil) (length xs0)) Nil xs0 fv1 gv1 ms'),
                                            (Pos.add next_x1 XH)))
                                        in
                                        Pair (s2, s3))
                                   in
                                   Obj.magic { resTree =
                                     (Obj.magic (Cons ((Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt, gv2, (Eapp0
                                       (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))),
                                       (Obj.magic (Cons ((Ffun (f4, ft3, (app gv fv), ge)), (Obj.magic x2)))))));
                                     resState = s2 })
                              | False ->
                                let lf = Obj.magic u in
                                let r_C0 = Obj.magic r in
                                let { resTree = x2; resState = s2 } =
                                  rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                    Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                    (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)),
                                      (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                    (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                in
                                let { resTree = x3; resState = s3 } =
                                  Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                    (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                    (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                in
                                Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                  (let Pair (s4, s5) = s3 in Pair (s4, s5)) })
                           | False ->
                             let lf = Obj.magic u in
                             let r_C0 = Obj.magic r in
                             let { resTree = x1; resState = s1 } =
                               rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                 Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                 (Obj.magic (Ffun (f0, ft, Nil, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)),
                                   (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                             in
                             let { resTree = x2; resState = s2 } =
                               Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                 (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                 (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s1
                             in
                             Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                               (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                        | Cons (v, l0) ->
                          (match eq_var f2 x0 with
                           | True ->
                             let Pair (ms, s1) = s0 in
                             let Pair (p, _) = ms in
                             let Pair (p0, _) = p in
                             let Pair (p1, x1) = p0 in
                             let Pair (b, _) = p1 in
                             (match match negb r with
                                    | True -> negb (match Coq0_M.get f2 x1 with
                                                    | Some b0 -> b0
                                                    | None -> False)
                                    | False -> False with
                              | True ->
                                (match occurs_in_exp f2 (iso_exp.isoBofA e2) with
                                 | True ->
                                   let lf = Obj.magic u in
                                   let r_C0 = Obj.magic r in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                       Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                       (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                         e2)), Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                       (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                   in
                                   let { resTree = x3; resState = s3 } =
                                     Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                   in
                                   Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                     (let Pair (s4, s5) = s3 in Pair (s4, s5)) }
                                 | False ->
                                   let Pair (ft1, ms') =
                                     get_fun_tag (N.of_nat (add (length (Cons (v, l0))) (length xs0))) ms
                                   in
                                   let Pair (next_x0, gv1) = gensyms s1 xs0 in
                                   let Pair (next_x1, fv1) = gensyms next_x0 (Cons (v, l0)) in
                                   let f3 = Obj.magic f0 in
                                   let f4 = Obj.magic next_x1 in
                                   let ft2 = Obj.magic ft in
                                   let ft3 = Obj.magic ft1 in
                                   let fv = Obj.magic (Cons (v, l0)) in
                                   let fv2 = Obj.magic fv1 in
                                   let g = Obj.magic f2 in
                                   let gt = Obj.magic ft0 in
                                   let gv = Obj.magic xs0 in
                                   let gv2 = Obj.magic gv1 in
                                   let ge = Obj.magic e2 in
                                   let { resTree = x2; resState = s2 } =
                                     rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f4, ft3, (app gv fv), ge)))), (Frames_cons
                                       (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                       (Obj.magic (Cons_fundef1 (Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt,
                                         gv2, (Eapp0 (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))))), c))))
                                       (Obj.magic u) (Obj.magic Tt) (Obj.magic b)
                                       (let Pair (s2, s3) =
                                          Obj.magic (Pair
                                            ((metadata_update f0 (iso_var.isoAofB f2) (iso_var.isoAofB next_x1)
                                               (add (length (Cons (v, l0))) (length xs0)) (Cons (v, l0)) xs0 fv1 gv1
                                               ms'), (Pos.add next_x1 XH)))
                                        in
                                        Pair (s2, s3))
                                   in
                                   Obj.magic { resTree =
                                     (Obj.magic (Cons ((Ffun (f3, ft2, fv2, (Efun0 ((Cons ((Ffun (g, gt, gv2, (Eapp0
                                       (f4, ft3, (app gv2 fv2))))), Nil)), (Ehalt0 g))))),
                                       (Obj.magic (Cons ((Ffun (f4, ft3, (app gv fv), ge)), (Obj.magic x2)))))));
                                     resState = s2 })
                              | False ->
                                let lf = Obj.magic u in
                                let r_C0 = Obj.magic r in
                                let { resTree = x2; resState = s2 } =
                                  rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                    Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                    (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0,
                                      e2)), Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                    (let Pair (s2, s3) = Obj.magic s0 in Pair (s2, s3))
                                in
                                let { resTree = x3; resState = s3 } =
                                  Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                    (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                    (Obj.magic (Cons_fundef1 (Obj.magic x2))), c)) lf Tt r_C0 s2
                                in
                                Obj.magic { resTree = (Obj.magic (Cons (x2, (Obj.magic x3)))); resState =
                                  (let Pair (s4, s5) = s3 in Pair (s4, s5)) })
                           | False ->
                             let lf = Obj.magic u in
                             let r_C0 = Obj.magic r in
                             let { resTree = x1; resState = s1 } =
                               rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                                 Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                                 (Obj.magic (Ffun (f0, ft, (Cons (v, l0)), (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)),
                                   Nil)), (Ehalt0 x0)))))) (Obj.magic Tt) r_C0
                                 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                             in
                             let { resTree = x2; resState = s2 } =
                               Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
                                 (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
                                 (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s1
                             in
                             Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                               (let Pair (s3, s4) = s2 in Pair (s3, s4)) }))
                     | x0 ->
                       let lf = Obj.magic u in
                       let r_C0 = Obj.magic r in
                       let { resTree = x1; resState = s1 } =
                         rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef,
                           Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                           (Obj.magic (Ffun (f0, ft, xs, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), Nil)), x0)))))
                           (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                       in
                       let { resTree = x2; resState = s2 } =
                         Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                           Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt
                           r_C0 s1
                       in
                       Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                         (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
                  | Cons (f3, l0) ->
                    let lf = Obj.magic u in
                    let r_C0 = Obj.magic r in
                    let { resTree = x0; resState = s1 } =
                      rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
                        Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c))
                        (Obj.magic (Ffun (f0, ft, xs, (Efun0 ((Cons ((Ffun (f2, ft0, xs0, e2)), (Cons (f3, l0)))),
                          e1))))) (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
                    in
                    let { resTree = x1; resState = s2 } =
                      Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                        Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x0))), c)) lf Tt
                        r_C0 s1
                    in
                    Obj.magic { resTree = (Obj.magic (Cons (x0, (Obj.magic x1)))); resState =
                      (let Pair (s3, s4) = s2 in Pair (s3, s4)) }))
            | x0 ->
              let lf = Obj.magic u in
              let r_C0 = Obj.magic r in
              let { resTree = x1; resState = s1 } =
                rw_uncurry (Pos.pred x) Exp_univ_fundef (Frames_cons (Exp_univ_fundef, Exp_univ_list_fundef,
                  Exp_univ_exp, (Obj.magic (Cons_fundef0 lf)), c)) (Obj.magic (Ffun (f0, ft, xs, x0)))
                  (Obj.magic Tt) r_C0 (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
              in
              let { resTree = x2; resState = s2 } =
                Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef,
                  Exp_univ_list_fundef, Exp_univ_exp, (Obj.magic (Cons_fundef1 (Obj.magic x1))), c)) lf Tt r_C0 s1
              in
              Obj.magic { resTree = (Obj.magic (Cons (x1, (Obj.magic x2)))); resState =
                (let Pair (s3, s4) = s2 in Pair (s3, s4)) })
       in
       { resTree = e'; resState = s' }
     | Exp_univ_exp ->
       let { resTree = e'; resState = s' } =
         match Obj.magic e with
         | Econstr0 (x0, c0, ys, u) ->
           let { resTree = x2; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Econstr4 (x0, c0, ys))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Econstr0 (x0, c0, ys, (Obj.magic x2)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Ecase0 (x0, ces) ->
           let { resTree = x1; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, (Obj.magic (Ecase2 x0)), c)) ces Tt r
               (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Ecase0 (x0, (Obj.magic x1)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Eproj0 (x0, c0, n0, y, u) ->
           let { resTree = x3; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eproj5 (x0, c0, n0, y))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Eproj0 (x0, c0, n0, y, (Obj.magic x3)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Eletapp0 (x0, f, ft, ys, u) ->
           let { resTree = x3; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eletapp5 (x0, f, ft, ys))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Eletapp0 (x0, f, ft, ys, (Obj.magic x3)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Efun0 (fds, u) ->
           let e0 = Obj.magic u in
           let r_C0 = Obj.magic r in
           let { resTree = x0; resState = s1 } =
             rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef, Exp_univ_exp,
               Exp_univ_exp, (Obj.magic (Efun1 e0)), c)) (Obj.magic fds) (Obj.magic Tt) r_C0
               (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2))
           in
           let { resTree = x1; resState = s2 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Efun2 (Obj.magic x0))), c)) e0 Tt r_C0 s1
           in
           Obj.magic { resTree = (Obj.magic (Efun0 ((Obj.magic x0), (Obj.magic x1)))); resState =
             (let Pair (s3, s4) = s2 in Pair (s3, s4)) }
         | Eapp0 (f, ft, xs) ->
           Obj.magic { resTree = (Obj.magic (Eapp0 ((Obj.magic f), (Obj.magic ft), (Obj.magic xs)))); resState =
             (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2)) }
         | Eprim0 (x0, p, ys, u) ->
           let { resTree = x2; resState = s1 } =
             Obj.magic rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
               (Obj.magic (Eprim4 (x0, p, ys))), c)) u Tt r (let Pair (s1, s2) = s0 in Pair (s1, s2))
           in
           { resTree = (Obj.magic (Eprim0 (x0, p, ys, (Obj.magic x2)))); resState =
           (let Pair (s2, s3) = s1 in Pair (s2, s3)) }
         | Ehalt0 x0 ->
           Obj.magic { resTree = (Obj.magic (Ehalt0 (Obj.magic x0))); resState =
             (let Pair (s1, s2) = Obj.magic s0 in Pair (s1, s2)) }
       in
       { resTree = e'; resState = s' }
     | _ -> { resTree = e; resState = s0 })
  | XH -> { resTree = e; resState = s0 }
