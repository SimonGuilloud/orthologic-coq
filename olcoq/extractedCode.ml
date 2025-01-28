
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

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

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

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
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
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
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

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

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> False)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos p -> (match y with
                 | Zpos p0 -> Pos.eq_dec p p0
                 | _ -> Right)
    | Zneg p -> (match y with
                 | Zneg p0 -> Pos.eq_dec p p0
                 | _ -> Right)
 end

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> Left
    | _ -> Right

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> True
    | Right -> False
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module PairOrderedType =
 functor (O1:OrderedType) ->
 functor (O2:OrderedType) ->
 struct
  module MO1 = OrderedTypeFacts(O1)

  module MO2 = OrderedTypeFacts(O2)

  type t = (O1.t, O2.t) prod

  (** val compare : t -> t -> (O1.t, O2.t) prod compare0 **)

  let compare x y =
    let Pair (t0, t1) = x in
    let Pair (t2, t3) = y in
    let c = O1.compare t0 t2 in
    (match c with
     | LT -> LT
     | EQ ->
       let c0 = O2.compare t1 t3 in
       (match c0 with
        | LT -> LT
        | EQ -> EQ
        | GT -> GT)
     | GT -> GT)

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec x y =
    match compare x y with
    | EQ -> Left
    | _ -> Right
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> sumbool

  val ge_lt_dec : t -> t -> sumbool

  val eq_dec : t -> t -> sumbool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> sumbool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in (match b with
                          | True -> Left
                          | False -> Right)

  (** val ge_lt_dec : z -> z -> sumbool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in (match b with
                          | True -> Right
                          | False -> Left)

  (** val i2z : t -> z **)

  let i2z n =
    n
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t, 'elt) prod list

  (** val empty : 'a1 t **)

  let empty =
    Nil

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | Nil -> True
  | Cons (_, _) -> False

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | Nil -> False
  | Cons (p, l) ->
    let Pair (k', _) = p in
    (match X.compare k k' with
     | LT -> False
     | EQ -> True
     | GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | Nil -> None
  | Cons (p, s') ->
    let Pair (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | Nil -> Cons ((Pair (k, x)), Nil)
  | Cons (p, l) ->
    let Pair (k', y) = p in
    (match X.compare k k' with
     | LT -> Cons ((Pair (k, x)), s)
     | EQ -> Cons ((Pair (k, x)), l)
     | GT -> Cons ((Pair (k', y)), (add k x l)))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | Nil -> Nil
  | Cons (p, l) ->
    let Pair (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> Cons ((Pair (k', x)), (remove k l)))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | Nil -> acc
    | Cons (p, m') -> let Pair (k, e) = p in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | Nil -> (match m' with
              | Nil -> True
              | Cons (_, _) -> False)
    | Cons (p, l) ->
      let Pair (x, e) = p in
      (match m' with
       | Nil -> False
       | Cons (p0, l') ->
         let Pair (x', e') = p0 in
         (match X.compare x x' with
          | EQ ->
            (match cmp e e' with
             | True -> equal cmp l l'
             | False -> False)
          | _ -> False))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | Nil -> Nil
  | Cons (p, m') ->
    let Pair (k, e) = p in Cons ((Pair (k, (f e))), (map f m'))

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | Nil -> Nil
  | Cons (p, m') ->
    let Pair (k, e) = p in Cons ((Pair (k, (f k e))), (mapi f m'))

  (** val option_cons :
      key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list **)

  let option_cons k o l =
    match o with
    | Some e -> Cons ((Pair (k, e)), l)
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | Nil -> Nil
  | Cons (p, l) ->
    let Pair (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | Nil -> Nil
  | Cons (p, l') ->
    let Pair (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | Nil -> map2_r f
  | Cons (p, l) ->
    let Pair (k, e) = p in
    let rec map2_aux m' = match m' with
    | Nil -> map2_l f m
    | Cons (p0, l') ->
      let Pair (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t **)

  let rec combine m = match m with
  | Nil -> map (fun e' -> Pair (None, (Some e')))
  | Cons (p, l) ->
    let Pair (k, e) = p in
    let rec combine_aux m' = match m' with
    | Nil -> map (fun e0 -> Pair ((Some e0), None)) m
    | Cons (p0, l') ->
      let Pair (k', e') = p0 in
      (match X.compare k k' with
       | LT -> Cons ((Pair (k, (Pair ((Some e), None)))), (combine l m'))
       | EQ -> Cons ((Pair (k, (Pair ((Some e), (Some e'))))), (combine l l'))
       | GT -> Cons ((Pair (k', (Pair (None, (Some e'))))), (combine_aux l')))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
      'a3) prod list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 Nil

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (Pair (o, o'))
    | None -> (match o' with
               | Some _ -> Some (Pair (o, o'))
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> True
  | Node (_, _, _, _, _) -> False

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> False
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> True
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    (match I.gt_le_dec hl (I.add hr I._2) with
     | Left ->
       (match l with
        | Leaf -> assert_false l x d r
        | Node (ll, lx, ld, lr, _) ->
          (match I.ge_lt_dec (height ll) (height lr) with
           | Left -> create ll lx ld (create lr x d r)
           | Right ->
             (match lr with
              | Leaf -> assert_false l x d r
              | Node (lrl, lrx, lrd, lrr, _) ->
                create (create ll lx ld lrl) lrx lrd (create lrr x d r))))
     | Right ->
       (match I.gt_le_dec hr (I.add hl I._2) with
        | Left ->
          (match r with
           | Leaf -> assert_false l x d r
           | Node (rl, rx, rd, rr, _) ->
             (match I.ge_lt_dec (height rr) (height rl) with
              | Left -> create (create l x d rl) rx rd rr
              | Right ->
                (match rl with
                 | Leaf -> assert_false l x d r
                 | Node (rll, rlx, rld, rlr, _) ->
                   create (create l x d rll) rlx rld (create rlr rx rd rr))))
        | Right -> create l x d r))

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> Pair (r, (Pair (x, d)))
    | Node (ll, lx, ld, lr, _) ->
      let Pair (l', m) = remove_min ll lx ld lr in Pair ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let Pair (s2', p) = remove_min l2 x2 d2 r2 in
         let Pair (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        (match I.gt_le_dec lh (I.add rh I._2) with
         | Left -> bal ll lx ld (join lr x d r)
         | Right ->
           (match I.gt_le_dec rh (I.add lh I._2) with
            | Left -> bal (join_aux rl) rx rd rr
            | Right -> create l x d r))
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let Pair (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) ->
    elements_aux (Cons ((Pair (x, d)), (elements_aux acc r))) l

  (** val elements : 'a1 tree -> (key, 'a1) prod list **)

  let elements m =
    elements_aux Nil m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> False
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> (match cmp d1 d2 with
              | True -> cont (cons r2 e3)
              | False -> False)
     | _ -> False)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> True
  | More (_, _, _, _) -> False

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree, (key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt tree * (key, 'elt) prod

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key, 'elt) prod * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key, 'elt) prod

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key, 'a1) prod list **)

    let rec flatten_e = function
    | End -> Nil
    | More (x, e0, t0, r) ->
      Cons ((Pair (x, e0)), (app (elements t0) (flatten_e r)))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key, 'a1) prod list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

type pointer = positive

type termPointer =
| VarP of positive * pointer
| MeetP of termPointer * termPointer * pointer
| JoinP of termPointer * termPointer * pointer
| NotP of termPointer * pointer

(** val get_pointer : termPointer -> pointer **)

let get_pointer = function
| VarP (_, p) -> p
| MeetP (_, _, p) -> p
| JoinP (_, _, p) -> p
| NotP (_, p) -> p

type anTermPointer =
| NTP
| LTP of termPointer
| RTP of termPointer

type anPointer =
| NP
| LP of pointer
| RP of pointer

(** val compare_anpointer : anPointer -> anPointer -> comparison **)

let compare_anpointer x y =
  match x with
  | NP -> (match y with
           | NP -> Eq
           | _ -> Gt)
  | LP n1 -> (match y with
              | LP n2 -> Pos.compare n1 n2
              | _ -> Lt)
  | RP n1 -> (match y with
              | NP -> Lt
              | LP _ -> Gt
              | RP n2 -> Pos.compare n1 n2)

module AnPointer_as_OT =
 struct
  type t = anPointer

  (** val compare : t -> t -> anPointer compare0 **)

  let compare x y =
    let c = compare_anpointer x y in
    (match c with
     | Eq -> EQ
     | Lt -> LT
     | Gt -> GT)

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec x y =
    let c = compare_anpointer x y in (match c with
                                      | Eq -> Left
                                      | _ -> Right)
 end

module AnPointerPair_as_OT = PairOrderedType(AnPointer_as_OT)(AnPointer_as_OT)

module AnPointerPairAVLMap = Make(AnPointerPair_as_OT)

type memoMap = bool AnPointerPairAVLMap.t

type memoMapBool = memoMap -> (bool, memoMap) prod

(** val mor :
    memoMapBool -> memoMapBool -> memoMap -> (bool, memoMap) prod **)

let mor left right memo =
  let Pair (b, m) = left memo in
  (match b with
   | True -> Pair (True, m)
   | False -> right m)

(** val mand :
    memoMapBool -> memoMapBool -> memoMap -> (bool, memoMap) prod **)

let mand left right memo =
  let Pair (b, m) = left memo in
  (match b with
   | True -> right m
   | False -> Pair (False, m))

(** val mbool : bool -> memoMapBool **)

let mbool b memo =
  Pair (b, memo)

(** val mfalse : memoMapBool **)

let mfalse =
  mbool False

module M = AnPointerPairAVLMap

(** val get_pointer_anterm : anTermPointer -> anPointer **)

let get_pointer_anterm = function
| NTP -> NP
| LTP p -> LP (get_pointer p)
| RTP p -> RP (get_pointer p)

(** val decideOL_pointers :
    nat -> anTermPointer -> anTermPointer -> memoMap -> (bool, memoMap) prod **)

let rec decideOL_pointers fuel g d memo =
  match M.find (Pair ((get_pointer_anterm g), (get_pointer_anterm d))) memo with
  | Some b -> Pair (b, memo)
  | None ->
    (match fuel with
     | O -> Pair (False, memo)
     | S n ->
       let Pair (b, m) =
         match g with
         | NTP ->
           (match d with
            | NTP ->
              mor
                (match g with
                 | LTP t0 ->
                   (match t0 with
                    | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                    | _ -> mfalse)
                 | _ -> mfalse)
                (mor
                  (match g with
                   | LTP t0 ->
                     (match t0 with
                      | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                      | _ -> mfalse)
                   | _ -> mfalse)
                  (mor
                    (match d with
                     | LTP t0 ->
                       (match t0 with
                        | MeetP (a, _, _) -> decideOL_pointers n g (LTP a)
                        | _ -> mfalse)
                     | _ -> mfalse)
                    (mor
                      (match d with
                       | LTP t0 ->
                         (match t0 with
                          | MeetP (_, b, _) -> decideOL_pointers n g (LTP b)
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | RTP t0 ->
                           (match t0 with
                            | JoinP (a, _, _) -> decideOL_pointers n (RTP a) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match g with
                           | RTP t0 ->
                             (match t0 with
                              | JoinP (_, b, _) ->
                                decideOL_pointers n (RTP b) d
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | RTP t0 ->
                               (match t0 with
                                | JoinP (a, _, _) ->
                                  decideOL_pointers n g (RTP a)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match d with
                               | RTP t0 ->
                                 (match t0 with
                                  | JoinP (_, b, _) ->
                                    decideOL_pointers n g (RTP b)
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match d with
                                 | NTP -> decideOL_pointers n g g
                                 | _ -> mfalse)
                                (mor
                                  (match g with
                                   | NTP -> decideOL_pointers n d d
                                   | _ -> mfalse)
                                  (mor (decideOL_pointers n g NTP)
                                    (decideOL_pointers n NTP d)))))))))))
                (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                  (get_pointer_anterm d))) False memo)
            | LTP t0 ->
              (match t0 with
               | VarP (_, _) ->
                 mfalse
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | MeetP (_, _, _) ->
                 mor
                   (match g with
                    | LTP t1 ->
                      (match t1 with
                       | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                       | _ -> mfalse)
                    | _ -> mfalse)
                   (mor
                     (match g with
                      | LTP t1 ->
                        (match t1 with
                         | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                         | _ -> mfalse)
                      | _ -> mfalse)
                     (mor
                       (match d with
                        | LTP t1 ->
                          (match t1 with
                           | MeetP (a, _, _) -> decideOL_pointers n g (LTP a)
                           | _ -> mfalse)
                        | _ -> mfalse)
                       (mor
                         (match d with
                          | LTP t1 ->
                            (match t1 with
                             | MeetP (_, b, _) ->
                               decideOL_pointers n g (LTP b)
                             | _ -> mfalse)
                          | _ -> mfalse)
                         (mor
                           (match g with
                            | RTP t1 ->
                              (match t1 with
                               | JoinP (a, _, _) ->
                                 decideOL_pointers n (RTP a) d
                               | _ -> mfalse)
                            | _ -> mfalse)
                           (mor
                             (match g with
                              | RTP t1 ->
                                (match t1 with
                                 | JoinP (_, b, _) ->
                                   decideOL_pointers n (RTP b) d
                                 | _ -> mfalse)
                              | _ -> mfalse)
                             (mor
                               (match d with
                                | RTP t1 ->
                                  (match t1 with
                                   | JoinP (a, _, _) ->
                                     decideOL_pointers n g (RTP a)
                                   | _ -> mfalse)
                                | _ -> mfalse)
                               (mor
                                 (match d with
                                  | RTP t1 ->
                                    (match t1 with
                                     | JoinP (_, b, _) ->
                                       decideOL_pointers n g (RTP b)
                                     | _ -> mfalse)
                                  | _ -> mfalse)
                                 (mor
                                   (match d with
                                    | NTP -> decideOL_pointers n g g
                                    | _ -> mfalse)
                                   (mor
                                     (match g with
                                      | NTP -> decideOL_pointers n d d
                                      | _ -> mfalse)
                                     (mor (decideOL_pointers n g NTP)
                                       (decideOL_pointers n NTP d)))))))))))
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | JoinP (a, b, _) ->
                 mand (decideOL_pointers n g (LTP a))
                   (decideOL_pointers n g (LTP b))
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | NotP (a, _) ->
                 decideOL_pointers n g (RTP a)
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo))
            | RTP t0 ->
              (match t0 with
               | VarP (_, _) ->
                 mfalse
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | MeetP (a, b, _) ->
                 mand (decideOL_pointers n g (RTP a))
                   (decideOL_pointers n g (RTP b))
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | JoinP (_, _, _) ->
                 mor
                   (match g with
                    | LTP t1 ->
                      (match t1 with
                       | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                       | _ -> mfalse)
                    | _ -> mfalse)
                   (mor
                     (match g with
                      | LTP t1 ->
                        (match t1 with
                         | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                         | _ -> mfalse)
                      | _ -> mfalse)
                     (mor
                       (match d with
                        | LTP t1 ->
                          (match t1 with
                           | MeetP (a, _, _) -> decideOL_pointers n g (LTP a)
                           | _ -> mfalse)
                        | _ -> mfalse)
                       (mor
                         (match d with
                          | LTP t1 ->
                            (match t1 with
                             | MeetP (_, b, _) ->
                               decideOL_pointers n g (LTP b)
                             | _ -> mfalse)
                          | _ -> mfalse)
                         (mor
                           (match g with
                            | RTP t1 ->
                              (match t1 with
                               | JoinP (a, _, _) ->
                                 decideOL_pointers n (RTP a) d
                               | _ -> mfalse)
                            | _ -> mfalse)
                           (mor
                             (match g with
                              | RTP t1 ->
                                (match t1 with
                                 | JoinP (_, b, _) ->
                                   decideOL_pointers n (RTP b) d
                                 | _ -> mfalse)
                              | _ -> mfalse)
                             (mor
                               (match d with
                                | RTP t1 ->
                                  (match t1 with
                                   | JoinP (a, _, _) ->
                                     decideOL_pointers n g (RTP a)
                                   | _ -> mfalse)
                                | _ -> mfalse)
                               (mor
                                 (match d with
                                  | RTP t1 ->
                                    (match t1 with
                                     | JoinP (_, b, _) ->
                                       decideOL_pointers n g (RTP b)
                                     | _ -> mfalse)
                                  | _ -> mfalse)
                                 (mor
                                   (match d with
                                    | NTP -> decideOL_pointers n g g
                                    | _ -> mfalse)
                                   (mor
                                     (match g with
                                      | NTP -> decideOL_pointers n d d
                                      | _ -> mfalse)
                                     (mor (decideOL_pointers n g NTP)
                                       (decideOL_pointers n NTP d)))))))))))
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | NotP (a, _) ->
                 decideOL_pointers n g (LTP a)
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)))
         | LTP t0 ->
           (match t0 with
            | VarP (a, _) ->
              (match d with
               | NTP ->
                 mfalse
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | LTP t1 ->
                 (match t1 with
                  | VarP (_, _) ->
                    mfalse
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | MeetP (_, _, _) ->
                    mor
                      (match g with
                       | LTP t2 ->
                         (match t2 with
                          | MeetP (a0, _, _) -> decideOL_pointers n (LTP a0) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t2 ->
                           (match t2 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t2 ->
                             (match t2 with
                              | MeetP (a0, _, _) ->
                                decideOL_pointers n g (LTP a0)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t2 ->
                               (match t2 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t2 ->
                                 (match t2 with
                                  | JoinP (a0, _, _) ->
                                    decideOL_pointers n (RTP a0) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t2 ->
                                   (match t2 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t2 ->
                                     (match t2 with
                                      | JoinP (a0, _, _) ->
                                        decideOL_pointers n g (RTP a0)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t2 ->
                                       (match t2 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | JoinP (a0, b, _) ->
                    mand (decideOL_pointers n g (LTP a0))
                      (decideOL_pointers n g (LTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a0, _) ->
                    decideOL_pointers n g (RTP a0)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))
               | RTP t1 ->
                 (match t1 with
                  | VarP (b, _) ->
                    mbool (Pos.eqb a b)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | MeetP (a0, b, _) ->
                    mand (decideOL_pointers n g (RTP a0))
                      (decideOL_pointers n g (RTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | JoinP (_, _, _) ->
                    mor
                      (match g with
                       | LTP t2 ->
                         (match t2 with
                          | MeetP (a0, _, _) -> decideOL_pointers n (LTP a0) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t2 ->
                           (match t2 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t2 ->
                             (match t2 with
                              | MeetP (a0, _, _) ->
                                decideOL_pointers n g (LTP a0)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t2 ->
                               (match t2 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t2 ->
                                 (match t2 with
                                  | JoinP (a0, _, _) ->
                                    decideOL_pointers n (RTP a0) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t2 ->
                                   (match t2 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t2 ->
                                     (match t2 with
                                      | JoinP (a0, _, _) ->
                                        decideOL_pointers n g (RTP a0)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t2 ->
                                       (match t2 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a0, _) ->
                    decideOL_pointers n g (LTP a0)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)))
            | MeetP (_, _, _) ->
              (match d with
               | NTP ->
                 mor
                   (match g with
                    | LTP t1 ->
                      (match t1 with
                       | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                       | _ -> mfalse)
                    | _ -> mfalse)
                   (mor
                     (match g with
                      | LTP t1 ->
                        (match t1 with
                         | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                         | _ -> mfalse)
                      | _ -> mfalse)
                     (mor
                       (match d with
                        | LTP t1 ->
                          (match t1 with
                           | MeetP (a, _, _) -> decideOL_pointers n g (LTP a)
                           | _ -> mfalse)
                        | _ -> mfalse)
                       (mor
                         (match d with
                          | LTP t1 ->
                            (match t1 with
                             | MeetP (_, b, _) ->
                               decideOL_pointers n g (LTP b)
                             | _ -> mfalse)
                          | _ -> mfalse)
                         (mor
                           (match g with
                            | RTP t1 ->
                              (match t1 with
                               | JoinP (a, _, _) ->
                                 decideOL_pointers n (RTP a) d
                               | _ -> mfalse)
                            | _ -> mfalse)
                           (mor
                             (match g with
                              | RTP t1 ->
                                (match t1 with
                                 | JoinP (_, b, _) ->
                                   decideOL_pointers n (RTP b) d
                                 | _ -> mfalse)
                              | _ -> mfalse)
                             (mor
                               (match d with
                                | RTP t1 ->
                                  (match t1 with
                                   | JoinP (a, _, _) ->
                                     decideOL_pointers n g (RTP a)
                                   | _ -> mfalse)
                                | _ -> mfalse)
                               (mor
                                 (match d with
                                  | RTP t1 ->
                                    (match t1 with
                                     | JoinP (_, b, _) ->
                                       decideOL_pointers n g (RTP b)
                                     | _ -> mfalse)
                                  | _ -> mfalse)
                                 (mor
                                   (match d with
                                    | NTP -> decideOL_pointers n g g
                                    | _ -> mfalse)
                                   (mor
                                     (match g with
                                      | NTP -> decideOL_pointers n d d
                                      | _ -> mfalse)
                                     (mor (decideOL_pointers n g NTP)
                                       (decideOL_pointers n NTP d)))))))))))
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | LTP t2 ->
                 (match t2 with
                  | JoinP (a, b, _) ->
                    mand (decideOL_pointers n g (LTP a))
                      (decideOL_pointers n g (LTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a, _) ->
                    decideOL_pointers n g (RTP a)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    mor
                      (match g with
                       | LTP t1 ->
                         (match t1 with
                          | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t1 ->
                           (match t1 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t1 ->
                             (match t1 with
                              | MeetP (a, _, _) ->
                                decideOL_pointers n g (LTP a)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t1 ->
                               (match t1 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t1 ->
                                 (match t1 with
                                  | JoinP (a, _, _) ->
                                    decideOL_pointers n (RTP a) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t1 ->
                                   (match t1 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t1 ->
                                     (match t1 with
                                      | JoinP (a, _, _) ->
                                        decideOL_pointers n g (RTP a)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t1 ->
                                       (match t1 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))
               | RTP t2 ->
                 (match t2 with
                  | MeetP (a, b, _) ->
                    mand (decideOL_pointers n g (RTP a))
                      (decideOL_pointers n g (RTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a, _) ->
                    decideOL_pointers n g (LTP a)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    mor
                      (match g with
                       | LTP t1 ->
                         (match t1 with
                          | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t1 ->
                           (match t1 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t1 ->
                             (match t1 with
                              | MeetP (a, _, _) ->
                                decideOL_pointers n g (LTP a)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t1 ->
                               (match t1 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t1 ->
                                 (match t1 with
                                  | JoinP (a, _, _) ->
                                    decideOL_pointers n (RTP a) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t1 ->
                                   (match t1 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t1 ->
                                     (match t1 with
                                      | JoinP (a, _, _) ->
                                        decideOL_pointers n g (RTP a)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t1 ->
                                       (match t1 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)))
            | JoinP (a, b, _) ->
              mand (decideOL_pointers n (LTP a) d)
                (decideOL_pointers n (LTP b) d)
                (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                  (get_pointer_anterm d))) False memo)
            | NotP (a, _) ->
              (match d with
               | NTP ->
                 decideOL_pointers n (RTP a) d
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | LTP t1 ->
                 (match t1 with
                  | JoinP (a0, b, _) ->
                    mand (decideOL_pointers n g (LTP a0))
                      (decideOL_pointers n g (LTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    decideOL_pointers n (RTP a) d
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))
               | RTP t1 ->
                 (match t1 with
                  | MeetP (a0, b, _) ->
                    mand (decideOL_pointers n g (RTP a0))
                      (decideOL_pointers n g (RTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    decideOL_pointers n (RTP a) d
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))))
         | RTP t0 ->
           (match t0 with
            | VarP (a, _) ->
              (match d with
               | NTP ->
                 mfalse
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | LTP t1 ->
                 (match t1 with
                  | VarP (b, _) ->
                    mbool (Pos.eqb a b)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | MeetP (_, _, _) ->
                    mor
                      (match g with
                       | LTP t2 ->
                         (match t2 with
                          | MeetP (a0, _, _) -> decideOL_pointers n (LTP a0) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t2 ->
                           (match t2 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t2 ->
                             (match t2 with
                              | MeetP (a0, _, _) ->
                                decideOL_pointers n g (LTP a0)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t2 ->
                               (match t2 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t2 ->
                                 (match t2 with
                                  | JoinP (a0, _, _) ->
                                    decideOL_pointers n (RTP a0) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t2 ->
                                   (match t2 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t2 ->
                                     (match t2 with
                                      | JoinP (a0, _, _) ->
                                        decideOL_pointers n g (RTP a0)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t2 ->
                                       (match t2 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | JoinP (a0, b, _) ->
                    mand (decideOL_pointers n g (LTP a0))
                      (decideOL_pointers n g (LTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a0, _) ->
                    decideOL_pointers n g (RTP a0)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))
               | RTP t1 ->
                 (match t1 with
                  | VarP (_, _) ->
                    mfalse
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | MeetP (a0, b, _) ->
                    mand (decideOL_pointers n g (RTP a0))
                      (decideOL_pointers n g (RTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | JoinP (_, _, _) ->
                    mor
                      (match g with
                       | LTP t2 ->
                         (match t2 with
                          | MeetP (a0, _, _) -> decideOL_pointers n (LTP a0) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t2 ->
                           (match t2 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t2 ->
                             (match t2 with
                              | MeetP (a0, _, _) ->
                                decideOL_pointers n g (LTP a0)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t2 ->
                               (match t2 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t2 ->
                                 (match t2 with
                                  | JoinP (a0, _, _) ->
                                    decideOL_pointers n (RTP a0) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t2 ->
                                   (match t2 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t2 ->
                                     (match t2 with
                                      | JoinP (a0, _, _) ->
                                        decideOL_pointers n g (RTP a0)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t2 ->
                                       (match t2 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a0, _) ->
                    decideOL_pointers n g (LTP a0)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)))
            | MeetP (a, b, _) ->
              (match d with
               | LTP t1 ->
                 (match t1 with
                  | JoinP (a0, b0, _) ->
                    mand (decideOL_pointers n g (LTP a0))
                      (decideOL_pointers n g (LTP b0))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    mand (decideOL_pointers n (RTP a) d)
                      (decideOL_pointers n (RTP b) d)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))
               | _ ->
                 mand (decideOL_pointers n (RTP a) d)
                   (decideOL_pointers n (RTP b) d)
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo))
            | JoinP (_, _, _) ->
              (match d with
               | NTP ->
                 mor
                   (match g with
                    | LTP t1 ->
                      (match t1 with
                       | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                       | _ -> mfalse)
                    | _ -> mfalse)
                   (mor
                     (match g with
                      | LTP t1 ->
                        (match t1 with
                         | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                         | _ -> mfalse)
                      | _ -> mfalse)
                     (mor
                       (match d with
                        | LTP t1 ->
                          (match t1 with
                           | MeetP (a, _, _) -> decideOL_pointers n g (LTP a)
                           | _ -> mfalse)
                        | _ -> mfalse)
                       (mor
                         (match d with
                          | LTP t1 ->
                            (match t1 with
                             | MeetP (_, b, _) ->
                               decideOL_pointers n g (LTP b)
                             | _ -> mfalse)
                          | _ -> mfalse)
                         (mor
                           (match g with
                            | RTP t1 ->
                              (match t1 with
                               | JoinP (a, _, _) ->
                                 decideOL_pointers n (RTP a) d
                               | _ -> mfalse)
                            | _ -> mfalse)
                           (mor
                             (match g with
                              | RTP t1 ->
                                (match t1 with
                                 | JoinP (_, b, _) ->
                                   decideOL_pointers n (RTP b) d
                                 | _ -> mfalse)
                              | _ -> mfalse)
                             (mor
                               (match d with
                                | RTP t1 ->
                                  (match t1 with
                                   | JoinP (a, _, _) ->
                                     decideOL_pointers n g (RTP a)
                                   | _ -> mfalse)
                                | _ -> mfalse)
                               (mor
                                 (match d with
                                  | RTP t1 ->
                                    (match t1 with
                                     | JoinP (_, b, _) ->
                                       decideOL_pointers n g (RTP b)
                                     | _ -> mfalse)
                                  | _ -> mfalse)
                                 (mor
                                   (match d with
                                    | NTP -> decideOL_pointers n g g
                                    | _ -> mfalse)
                                   (mor
                                     (match g with
                                      | NTP -> decideOL_pointers n d d
                                      | _ -> mfalse)
                                     (mor (decideOL_pointers n g NTP)
                                       (decideOL_pointers n NTP d)))))))))))
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | LTP t2 ->
                 (match t2 with
                  | JoinP (a, b, _) ->
                    mand (decideOL_pointers n g (LTP a))
                      (decideOL_pointers n g (LTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a, _) ->
                    decideOL_pointers n g (RTP a)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    mor
                      (match g with
                       | LTP t1 ->
                         (match t1 with
                          | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t1 ->
                           (match t1 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t1 ->
                             (match t1 with
                              | MeetP (a, _, _) ->
                                decideOL_pointers n g (LTP a)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t1 ->
                               (match t1 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t1 ->
                                 (match t1 with
                                  | JoinP (a, _, _) ->
                                    decideOL_pointers n (RTP a) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t1 ->
                                   (match t1 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t1 ->
                                     (match t1 with
                                      | JoinP (a, _, _) ->
                                        decideOL_pointers n g (RTP a)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t1 ->
                                       (match t1 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))
               | RTP t2 ->
                 (match t2 with
                  | MeetP (a, b, _) ->
                    mand (decideOL_pointers n g (RTP a))
                      (decideOL_pointers n g (RTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a, _) ->
                    decideOL_pointers n g (LTP a)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    mor
                      (match g with
                       | LTP t1 ->
                         (match t1 with
                          | MeetP (a, _, _) -> decideOL_pointers n (LTP a) d
                          | _ -> mfalse)
                       | _ -> mfalse)
                      (mor
                        (match g with
                         | LTP t1 ->
                           (match t1 with
                            | MeetP (_, b, _) -> decideOL_pointers n (LTP b) d
                            | _ -> mfalse)
                         | _ -> mfalse)
                        (mor
                          (match d with
                           | LTP t1 ->
                             (match t1 with
                              | MeetP (a, _, _) ->
                                decideOL_pointers n g (LTP a)
                              | _ -> mfalse)
                           | _ -> mfalse)
                          (mor
                            (match d with
                             | LTP t1 ->
                               (match t1 with
                                | MeetP (_, b, _) ->
                                  decideOL_pointers n g (LTP b)
                                | _ -> mfalse)
                             | _ -> mfalse)
                            (mor
                              (match g with
                               | RTP t1 ->
                                 (match t1 with
                                  | JoinP (a, _, _) ->
                                    decideOL_pointers n (RTP a) d
                                  | _ -> mfalse)
                               | _ -> mfalse)
                              (mor
                                (match g with
                                 | RTP t1 ->
                                   (match t1 with
                                    | JoinP (_, b, _) ->
                                      decideOL_pointers n (RTP b) d
                                    | _ -> mfalse)
                                 | _ -> mfalse)
                                (mor
                                  (match d with
                                   | RTP t1 ->
                                     (match t1 with
                                      | JoinP (a, _, _) ->
                                        decideOL_pointers n g (RTP a)
                                      | _ -> mfalse)
                                   | _ -> mfalse)
                                  (mor
                                    (match d with
                                     | RTP t1 ->
                                       (match t1 with
                                        | JoinP (_, b, _) ->
                                          decideOL_pointers n g (RTP b)
                                        | _ -> mfalse)
                                     | _ -> mfalse)
                                    (mor
                                      (match d with
                                       | NTP -> decideOL_pointers n g g
                                       | _ -> mfalse)
                                      (mor
                                        (match g with
                                         | NTP -> decideOL_pointers n d d
                                         | _ -> mfalse)
                                        (mor (decideOL_pointers n g NTP)
                                          (decideOL_pointers n NTP d)))))))))))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)))
            | NotP (a, _) ->
              (match d with
               | NTP ->
                 decideOL_pointers n (LTP a) d
                   (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                     (get_pointer_anterm d))) False memo)
               | LTP t1 ->
                 (match t1 with
                  | JoinP (a0, b, _) ->
                    mand (decideOL_pointers n g (LTP a0))
                      (decideOL_pointers n g (LTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | NotP (a0, _) ->
                    decideOL_pointers n g (RTP a0)
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    decideOL_pointers n (LTP a) d
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))
               | RTP t1 ->
                 (match t1 with
                  | MeetP (a0, b, _) ->
                    mand (decideOL_pointers n g (RTP a0))
                      (decideOL_pointers n g (RTP b))
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo)
                  | _ ->
                    decideOL_pointers n (LTP a) d
                      (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
                        (get_pointer_anterm d))) False memo))))
       in
       Pair (b,
       (AnPointerPairAVLMap.add (Pair ((get_pointer_anterm g),
         (get_pointer_anterm d))) b m)))
