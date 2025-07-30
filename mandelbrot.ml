
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
  (** val max : int -> int -> int **)

  let rec max n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n0
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n1 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n1 l0))
    n0

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: l0 -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

type positive =
| XI of positive
| XO of positive
| XH

module Coq__2 = struct
 type n =
 | N0
 | Npos of positive
end
include Coq__2

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

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

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

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op add x (Stdlib.Int.succ 0)

  (** val pred : positive -> positive **)

  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
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
 end

module Coq_Z =
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

  let sub m n0 =
    add m (opp n0)

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

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

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
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val of_nat : int -> z **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n1 -> Zpos (Pos.of_succ_nat n1))
      n0

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q, _) = div_eucl a b in q
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      match p with
      | XI p' -> shift true (loop n' p')
      | XO p' -> shift false (loop n' p')
      | XH -> one)
      n0
  in loop (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c0::s1' -> c0::(append s1' s2)

(** val concat : char list -> char list list -> char list **)

let rec concat sep = function
| [] -> []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))

(** val base : positive -> z **)

let base digits0 =
  Coq_Z.pow (Zpos (XO XH)) (Zpos digits0)

type 'znz zn2z =
| W0
| WW of 'znz * 'znz

(** val zn2z_to_Z : z -> ('a1 -> z) -> 'a1 zn2z -> z **)

let zn2z_to_Z wB w_to_Z = function
| W0 -> Z0
| WW (xh, xl) -> Coq_Z.add (Coq_Z.mul (w_to_Z xh) wB) (w_to_Z xl)

type 'w word = __

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lor0 = Uint63.l_or

(** val lxor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lxor0 = Uint63.l_xor

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

(** val mul0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mul0 = Uint63.mul

(** val mulc : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let mulc = Uint63.mulc

(** val div0 : Uint63.t -> Uint63.t -> Uint63.t **)

let div0 = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

(** val leb0 : Uint63.t -> Uint63.t -> bool **)

let leb0 = Uint63.le

(** val addc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry **)

let addc = Uint63.addc

(** val addcarryc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry **)

let addcarryc = Uint63.addcarryc

(** val subc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry **)

let subc = Uint63.subc

(** val subcarryc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry **)

let subcarryc = Uint63.subcarryc

(** val diveucl : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let diveucl = Uint63.diveucl

(** val diveucl_21 :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let diveucl_21 = Uint63.div21

(** val addmuldiv : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let addmuldiv = Uint63.addmuldiv

(** val compare0 : Uint63.t -> Uint63.t -> comparison **)

let compare0 = (fun x y -> let c = Uint63.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)

(** val head0 : Uint63.t -> Uint63.t **)

let head0 = Uint63.head0

(** val tail0 : Uint63.t -> Uint63.t **)

let tail0 = Uint63.tail0

(** val size : int **)

let size =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val digits : Uint63.t **)

let digits =
  (Uint63.of_int (63))

(** val max_int : Uint63.t **)

let max_int =
  (Uint63.of_int (-1))

(** val is_zero : Uint63.t -> bool **)

let is_zero i =
  eqb i (Uint63.of_int (0))

(** val is_even : Uint63.t -> bool **)

let is_even i =
  is_zero (land0 i (Uint63.of_int (1)))

(** val to_Z_rec : int -> Uint63.t -> z **)

let rec to_Z_rec n0 i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Z0)
    (fun n1 ->
    if is_even i
    then Z.double (to_Z_rec n1 (lsr0 i (Uint63.of_int (1))))
    else Z.succ_double (to_Z_rec n1 (lsr0 i (Uint63.of_int (1)))))
    n0

(** val to_Z : Uint63.t -> z **)

let to_Z =
  to_Z_rec size

(** val addcarry : Uint63.t -> Uint63.t -> Uint63.t **)

let addcarry i j =
  add0 (add0 i j) (Uint63.of_int (1))

(** val opp0 : Uint63.t -> Uint63.t **)

let opp0 i =
  sub0 (Uint63.of_int (0)) i

(** val oppcarry : Uint63.t -> Uint63.t **)

let oppcarry i =
  sub0 max_int i

(** val succ0 : Uint63.t -> Uint63.t **)

let succ0 i =
  add0 i (Uint63.of_int (1))

(** val pred0 : Uint63.t -> Uint63.t **)

let pred0 i =
  sub0 i (Uint63.of_int (1))

(** val subcarry : Uint63.t -> Uint63.t -> Uint63.t **)

let subcarry i j =
  sub0 (sub0 i j) (Uint63.of_int (1))

(** val oppc : Uint63.t -> Uint63.t Uint63.carry **)

let oppc i =
  subc (Uint63.of_int (0)) i

(** val succc : Uint63.t -> Uint63.t Uint63.carry **)

let succc i =
  addc i (Uint63.of_int (1))

(** val predc : Uint63.t -> Uint63.t Uint63.carry **)

let predc i =
  subc i (Uint63.of_int (1))

(** val iter_sqrt :
    int -> (Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec iter_sqrt n0 rec0 i j =
  let quo = div0 i j in
  if ltb0 quo j
  then ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> rec0 i (lsr0 (add0 j quo) (Uint63.of_int (1))))
          (fun n1 ->
          iter_sqrt n1 (iter_sqrt n1 rec0) i
            (lsr0 (add0 j quo) (Uint63.of_int (1))))
          n0)
  else j

(** val sqrt : Uint63.t -> Uint63.t **)

let sqrt i =
  match compare0 (Uint63.of_int (1)) i with
  | Eq -> (Uint63.of_int (1))
  | Lt -> iter_sqrt size (fun _ j -> j) i (lsr0 i (Uint63.of_int (1)))
  | Gt -> (Uint63.of_int (0))

(** val high_bit : Uint63.t **)

let high_bit =
  lsl0 (Uint63.of_int (1)) (sub0 digits (Uint63.of_int (1)))

(** val iter2_sqrt :
    int -> (Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t **)

let rec iter2_sqrt n0 rec0 ih il j =
  if ltb0 ih j
  then let (quo, _) = diveucl_21 ih il j in
       if ltb0 quo j
       then (match addc j quo with
             | Uint63.C0 m1 ->
               ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ ->
                  rec0 ih il (lsr0 m1 (Uint63.of_int (1))))
                  (fun n1 ->
                  iter2_sqrt n1 (iter2_sqrt n1 rec0) ih il
                    (lsr0 m1 (Uint63.of_int (1))))
                  n0)
             | Uint63.C1 m1 ->
               ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ ->
                  rec0 ih il (add0 (lsr0 m1 (Uint63.of_int (1))) high_bit))
                  (fun n1 ->
                  iter2_sqrt n1 (iter2_sqrt n1 rec0) ih il
                    (add0 (lsr0 m1 (Uint63.of_int (1))) high_bit))
                  n0))
       else j
  else j

(** val sqrt2 : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t Uint63.carry **)

let sqrt2 ih il =
  let s = iter2_sqrt size (fun _ _ j -> j) ih il max_int in
  let (ih1, il1) = mulc s s in
  (match subc il il1 with
   | Uint63.C0 il2 ->
     if ltb0 ih1 ih then (s, (Uint63.C1 il2)) else (s, (Uint63.C0 il2))
   | Uint63.C1 il2 ->
     if ltb0 ih1 (sub0 ih (Uint63.of_int (1)))
     then (s, (Uint63.C1 il2))
     else (s, (Uint63.C0 il2)))

(** val gcd_rec : int -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec gcd_rec guard i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (Uint63.of_int (1)))
    (fun p ->
    if eqb j (Uint63.of_int (0)) then i else gcd_rec p j (mod0 i j))
    guard

(** val gcd : Uint63.t -> Uint63.t -> Uint63.t **)

let gcd =
  gcd_rec (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) size)

type 't pred1 = 't -> bool

type 't rel = 't -> 't pred1

(** val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec merge leT s1 = match s1 with
| [] -> (fun x -> x)
| x1 :: s1' ->
  let rec merge_s1 s2 = match s2 with
  | [] -> s1
  | x2 :: s2' ->
    if leT x1 x2 then x1 :: (merge leT s1' s2) else x2 :: (merge_s1 s2')
  in merge_s1

(** val merge_sort_push :
    'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec merge_sort_push leT s1 ss = match ss with
| [] -> s1 :: ss
| s2 :: ss' ->
  (match s2 with
   | [] -> s1 :: ss'
   | _ :: _ -> [] :: (merge_sort_push leT (merge leT s2 s1) ss'))

(** val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list **)

let rec merge_sort_pop leT s1 = function
| [] -> s1
| s2 :: ss' -> merge_sort_pop leT (merge leT s2 s1) ss'

(** val merge_sort_rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec merge_sort_rec leT ss s = match s with
| [] -> merge_sort_pop leT s ss
| x1 :: l ->
  (match l with
   | [] -> merge_sort_pop leT s ss
   | x2 :: s' ->
     let s1 = if leT x1 x2 then x1 :: (x2 :: []) else x2 :: (x1 :: []) in
     merge_sort_rec leT (merge_sort_push leT s1 ss) s')

(** val sort : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort leT =
  merge_sort_rec leT []

module ZnZ =
 struct
  type 't coq_Ops = { digits : positive; zdigits : 't; to_Z : ('t -> z);
                      of_pos : (positive -> n * 't); head0 : ('t -> 't);
                      tail0 : ('t -> 't); zero : 't; one : 't;
                      minus_one : 't; compare : ('t -> 't -> comparison);
                      eq0 : ('t -> bool); opp_c : ('t -> 't Uint63.carry);
                      opp : ('t -> 't); opp_carry : ('t -> 't);
                      succ_c : ('t -> 't Uint63.carry);
                      add_c : ('t -> 't -> 't Uint63.carry);
                      add_carry_c : ('t -> 't -> 't Uint63.carry);
                      succ : ('t -> 't); add : ('t -> 't -> 't);
                      add_carry : ('t -> 't -> 't);
                      pred_c : ('t -> 't Uint63.carry);
                      sub_c : ('t -> 't -> 't Uint63.carry);
                      sub_carry_c : ('t -> 't -> 't Uint63.carry);
                      pred : ('t -> 't); sub : ('t -> 't -> 't);
                      sub_carry : ('t -> 't -> 't);
                      mul_c : ('t -> 't -> 't zn2z); mul : ('t -> 't -> 't);
                      square_c : ('t -> 't zn2z);
                      div21 : ('t -> 't -> 't -> 't * 't);
                      div_gt : ('t -> 't -> 't * 't);
                      div : ('t -> 't -> 't * 't);
                      modulo_gt : ('t -> 't -> 't);
                      modulo : ('t -> 't -> 't); gcd_gt : ('t -> 't -> 't);
                      gcd : ('t -> 't -> 't);
                      add_mul_div : ('t -> 't -> 't -> 't);
                      pos_mod : ('t -> 't -> 't); is_even : ('t -> bool);
                      sqrt2 : ('t -> 't -> 't * 't Uint63.carry);
                      sqrt : ('t -> 't); coq_lor : ('t -> 't -> 't);
                      coq_land : ('t -> 't -> 't); coq_lxor : ('t -> 't -> 't) }

  (** val digits : 'a1 coq_Ops -> positive **)

  let digits ops0 =
    ops0.digits

  (** val zdigits : 'a1 coq_Ops -> 'a1 **)

  let zdigits ops0 =
    ops0.zdigits

  (** val to_Z : 'a1 coq_Ops -> 'a1 -> z **)

  let to_Z ops0 =
    ops0.to_Z

  (** val of_pos : 'a1 coq_Ops -> positive -> n * 'a1 **)

  let of_pos ops0 =
    ops0.of_pos

  (** val head0 : 'a1 coq_Ops -> 'a1 -> 'a1 **)

  let head0 ops0 =
    ops0.head0

  (** val tail0 : 'a1 coq_Ops -> 'a1 -> 'a1 **)

  let tail0 ops0 =
    ops0.tail0

  (** val zero : 'a1 coq_Ops -> 'a1 **)

  let zero ops0 =
    ops0.zero

  (** val one : 'a1 coq_Ops -> 'a1 **)

  let one ops0 =
    ops0.one

  (** val minus_one : 'a1 coq_Ops -> 'a1 **)

  let minus_one ops0 =
    ops0.minus_one

  (** val compare : 'a1 coq_Ops -> 'a1 -> 'a1 -> comparison **)

  let compare ops0 =
    ops0.compare

  (** val eq0 : 'a1 coq_Ops -> 'a1 -> bool **)

  let eq0 ops0 =
    ops0.eq0

  (** val opp_c : 'a1 coq_Ops -> 'a1 -> 'a1 Uint63.carry **)

  let opp_c ops0 =
    ops0.opp_c

  (** val opp : 'a1 coq_Ops -> 'a1 -> 'a1 **)

  let opp ops0 =
    ops0.opp

  (** val opp_carry : 'a1 coq_Ops -> 'a1 -> 'a1 **)

  let opp_carry ops0 =
    ops0.opp_carry

  (** val succ_c : 'a1 coq_Ops -> 'a1 -> 'a1 Uint63.carry **)

  let succ_c ops0 =
    ops0.succ_c

  (** val add_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry **)

  let add_c ops0 =
    ops0.add_c

  (** val add_carry_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry **)

  let add_carry_c ops0 =
    ops0.add_carry_c

  (** val succ : 'a1 coq_Ops -> 'a1 -> 'a1 **)

  let succ ops0 =
    ops0.succ

  (** val add : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let add ops0 =
    ops0.add

  (** val add_carry : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let add_carry ops0 =
    ops0.add_carry

  (** val pred_c : 'a1 coq_Ops -> 'a1 -> 'a1 Uint63.carry **)

  let pred_c ops0 =
    ops0.pred_c

  (** val sub_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry **)

  let sub_c ops0 =
    ops0.sub_c

  (** val sub_carry_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry **)

  let sub_carry_c ops0 =
    ops0.sub_carry_c

  (** val pred : 'a1 coq_Ops -> 'a1 -> 'a1 **)

  let pred ops0 =
    ops0.pred

  (** val sub : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let sub ops0 =
    ops0.sub

  (** val sub_carry : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let sub_carry ops0 =
    ops0.sub_carry

  (** val mul_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 zn2z **)

  let mul_c ops0 =
    ops0.mul_c

  (** val mul : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let mul ops0 =
    ops0.mul

  (** val square_c : 'a1 coq_Ops -> 'a1 -> 'a1 zn2z **)

  let square_c ops0 =
    ops0.square_c

  (** val div21 : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 -> 'a1 * 'a1 **)

  let div21 ops0 =
    ops0.div21

  (** val div_gt : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 * 'a1 **)

  let div_gt ops0 =
    ops0.div_gt

  (** val modulo_gt : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let modulo_gt ops0 =
    ops0.modulo_gt

  (** val gcd_gt : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let gcd_gt ops0 =
    ops0.gcd_gt

  (** val add_mul_div : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 -> 'a1 **)

  let add_mul_div ops0 =
    ops0.add_mul_div

  (** val pos_mod : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let pos_mod ops0 =
    ops0.pos_mod

  (** val is_even : 'a1 coq_Ops -> 'a1 -> bool **)

  let is_even ops0 =
    ops0.is_even

  (** val sqrt2 : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 * 'a1 Uint63.carry **)

  let sqrt2 ops0 =
    ops0.sqrt2

  (** val coq_lor : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let coq_lor ops0 =
    ops0.coq_lor

  (** val coq_land : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let coq_land ops0 =
    ops0.coq_land

  (** val coq_lxor : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 **)

  let coq_lxor ops0 =
    ops0.coq_lxor

  (** val coq_WO : 'a1 coq_Ops -> 'a1 -> 'a1 zn2z **)

  let coq_WO ops0 =
    let eq1 = ops0.eq0 in
    let zero1 = ops0.zero in (fun h -> if eq1 h then W0 else WW (h, zero1))

  (** val coq_OW : 'a1 coq_Ops -> 'a1 -> 'a1 zn2z **)

  let coq_OW ops0 =
    let eq1 = ops0.eq0 in
    let zero1 = ops0.zero in (fun l -> if eq1 l then W0 else WW (zero1, l))

  (** val coq_WW : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 zn2z **)

  let coq_WW ops0 =
    let eq1 = ops0.eq0 in
    let zero1 = ops0.zero in
    (fun h l ->
    if eq1 h then if eq1 l then W0 else WW (zero1, l) else WW (h, l))
 end

(** val pdigits : positive **)

let pdigits =
  XI (XI (XI (XI (XI XH))))

(** val positive_to_int_rec : int -> positive -> n * Uint63.t **)

let rec positive_to_int_rec n0 p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ((Npos p), (Uint63.of_int (0))))
    (fun n1 ->
    match p with
    | XI p0 ->
      let (n2, i) = positive_to_int_rec n1 p0 in
      (n2, (add0 (lsl0 i (Uint63.of_int (1))) (Uint63.of_int (1))))
    | XO p0 ->
      let (n2, i) = positive_to_int_rec n1 p0 in
      (n2, (lsl0 i (Uint63.of_int (1))))
    | XH -> (N0, (Uint63.of_int (1))))
    n0

(** val positive_to_int : positive -> n * Uint63.t **)

let positive_to_int =
  positive_to_int_rec size

(** val mulc_WW : Uint63.t -> Uint63.t -> Uint63.t zn2z **)

let mulc_WW x y =
  let (h, l) = mulc x y in
  if is_zero h then if is_zero l then W0 else WW (h, l) else WW (h, l)

(** val pos_mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let pos_mod0 p x =
  if leb0 p digits then let p0 = sub0 digits p in lsr0 (lsl0 x p0) p0 else x

(** val int_ops : Uint63.t ZnZ.coq_Ops **)

let int_ops =
  { ZnZ.digits = pdigits; ZnZ.zdigits = digits; ZnZ.to_Z = to_Z; ZnZ.of_pos =
    positive_to_int; ZnZ.head0 = head0; ZnZ.tail0 = tail0; ZnZ.zero =
    (Uint63.of_int (0)); ZnZ.one = (Uint63.of_int (1)); ZnZ.minus_one =
    max_int; ZnZ.compare = compare0; ZnZ.eq0 = is_zero; ZnZ.opp_c = oppc;
    ZnZ.opp = opp0; ZnZ.opp_carry = oppcarry; ZnZ.succ_c = succc; ZnZ.add_c =
    addc; ZnZ.add_carry_c = addcarryc; ZnZ.succ = succ0; ZnZ.add = add0;
    ZnZ.add_carry = addcarry; ZnZ.pred_c = predc; ZnZ.sub_c = subc;
    ZnZ.sub_carry_c = subcarryc; ZnZ.pred = pred0; ZnZ.sub = sub0;
    ZnZ.sub_carry = subcarry; ZnZ.mul_c = mulc_WW; ZnZ.mul = mul0;
    ZnZ.square_c = (fun x -> mulc_WW x x); ZnZ.div21 = diveucl_21;
    ZnZ.div_gt = diveucl; ZnZ.div = diveucl; ZnZ.modulo_gt = mod0;
    ZnZ.modulo = mod0; ZnZ.gcd_gt = gcd; ZnZ.gcd = gcd; ZnZ.add_mul_div =
    addmuldiv; ZnZ.pos_mod = pos_mod0; ZnZ.is_even = is_even; ZnZ.sqrt2 =
    sqrt2; ZnZ.sqrt = sqrt; ZnZ.coq_lor = lor0; ZnZ.coq_land = land0;
    ZnZ.coq_lxor = lxor0 }

module Uint63Cyclic =
 struct
  type t = Uint63.t

  (** val ops : Uint63.t ZnZ.coq_Ops **)

  let ops =
    int_ops
 end

(** val ww_1 : 'a1 -> 'a1 -> 'a1 zn2z **)

let ww_1 w_0 w_1 =
  WW (w_0, w_1)

(** val ww_Bm1 : 'a1 -> 'a1 zn2z **)

let ww_Bm1 w_Bm1 =
  WW (w_Bm1, w_Bm1)

(** val double_WW :
    ('a1 -> 'a1 -> 'a1 zn2z) -> int -> 'a1 word -> 'a1 word -> 'a1 word **)

let double_WW w_WW n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic w_WW)
    (fun _ h l ->
    match Obj.magic h with
    | W0 ->
      (match Obj.magic l with
       | W0 -> Obj.magic W0
       | WW (_, _) -> Obj.magic (WW (h, l)))
    | WW (_, _) -> Obj.magic (WW (h, l)))
    n0

(** val extend_aux : int -> 'a1 zn2z -> 'a1 word **)

let rec extend_aux n0 x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic x)
    (fun n1 -> Obj.magic (WW ((Obj.magic W0), (extend_aux n1 x))))
    n0

(** val extend : ('a1 -> 'a1 zn2z) -> int -> 'a1 -> 'a1 word **)

let extend w_0W n0 x =
  let r = w_0W x in
  (match r with
   | W0 -> Obj.magic W0
   | WW (_, _) -> extend_aux n0 r)

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Cons of 'a * 'a stream

(** val hd : 'a1 stream -> 'a1 **)

let hd x =
  let Cons (a, _) = Lazy.force x in a

(** val tl : 'a1 stream -> 'a1 stream **)

let tl x =
  let Cons (_, s) = Lazy.force x in s

(** val memo_make : (int -> 'a1) -> int -> 'a1 stream **)

let rec memo_make f n0 =
  lazy (Cons ((f n0), (memo_make f (Stdlib.Int.succ n0))))

(** val memo_list : (int -> 'a1) -> 'a1 stream **)

let memo_list f =
  memo_make f 0

(** val memo_get : int -> 'a1 stream -> 'a1 **)

let rec memo_get n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> hd l)
    (fun n1 -> memo_get n1 (tl l))
    n0

type 'a memo_val =
| Memo_mval of int * 'a

(** val is_eq : int -> int -> bool **)

let rec is_eq n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      m)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m1 -> is_eq n1 m1)
      m)
    n0

(** val memo_get_val : (int -> 'a1) -> int -> 'a1 memo_val -> 'a1 **)

let memo_get_val f n0 = function
| Memo_mval (m, x) -> if is_eq n0 m then x else f n0

(** val dmemo_list : (int -> 'a1) -> 'a1 memo_val stream **)

let dmemo_list f =
  let mf = fun n0 -> Memo_mval (n0, (f n0)) in memo_list mf

(** val dmemo_get : (int -> 'a1) -> int -> 'a1 memo_val stream -> 'a1 **)

let dmemo_get f n0 l =
  memo_get_val f n0 (memo_get n0 l)

(** val w_2 : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 **)

let w_2 w_1 w_add =
  w_add w_1 w_1

(** val double_mul_add_n1 :
    'a1 -> ('a1 -> 'a1 -> 'a1 zn2z) -> ('a1 -> 'a1 zn2z) -> ('a1 -> 'a1 ->
    'a1 -> 'a1 * 'a1) -> int -> 'a1 word -> 'a1 -> 'a1 -> 'a1 * 'a1 word **)

let rec double_mul_add_n1 w_0 w_WW w_0W w_mul_add n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic w_mul_add)
    (fun n1 ->
    let mul_add = double_mul_add_n1 w_0 w_WW w_0W w_mul_add n1 in
    (fun x y r ->
    match Obj.magic x with
    | W0 -> (w_0, (extend w_0W n1 r))
    | WW (xh, xl) ->
      let (rl, l) = mul_add xl y r in
      let (rh, h) = mul_add xh y rl in (rh, (double_WW w_WW n1 h l))))
    n0

(** val ww_is_even : ('a1 -> bool) -> 'a1 zn2z -> bool **)

let ww_is_even w_is_even = function
| W0 -> true
| WW (_, xl) -> w_is_even xl

(** val split : 'a1 -> 'a1 zn2z -> 'a1 * 'a1 **)

let split w_0 = function
| W0 -> (w_0, w_0)
| WW (h, l) -> (h, l)

(** val ww_is_zero :
    ('a1 zn2z -> 'a1 zn2z -> comparison) -> 'a1 zn2z -> bool **)

let ww_is_zero ww_compare x =
  match ww_compare W0 x with
  | Eq -> true
  | _ -> false

(** val ww_head1 :
    ('a1 -> bool) -> ('a1 zn2z -> 'a1 zn2z) -> ('a1 zn2z -> 'a1 zn2z) -> 'a1
    zn2z -> 'a1 zn2z **)

let ww_head1 w_is_even ww_pred ww_head0 x =
  let p = ww_head0 x in if ww_is_even w_is_even p then p else ww_pred p

(** val high : 'a1 -> int -> 'a1 word -> 'a1 **)

let rec high w_0 n0 a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic a)
    (fun n1 ->
    match Obj.magic a with
    | W0 -> w_0
    | WW (h, _) -> high w_0 n1 h)
    n0

(** val lor1 : 'a1 ZnZ.coq_Ops -> 'a1 zn2z -> 'a1 zn2z -> 'a1 zn2z **)

let lor1 ops0 x y =
  match x with
  | W0 -> y
  | WW (hx, lx) ->
    (match y with
     | W0 -> x
     | WW (hy, ly) -> WW ((ops0.ZnZ.coq_lor hx hy), (ops0.ZnZ.coq_lor lx ly)))

(** val land1 : 'a1 ZnZ.coq_Ops -> 'a1 zn2z -> 'a1 zn2z -> 'a1 zn2z **)

let land1 ops0 x y =
  match x with
  | W0 -> W0
  | WW (hx, lx) ->
    (match y with
     | W0 -> W0
     | WW (hy, ly) ->
       WW ((ops0.ZnZ.coq_land hx hy), (ops0.ZnZ.coq_land lx ly)))

(** val lxor1 : 'a1 ZnZ.coq_Ops -> 'a1 zn2z -> 'a1 zn2z -> 'a1 zn2z **)

let lxor1 ops0 x y =
  match x with
  | W0 -> y
  | WW (hx, lx) ->
    (match y with
     | W0 -> x
     | WW (hy, ly) ->
       WW ((ops0.ZnZ.coq_lxor hx hy), (ops0.ZnZ.coq_lxor lx ly)))

(** val mk_zn2z_ops : 'a1 ZnZ.coq_Ops -> 'a1 zn2z ZnZ.coq_Ops **)

let mk_zn2z_ops ops0 =
  let w_digits = ops0.ZnZ.digits in
  let w_zdigits = ops0.ZnZ.zdigits in
  let w_to_Z = ops0.ZnZ.to_Z in
  let w_of_pos = ops0.ZnZ.of_pos in
  let w_head0 = ops0.ZnZ.head0 in
  let w_tail0 = ops0.ZnZ.tail0 in
  let w_0 = ops0.ZnZ.zero in
  let w_1 = ops0.ZnZ.one in
  let w_Bm1 = ops0.ZnZ.minus_one in
  let w_compare = ops0.ZnZ.compare in
  let w_eq0 = ops0.ZnZ.eq0 in
  let w_opp_c = ops0.ZnZ.opp_c in
  let w_opp = ops0.ZnZ.opp in
  let w_opp_carry = ops0.ZnZ.opp_carry in
  let w_succ_c = ops0.ZnZ.succ_c in
  let w_add_c = ops0.ZnZ.add_c in
  let w_add_carry_c = ops0.ZnZ.add_carry_c in
  let w_succ = ops0.ZnZ.succ in
  let w_add = ops0.ZnZ.add in
  let w_add_carry = ops0.ZnZ.add_carry in
  let w_pred_c = ops0.ZnZ.pred_c in
  let w_sub_c = ops0.ZnZ.sub_c in
  let w_sub_carry_c = ops0.ZnZ.sub_carry_c in
  let w_pred = ops0.ZnZ.pred in
  let w_sub = ops0.ZnZ.sub in
  let w_sub_carry = ops0.ZnZ.sub_carry in
  let w_mul_c = ops0.ZnZ.mul_c in
  let w_mul = ops0.ZnZ.mul in
  let w_square_c = ops0.ZnZ.square_c in
  let w_div21 = ops0.ZnZ.div21 in
  let w_div_gt = ops0.ZnZ.div_gt in
  let w_mod_gt = ops0.ZnZ.modulo_gt in
  let w_gcd_gt = ops0.ZnZ.gcd_gt in
  let w_add_mul_div = ops0.ZnZ.add_mul_div in
  let w_pos_mod = ops0.ZnZ.pos_mod in
  let w_is_even = ops0.ZnZ.is_even in
  let w_sqrt2 = ops0.ZnZ.sqrt2 in
  let wB = base w_digits in
  let w_Bm2 = w_pred w_Bm1 in
  let ww_2 = ww_1 w_0 w_1 in
  let ww_Bm2 = ww_Bm1 w_Bm1 in
  let w_add2 = fun a b ->
    match w_add_c a b with
    | Uint63.C0 p -> WW (w_0, p)
    | Uint63.C1 p -> WW (w_1, p)
  in
  let _ww_digits = XO w_digits in
  let _ww_zdigits = w_add2 w_zdigits w_zdigits in
  let to_Z0 = zn2z_to_Z wB w_to_Z in
  let w_W0 = ZnZ.coq_WO ops0 in
  let w_0W = ZnZ.coq_OW ops0 in
  let w_WW = ZnZ.coq_WW ops0 in
  let ww_of_pos = fun p ->
    let (n0, l) = w_of_pos p in
    (match n0 with
     | N0 -> (N0, (WW (w_0, l)))
     | Npos ph -> let (n1, h) = w_of_pos ph in (n1, (w_WW h l)))
  in
  let head1 = fun x ->
    match x with
    | W0 -> _ww_zdigits
    | WW (xh, xl) ->
      (match w_compare w_0 xh with
       | Eq -> w_add2 w_zdigits (w_head0 xl)
       | _ -> w_0W (w_head0 xh))
  in
  let tail1 = fun x ->
    match x with
    | W0 -> _ww_zdigits
    | WW (xh, xl) ->
      (match w_compare w_0 xl with
       | Eq -> w_add2 w_zdigits (w_tail0 xh)
       | _ -> w_0W (w_tail0 xl))
  in
  let compare1 = fun x y ->
    match x with
    | W0 ->
      (match y with
       | W0 -> Eq
       | WW (yh, yl) ->
         (match w_compare w_0 yh with
          | Eq -> w_compare w_0 yl
          | _ -> Lt))
    | WW (xh, xl) ->
      (match y with
       | W0 -> (match w_compare xh w_0 with
                | Eq -> w_compare xl w_0
                | _ -> Gt)
       | WW (yh, yl) ->
         (match w_compare xh yh with
          | Eq -> w_compare xl yl
          | x0 -> x0))
  in
  let eq1 = fun x -> match x with
                     | W0 -> true
                     | WW (_, _) -> false in
  let opp_c0 = fun x ->
    match x with
    | W0 -> Uint63.C0 W0
    | WW (xh, xl) ->
      (match w_opp_c xl with
       | Uint63.C0 _ ->
         (match w_opp_c xh with
          | Uint63.C0 _ -> Uint63.C0 W0
          | Uint63.C1 h -> Uint63.C1 (WW (h, w_0)))
       | Uint63.C1 l -> Uint63.C1 (WW ((w_opp_carry xh), l)))
  in
  let opp1 = fun x ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      (match w_opp_c xl with
       | Uint63.C0 _ -> WW ((w_opp xh), w_0)
       | Uint63.C1 l -> WW ((w_opp_carry xh), l))
  in
  let opp_carry0 = fun x ->
    match x with
    | W0 -> ww_Bm2
    | WW (xh, xl) -> w_WW (w_opp_carry xh) (w_opp_carry xl)
  in
  let succ_c0 = fun x ->
    match x with
    | W0 -> Uint63.C0 ww_2
    | WW (xh, xl) ->
      (match w_succ_c xl with
       | Uint63.C0 l -> Uint63.C0 (WW (xh, l))
       | Uint63.C1 _ ->
         (match w_succ_c xh with
          | Uint63.C0 h -> Uint63.C0 (WW (h, w_0))
          | Uint63.C1 _ -> Uint63.C1 W0))
  in
  let add_c0 = fun x y ->
    match x with
    | W0 -> Uint63.C0 y
    | WW (xh, xl) ->
      (match y with
       | W0 -> Uint63.C0 x
       | WW (yh, yl) ->
         (match w_add_c xl yl with
          | Uint63.C0 l ->
            (match w_add_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))
          | Uint63.C1 l ->
            (match w_add_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))))
  in
  let add_carry_c0 = fun x y ->
    match x with
    | W0 ->
      (match y with
       | W0 -> Uint63.C0 ww_2
       | WW (yh, yl) ->
         (match w_succ_c yl with
          | Uint63.C0 l -> Uint63.C0 (WW (yh, l))
          | Uint63.C1 _ ->
            (match w_succ_c yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, w_0))
             | Uint63.C1 _ -> Uint63.C1 W0)))
    | WW (xh, xl) ->
      (match y with
       | W0 ->
         (match w_succ_c xl with
          | Uint63.C0 l -> Uint63.C0 (WW (xh, l))
          | Uint63.C1 _ ->
            (match w_succ_c xh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, w_0))
             | Uint63.C1 _ -> Uint63.C1 W0))
       | WW (yh, yl) ->
         (match w_add_carry_c xl yl with
          | Uint63.C0 l ->
            (match w_add_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))
          | Uint63.C1 l ->
            (match w_add_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))))
  in
  let succ1 = fun x ->
    match x with
    | W0 -> ww_2
    | WW (xh, xl) ->
      (match w_succ_c xl with
       | Uint63.C0 l -> WW (xh, l)
       | Uint63.C1 _ -> w_W0 (w_succ xh))
  in
  let add1 = fun x y ->
    match x with
    | W0 -> y
    | WW (xh, xl) ->
      (match y with
       | W0 -> x
       | WW (yh, yl) ->
         (match w_add_c xl yl with
          | Uint63.C0 l -> WW ((w_add xh yh), l)
          | Uint63.C1 l -> WW ((w_add_carry xh yh), l)))
  in
  let add_carry0 = fun x y ->
    match x with
    | W0 ->
      (match y with
       | W0 -> ww_2
       | WW (yh, yl) ->
         (match w_succ_c yl with
          | Uint63.C0 l -> WW (yh, l)
          | Uint63.C1 _ -> w_W0 (w_succ yh)))
    | WW (xh, xl) ->
      (match y with
       | W0 ->
         (match w_succ_c xl with
          | Uint63.C0 l -> WW (xh, l)
          | Uint63.C1 _ -> w_W0 (w_succ xh))
       | WW (yh, yl) ->
         (match w_add_carry_c xl yl with
          | Uint63.C0 l -> WW ((w_add xh yh), l)
          | Uint63.C1 l -> WW ((w_add_carry xh yh), l)))
  in
  let pred_c0 = fun x ->
    match x with
    | W0 -> Uint63.C1 ww_Bm2
    | WW (xh, xl) ->
      (match w_pred_c xl with
       | Uint63.C0 l -> Uint63.C0 (w_WW xh l)
       | Uint63.C1 _ ->
         (match w_pred_c xh with
          | Uint63.C0 h -> Uint63.C0 (WW (h, w_Bm1))
          | Uint63.C1 _ -> Uint63.C1 ww_Bm2))
  in
  let sub_c0 = fun x y ->
    match y with
    | W0 -> Uint63.C0 x
    | WW (yh, yl) ->
      (match x with
       | W0 ->
         (match w_opp_c yl with
          | Uint63.C0 _ ->
            (match w_opp_c yh with
             | Uint63.C0 _ -> Uint63.C0 W0
             | Uint63.C1 h -> Uint63.C1 (WW (h, w_0)))
          | Uint63.C1 l -> Uint63.C1 (WW ((w_opp_carry yh), l)))
       | WW (xh, xl) ->
         (match w_sub_c xl yl with
          | Uint63.C0 l ->
            (match w_sub_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (w_WW h l)
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))
          | Uint63.C1 l ->
            (match w_sub_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))))
  in
  let sub_carry_c0 = fun x y ->
    match y with
    | W0 ->
      (match x with
       | W0 -> Uint63.C1 ww_Bm2
       | WW (xh, xl) ->
         (match w_pred_c xl with
          | Uint63.C0 l -> Uint63.C0 (w_WW xh l)
          | Uint63.C1 _ ->
            (match w_pred_c xh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, w_Bm1))
             | Uint63.C1 _ -> Uint63.C1 ww_Bm2)))
    | WW (yh, yl) ->
      (match x with
       | W0 -> Uint63.C1 (w_WW (w_opp_carry yh) (w_opp_carry yl))
       | WW (xh, xl) ->
         (match w_sub_carry_c xl yl with
          | Uint63.C0 l ->
            (match w_sub_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (w_WW h l)
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))
          | Uint63.C1 l ->
            (match w_sub_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (w_WW h l)
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))))
  in
  let pred2 = fun x ->
    match x with
    | W0 -> ww_Bm2
    | WW (xh, xl) ->
      (match w_pred_c xl with
       | Uint63.C0 l -> w_WW xh l
       | Uint63.C1 _ -> WW ((w_pred xh), w_Bm1))
  in
  let sub1 = fun x y ->
    match y with
    | W0 -> x
    | WW (yh, yl) ->
      (match x with
       | W0 ->
         (match w_opp_c yl with
          | Uint63.C0 _ -> WW ((w_opp yh), w_0)
          | Uint63.C1 l -> WW ((w_opp_carry yh), l))
       | WW (xh, xl) ->
         (match w_sub_c xl yl with
          | Uint63.C0 l -> w_WW (w_sub xh yh) l
          | Uint63.C1 l -> WW ((w_sub_carry xh yh), l)))
  in
  let sub_carry0 = fun x y ->
    match y with
    | W0 ->
      (match x with
       | W0 -> ww_Bm2
       | WW (xh, xl) ->
         (match w_pred_c xl with
          | Uint63.C0 l -> w_WW xh l
          | Uint63.C1 _ -> WW ((w_pred xh), w_Bm1)))
    | WW (yh, yl) ->
      (match x with
       | W0 -> w_WW (w_opp_carry yh) (w_opp_carry yl)
       | WW (xh, xl) ->
         (match w_sub_carry_c xl yl with
          | Uint63.C0 l -> w_WW (w_sub xh yh) l
          | Uint63.C1 l -> w_WW (w_sub_carry xh yh) l))
  in
  let mul_c0 = fun x y ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      (match y with
       | W0 -> W0
       | WW (yh, yl) ->
         let hh = w_mul_c xh yh in
         let ll = w_mul_c xl yl in
         (match add_c0 (w_mul_c xh yl) (w_mul_c xl yh) with
          | Uint63.C0 cc ->
            (match cc with
             | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
             | WW (cch, ccl) ->
               (match add_c0 (w_W0 ccl) ll with
                | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))
          | Uint63.C1 cc ->
            (match cc with
             | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
             | WW (cch, ccl) ->
               (match add_c0 (w_W0 ccl) ll with
                | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_1 cch)), l)))))
  in
  let mul1 = fun x y ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      (match y with
       | W0 -> W0
       | WW (yh, yl) ->
         let ccl = w_add (w_mul xh yl) (w_mul xl yh) in
         add1 (w_W0 ccl) (w_mul_c xl yl))
  in
  let square_c0 = fun x ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      let hh = w_square_c xh in
      let ll = w_square_c xl in
      let xhxl = w_mul_c xh xl in
      (match add_c0 xhxl xhxl with
       | Uint63.C0 cc ->
         (match cc with
          | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
          | WW (cch, ccl) ->
            (match add_c0 (w_W0 ccl) ll with
             | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
             | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))
       | Uint63.C1 cc ->
         (match cc with
          | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
          | WW (cch, ccl) ->
            (match add_c0 (w_W0 ccl) ll with
             | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
             | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_1 cch)), l))))
  in
  let div32 = fun a1 a2 a3 b1 b2 ->
    match w_compare a1 b1 with
    | Eq ->
      (match w_add_c a3 b2 with
       | Uint63.C0 l ->
         (match w_add_c (w_sub a2 b2) b1 with
          | Uint63.C0 h ->
            (w_Bm2,
              (match w_add_c l b2 with
               | Uint63.C0 l0 -> WW ((w_add h b1), l0)
               | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
          | Uint63.C1 h -> (w_Bm1, (w_WW h l)))
       | Uint63.C1 l ->
         (match w_add_carry_c (w_sub a2 b2) b1 with
          | Uint63.C0 h ->
            (w_Bm2,
              (match w_add_c l b2 with
               | Uint63.C0 l0 -> WW ((w_add h b1), l0)
               | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
          | Uint63.C1 h -> (w_Bm1, (w_WW h l))))
    | Lt ->
      let (q, r) = w_div21 a1 a2 b1 in
      (match sub_c0 (w_WW r a3) (w_mul_c q b2) with
       | Uint63.C0 r1 -> (q, r1)
       | Uint63.C1 r1 ->
         let q0 = w_pred q in
         (match r1 with
          | W0 ->
            ((w_pred q0),
              (match w_add_c b2 b2 with
               | Uint63.C0 l -> WW ((w_add b1 b1), l)
               | Uint63.C1 l -> WW ((w_add_carry b1 b1), l)))
          | WW (xh, xl) ->
            (match w_add_c xl b2 with
             | Uint63.C0 l ->
               (match w_add_c xh b1 with
                | Uint63.C0 h ->
                  ((w_pred q0),
                    (match w_add_c l b2 with
                     | Uint63.C0 l0 -> WW ((w_add h b1), l0)
                     | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
                | Uint63.C1 h -> (q0, (w_WW h l)))
             | Uint63.C1 l ->
               (match w_add_carry_c xh b1 with
                | Uint63.C0 h ->
                  ((w_pred q0),
                    (match w_add_c l b2 with
                     | Uint63.C0 l0 -> WW ((w_add h b1), l0)
                     | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
                | Uint63.C1 h -> (q0, (w_WW h l))))))
    | Gt -> (w_0, W0)
  in
  let div22 = fun a1 a2 b ->
    match a1 with
    | W0 ->
      (match compare1 a2 b with
       | Eq -> (ww_2, W0)
       | Lt -> (W0, a2)
       | Gt -> (ww_2, (sub1 a2 b)))
    | WW (a1h, a1l) ->
      (match a2 with
       | W0 ->
         (match b with
          | W0 -> (W0, W0)
          | WW (b1, b2) ->
            let (q1, r) = div32 a1h a1l w_0 b1 b2 in
            (match r with
             | W0 -> ((WW (q1, w_0)), W0)
             | WW (r1, r2) ->
               let (q2, s) = div32 r1 r2 w_0 b1 b2 in ((WW (q1, q2)), s)))
       | WW (a2h, a2l) ->
         (match b with
          | W0 -> (W0, W0)
          | WW (b1, b2) ->
            let (q1, r) = div32 a1h a1l a2h b1 b2 in
            (match r with
             | W0 -> ((WW (q1, w_0)), (w_0W a2l))
             | WW (r1, r2) ->
               let (q2, s) = div32 r1 r2 a2l b1 b2 in ((WW (q1, q2)), s))))
  in
  let low = fun p -> match p with
                     | W0 -> w_0
                     | WW (_, p1) -> p1 in
  let add_mul_div0 = fun p x y ->
    let zdigits0 = w_0W w_zdigits in
    (match x with
     | W0 ->
       (match y with
        | W0 -> W0
        | WW (yh, yl) ->
          (match compare1 p zdigits0 with
           | Eq -> w_0W yh
           | Lt -> w_0W (w_add_mul_div (low p) w_0 yh)
           | Gt ->
             let n0 = low (sub1 p zdigits0) in
             w_WW (w_add_mul_div n0 w_0 yh) (w_add_mul_div n0 yh yl)))
     | WW (xh, xl) ->
       (match y with
        | W0 ->
          (match compare1 p zdigits0 with
           | Eq -> w_W0 xl
           | Lt ->
             w_WW (w_add_mul_div (low p) xh xl) (w_add_mul_div (low p) xl w_0)
           | Gt ->
             let n0 = low (sub1 p zdigits0) in w_W0 (w_add_mul_div n0 xl w_0))
        | WW (yh, yl) ->
          (match compare1 p zdigits0 with
           | Eq -> w_WW xl yh
           | Lt ->
             w_WW (w_add_mul_div (low p) xh xl) (w_add_mul_div (low p) xl yh)
           | Gt ->
             let n0 = low (sub1 p zdigits0) in
             w_WW (w_add_mul_div n0 xl yh) (w_add_mul_div n0 yh yl))))
  in
  let div_gt0 = fun a b ->
    match a with
    | W0 -> (W0, W0)
    | WW (ah, al) ->
      (match b with
       | W0 -> (W0, W0)
       | WW (bh, bl) ->
         if w_eq0 ah
         then let (q, r) = w_div_gt al bl in ((WW (w_0, q)), (w_0W r))
         else (match w_compare w_0 bh with
               | Eq ->
                 let (q, r) =
                   let p = w_head0 bl in
                   (match w_compare p w_0 with
                    | Gt ->
                      let b2p = w_add_mul_div p bl w_0 in
                      let ha = high w_0 (Stdlib.Int.succ 0) (Obj.magic a) in
                      let k = w_sub w_zdigits p in
                      let lsr_n = w_add_mul_div k w_0 in
                      let r0 = w_add_mul_div p w_0 ha in
                      (match a with
                       | W0 ->
                         let (qh, rh) =
                           w_div21 r0 (w_add_mul_div p w_0 w_0) b2p
                         in
                         let (ql, rl) =
                           w_div21 rh (w_add_mul_div p w_0 w_0) b2p
                         in
                         let q = w_WW qh ql in (q, (lsr_n rl))
                       | WW (h, l) ->
                         let (qh, rh) = w_div21 r0 (w_add_mul_div p h l) b2p
                         in
                         let (ql, rl) = w_div21 rh (w_add_mul_div p l w_0) b2p
                         in
                         let q = w_WW qh ql in (q, (lsr_n rl)))
                    | _ ->
                      (match a with
                       | W0 ->
                         let (qh, rh) = w_div21 w_0 w_0 bl in
                         let (ql, rl) = w_div21 rh w_0 bl in
                         ((w_WW qh ql), rl)
                       | WW (h, l) ->
                         let (qh, rh) = w_div21 w_0 h bl in
                         let (ql, rl) = w_div21 rh l bl in ((w_WW qh ql), rl)))
                 in
                 (q, (w_0W r))
               | Lt ->
                 let p = w_head0 bh in
                 (match w_compare p w_0 with
                  | Gt ->
                    let b1 = w_add_mul_div p bh bl in
                    let b2 = w_add_mul_div p bl w_0 in
                    let a1 = w_add_mul_div p w_0 ah in
                    let a2 = w_add_mul_div p ah al in
                    let a3 = w_add_mul_div p al w_0 in
                    let (q, r) = div32 a1 a2 a3 b1 b2 in
                    ((WW (w_0, q)),
                    (add_mul_div0
                      (match w_0W p with
                       | W0 -> _ww_zdigits
                       | WW (yh, yl) ->
                         (match _ww_zdigits with
                          | W0 ->
                            (match w_opp_c yl with
                             | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                             | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                          | WW (xh, xl) ->
                            (match w_sub_c xl yl with
                             | Uint63.C0 l -> w_WW (w_sub xh yh) l
                             | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
                      W0 r))
                  | _ ->
                    (ww_2,
                      (match w_sub_c al bl with
                       | Uint63.C0 l -> w_WW (w_sub ah bh) l
                       | Uint63.C1 l -> WW ((w_sub_carry ah bh), l))))
               | Gt -> (W0, W0)))
  in
  let div1 = fun a b ->
    match compare1 a b with
    | Eq -> (ww_2, W0)
    | Lt -> (W0, a)
    | Gt -> div_gt0 a b
  in
  let mod_gt = fun a b ->
    match a with
    | W0 -> W0
    | WW (ah, al) ->
      (match b with
       | W0 -> W0
       | WW (bh, bl) ->
         if w_eq0 ah
         then w_0W (w_mod_gt al bl)
         else (match w_compare w_0 bh with
               | Eq ->
                 w_0W
                   (let p = w_head0 bl in
                    match w_compare p w_0 with
                    | Gt ->
                      let b2p = w_add_mul_div p bl w_0 in
                      let ha = high w_0 (Stdlib.Int.succ 0) (Obj.magic a) in
                      let k = w_sub w_zdigits p in
                      let lsr_n = w_add_mul_div k w_0 in
                      let r0 = w_add_mul_div p w_0 ha in
                      let r =
                        match a with
                        | W0 ->
                          let (_, y) =
                            w_div21
                              (let (_, y) =
                                 w_div21 r0 (w_add_mul_div p w_0 w_0) b2p
                               in
                               y)
                              (w_add_mul_div p w_0 w_0) b2p
                          in
                          y
                        | WW (h, l) ->
                          let (_, y) =
                            w_div21
                              (let (_, y) =
                                 w_div21 r0 (w_add_mul_div p h l) b2p
                               in
                               y)
                              (w_add_mul_div p l w_0) b2p
                          in
                          y
                      in
                      lsr_n r
                    | _ ->
                      (match a with
                       | W0 ->
                         let (_, y) =
                           w_div21 (let (_, y) = w_div21 w_0 w_0 bl in y) w_0
                             bl
                         in
                         y
                       | WW (h, l) ->
                         let (_, y) =
                           w_div21 (let (_, y) = w_div21 w_0 h bl in y) l bl
                         in
                         y))
               | Lt ->
                 let p = w_head0 bh in
                 (match w_compare p w_0 with
                  | Gt ->
                    let b1 = w_add_mul_div p bh bl in
                    let b2 = w_add_mul_div p bl w_0 in
                    let a1 = w_add_mul_div p w_0 ah in
                    let a2 = w_add_mul_div p ah al in
                    let a3 = w_add_mul_div p al w_0 in
                    let (_, r) = div32 a1 a2 a3 b1 b2 in
                    add_mul_div0
                      (match w_0W p with
                       | W0 -> _ww_zdigits
                       | WW (yh, yl) ->
                         (match _ww_zdigits with
                          | W0 ->
                            (match w_opp_c yl with
                             | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                             | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                          | WW (xh, xl) ->
                            (match w_sub_c xl yl with
                             | Uint63.C0 l -> w_WW (w_sub xh yh) l
                             | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
                      W0 r
                  | _ ->
                    (match w_sub_c al bl with
                     | Uint63.C0 l -> w_WW (w_sub ah bh) l
                     | Uint63.C1 l -> WW ((w_sub_carry ah bh), l)))
               | Gt -> W0))
  in
  let mod_ = fun a b ->
    match compare1 a b with
    | Eq -> W0
    | Lt -> a
    | Gt -> mod_gt a b
  in
  let pos_mod1 = fun p x ->
    let zdigits0 = w_0W w_zdigits in
    (match x with
     | W0 -> W0
     | WW (xh, xl) ->
       (match compare1 p zdigits0 with
        | Eq -> w_WW w_0 xl
        | Lt -> w_WW w_0 (w_pos_mod (low p) xl)
        | Gt ->
          (match compare1 p _ww_zdigits with
           | Lt -> let n0 = low (sub1 p zdigits0) in w_WW (w_pos_mod n0 xh) xl
           | _ -> x)))
  in
  let is_even0 = fun x -> match x with
                          | W0 -> true
                          | WW (_, xl) -> w_is_even xl
  in
  let sqrt3 =
    let wwBm1 = ww_Bm1 w_Bm1 in
    let w_div21c = fun x y z0 ->
      match w_compare x z0 with
      | Eq ->
        (match w_compare y z0 with
         | Eq -> ((Uint63.C1 w_1), w_0)
         | Lt -> ((Uint63.C1 w_0), y)
         | Gt -> ((Uint63.C1 w_1), (w_sub y z0)))
      | Lt -> let (q, r) = w_div21 x y z0 in ((Uint63.C0 q), r)
      | Gt ->
        let x1 = w_sub x z0 in
        let (q, r) = w_div21 x1 y z0 in ((Uint63.C1 q), r)
    in
    let w_div2s = fun x y s ->
      match x with
      | Uint63.C0 x1 ->
        let (q, r) = w_div21c x1 y s in
        (match q with
         | Uint63.C0 q1 ->
           if w_is_even q1
           then ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (w_add_c r s))
         | Uint63.C1 q1 ->
           if w_is_even q1
           then ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (w_add_c r s)))
      | Uint63.C1 x1 ->
        let x2 = w_sub x1 s in
        let (q, r) = w_div21c x2 y s in
        (match q with
         | Uint63.C0 q1 ->
           if w_is_even q1
           then ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (w_add_c r s))
         | Uint63.C1 q1 ->
           if w_is_even q1
           then ((Uint63.C1 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C1 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (w_add_c r s)))
    in
    (fun x y ->
    let (x1, x2) = split w_0 x in
    let (y1, y2) = split w_0 y in
    let (q, r) = w_sqrt2 x1 x2 in
    let (q1, r1) = w_div2s r y1 q in
    (match q1 with
     | Uint63.C0 q2 ->
       let q3 = w_square_c q2 in
       let a = WW (q, q2) in
       (match r1 with
        | Uint63.C0 r2 ->
          (match sub_c0 (WW (r2, y2)) q3 with
           | Uint63.C0 r3 -> (a, (Uint63.C0 r3))
           | Uint63.C1 r3 ->
             let a2 = add_mul_div0 (w_0W w_1) a W0 in
             (match pred_c0 a2 with
              | Uint63.C0 a3 -> ((pred2 a), (add_c0 a3 r3))
              | Uint63.C1 a3 -> ((pred2 a), (Uint63.C0 (add1 a3 r3)))))
        | Uint63.C1 r2 ->
          (match sub_c0 (WW (r2, y2)) q3 with
           | Uint63.C0 r3 -> (a, (Uint63.C1 r3))
           | Uint63.C1 r3 -> (a, (Uint63.C0 r3))))
     | Uint63.C1 _ ->
       let a1 = WW (q, w_Bm1) in
       let a2 = add_mul_div0 (w_0W w_1) a1 wwBm1 in (a1, (add_c0 a2 y))))
  in
  let sqrt0 = fun x ->
    if ww_is_zero compare1 x
    then W0
    else let p = ww_head1 w_is_even pred2 head1 x in
         (match compare1 p W0 with
          | Eq ->
            (match x with
             | W0 -> W0
             | WW (x1, x2) -> WW (w_0, (fst (w_sqrt2 x1 x2))))
          | Lt ->
            (match x with
             | W0 -> W0
             | WW (x1, x2) -> WW (w_0, (fst (w_sqrt2 x1 x2))))
          | Gt ->
            (match add_mul_div0 p x W0 with
             | W0 -> W0
             | WW (x1, x2) ->
               let (r, _) = w_sqrt2 x1 x2 in
               WW (w_0,
               (w_add_mul_div
                 (w_sub w_zdigits
                   (low (add_mul_div0 (pred2 _ww_zdigits) W0 p)))
                 w_0 r))))
  in
  let gcd_gt_fix =
    let rec ww_gcd_gt_aux p cont ah al bh bl =
      match w_compare w_0 bh with
      | Eq ->
        (match w_compare w_0 bl with
         | Eq -> WW (ah, al)
         | Lt ->
           let m =
             let p0 = w_head0 bl in
             (match w_compare p0 w_0 with
              | Gt ->
                let b2p = w_add_mul_div p0 bl w_0 in
                let ha =
                  high w_0 (Stdlib.Int.succ 0) (Obj.magic (WW (ah, al)))
                in
                let k = w_sub w_zdigits p0 in
                let lsr_n = w_add_mul_div k w_0 in
                let r0 = w_add_mul_div p0 w_0 ha in
                let r =
                  let (_, y) =
                    w_div21
                      (let (_, y) = w_div21 r0 (w_add_mul_div p0 ah al) b2p in
                       y)
                      (w_add_mul_div p0 al w_0) b2p
                  in
                  y
                in
                lsr_n r
              | _ ->
                let (_, y) =
                  w_div21 (let (_, y) = w_div21 w_0 ah bl in y) al bl
                in
                y)
           in
           WW (w_0, (w_gcd_gt bl m))
         | Gt -> W0)
      | Lt ->
        let m =
          let p0 = w_head0 bh in
          (match w_compare p0 w_0 with
           | Gt ->
             let b1 = w_add_mul_div p0 bh bl in
             let b2 = w_add_mul_div p0 bl w_0 in
             let a1 = w_add_mul_div p0 w_0 ah in
             let a2 = w_add_mul_div p0 ah al in
             let a3 = w_add_mul_div p0 al w_0 in
             let (_, r) = div32 a1 a2 a3 b1 b2 in
             add_mul_div0
               (match w_0W p0 with
                | W0 -> _ww_zdigits
                | WW (yh, yl) ->
                  (match _ww_zdigits with
                   | W0 ->
                     (match w_opp_c yl with
                      | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                      | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                   | WW (xh, xl) ->
                     (match w_sub_c xl yl with
                      | Uint63.C0 l -> w_WW (w_sub xh yh) l
                      | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
               W0 r
           | _ ->
             (match w_sub_c al bl with
              | Uint63.C0 l -> w_WW (w_sub ah bh) l
              | Uint63.C1 l -> WW ((w_sub_carry ah bh), l)))
        in
        (match m with
         | W0 -> WW (bh, bl)
         | WW (mh, ml) ->
           (match w_compare w_0 mh with
            | Eq ->
              (match w_compare w_0 ml with
               | Eq -> WW (bh, bl)
               | _ ->
                 let r =
                   let p0 = w_head0 ml in
                   (match w_compare p0 w_0 with
                    | Gt ->
                      let b2p = w_add_mul_div p0 ml w_0 in
                      let ha =
                        high w_0 (Stdlib.Int.succ 0) (Obj.magic (WW (bh, bl)))
                      in
                      let k = w_sub w_zdigits p0 in
                      let lsr_n = w_add_mul_div k w_0 in
                      let r0 = w_add_mul_div p0 w_0 ha in
                      let r =
                        let (_, y) =
                          w_div21
                            (let (_, y) =
                               w_div21 r0 (w_add_mul_div p0 bh bl) b2p
                             in
                             y)
                            (w_add_mul_div p0 bl w_0) b2p
                        in
                        y
                      in
                      lsr_n r
                    | _ ->
                      let (_, y) =
                        w_div21 (let (_, y) = w_div21 w_0 bh ml in y) bl ml
                      in
                      y)
                 in
                 WW (w_0, (w_gcd_gt ml r)))
            | Lt ->
              let r =
                let p0 = w_head0 mh in
                (match w_compare p0 w_0 with
                 | Gt ->
                   let b1 = w_add_mul_div p0 mh ml in
                   let b2 = w_add_mul_div p0 ml w_0 in
                   let a1 = w_add_mul_div p0 w_0 bh in
                   let a2 = w_add_mul_div p0 bh bl in
                   let a3 = w_add_mul_div p0 bl w_0 in
                   let (_, r) = div32 a1 a2 a3 b1 b2 in
                   add_mul_div0
                     (match w_0W p0 with
                      | W0 -> _ww_zdigits
                      | WW (yh, yl) ->
                        (match _ww_zdigits with
                         | W0 ->
                           (match w_opp_c yl with
                            | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                            | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                         | WW (xh, xl) ->
                           (match w_sub_c xl yl with
                            | Uint63.C0 l -> w_WW (w_sub xh yh) l
                            | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
                     W0 r
                 | _ ->
                   (match w_sub_c bl ml with
                    | Uint63.C0 l -> w_WW (w_sub bh mh) l
                    | Uint63.C1 l -> WW ((w_sub_carry bh mh), l)))
              in
              (match r with
               | W0 -> m
               | WW (rh, rl) ->
                 (match p with
                  | XI p0 ->
                    ww_gcd_gt_aux p0 (ww_gcd_gt_aux p0 cont) mh ml rh rl
                  | XO p0 ->
                    ww_gcd_gt_aux p0 (ww_gcd_gt_aux p0 cont) mh ml rh rl
                  | XH -> cont mh ml rh rl))
            | Gt -> W0))
      | Gt -> W0
    in ww_gcd_gt_aux
  in
  let gcd_cont = fun xh xl _ yl ->
    match w_compare w_1 yl with
    | Eq -> ww_2
    | _ -> WW (xh, xl)
  in
  let gcd_gt0 = fun a b ->
    match a with
    | W0 -> b
    | WW (ah, al) ->
      (match b with
       | W0 -> a
       | WW (bh, bl) ->
         if w_eq0 ah
         then WW (w_0, (w_gcd_gt al bl))
         else gcd_gt_fix _ww_digits gcd_cont ah al bh bl)
  in
  let gcd0 = fun a b ->
    match compare1 a b with
    | Eq -> a
    | Lt ->
      (match b with
       | W0 -> a
       | WW (ah, al) ->
         (match a with
          | W0 -> b
          | WW (bh, bl) ->
            if w_eq0 ah
            then WW (w_0, (w_gcd_gt al bl))
            else gcd_gt_fix _ww_digits gcd_cont ah al bh bl))
    | Gt ->
      (match a with
       | W0 -> b
       | WW (ah, al) ->
         (match b with
          | W0 -> a
          | WW (bh, bl) ->
            if w_eq0 ah
            then WW (w_0, (w_gcd_gt al bl))
            else gcd_gt_fix _ww_digits gcd_cont ah al bh bl))
  in
  { ZnZ.digits = _ww_digits; ZnZ.zdigits = _ww_zdigits; ZnZ.to_Z = to_Z0;
  ZnZ.of_pos = ww_of_pos; ZnZ.head0 = head1; ZnZ.tail0 = tail1; ZnZ.zero =
  W0; ZnZ.one = ww_2; ZnZ.minus_one = ww_Bm2; ZnZ.compare = compare1;
  ZnZ.eq0 = eq1; ZnZ.opp_c = opp_c0; ZnZ.opp = opp1; ZnZ.opp_carry =
  opp_carry0; ZnZ.succ_c = succ_c0; ZnZ.add_c = add_c0; ZnZ.add_carry_c =
  add_carry_c0; ZnZ.succ = succ1; ZnZ.add = add1; ZnZ.add_carry = add_carry0;
  ZnZ.pred_c = pred_c0; ZnZ.sub_c = sub_c0; ZnZ.sub_carry_c = sub_carry_c0;
  ZnZ.pred = pred2; ZnZ.sub = sub1; ZnZ.sub_carry = sub_carry0; ZnZ.mul_c =
  mul_c0; ZnZ.mul = mul1; ZnZ.square_c = square_c0; ZnZ.div21 = div22;
  ZnZ.div_gt = div_gt0; ZnZ.div = div1; ZnZ.modulo_gt = mod_gt; ZnZ.modulo =
  mod_; ZnZ.gcd_gt = gcd_gt0; ZnZ.gcd = gcd0; ZnZ.add_mul_div = add_mul_div0;
  ZnZ.pos_mod = pos_mod1; ZnZ.is_even = is_even0; ZnZ.sqrt2 = sqrt3;
  ZnZ.sqrt = sqrt0; ZnZ.coq_lor = (lor1 ops0); ZnZ.coq_land = (land1 ops0);
  ZnZ.coq_lxor = (lxor1 ops0) }

(** val mk_zn2z_ops_karatsuba : 'a1 ZnZ.coq_Ops -> 'a1 zn2z ZnZ.coq_Ops **)

let mk_zn2z_ops_karatsuba ops0 =
  let w_digits = ops0.ZnZ.digits in
  let w_zdigits = ops0.ZnZ.zdigits in
  let w_to_Z = ops0.ZnZ.to_Z in
  let w_of_pos = ops0.ZnZ.of_pos in
  let w_head0 = ops0.ZnZ.head0 in
  let w_tail0 = ops0.ZnZ.tail0 in
  let w_0 = ops0.ZnZ.zero in
  let w_1 = ops0.ZnZ.one in
  let w_Bm1 = ops0.ZnZ.minus_one in
  let w_compare = ops0.ZnZ.compare in
  let w_eq0 = ops0.ZnZ.eq0 in
  let w_opp_c = ops0.ZnZ.opp_c in
  let w_opp = ops0.ZnZ.opp in
  let w_opp_carry = ops0.ZnZ.opp_carry in
  let w_succ_c = ops0.ZnZ.succ_c in
  let w_add_c = ops0.ZnZ.add_c in
  let w_add_carry_c = ops0.ZnZ.add_carry_c in
  let w_succ = ops0.ZnZ.succ in
  let w_add = ops0.ZnZ.add in
  let w_add_carry = ops0.ZnZ.add_carry in
  let w_pred_c = ops0.ZnZ.pred_c in
  let w_sub_c = ops0.ZnZ.sub_c in
  let w_sub_carry_c = ops0.ZnZ.sub_carry_c in
  let w_pred = ops0.ZnZ.pred in
  let w_sub = ops0.ZnZ.sub in
  let w_sub_carry = ops0.ZnZ.sub_carry in
  let w_mul_c = ops0.ZnZ.mul_c in
  let w_mul = ops0.ZnZ.mul in
  let w_square_c = ops0.ZnZ.square_c in
  let w_div21 = ops0.ZnZ.div21 in
  let w_div_gt = ops0.ZnZ.div_gt in
  let w_mod_gt = ops0.ZnZ.modulo_gt in
  let w_gcd_gt = ops0.ZnZ.gcd_gt in
  let w_add_mul_div = ops0.ZnZ.add_mul_div in
  let w_pos_mod = ops0.ZnZ.pos_mod in
  let w_is_even = ops0.ZnZ.is_even in
  let w_sqrt2 = ops0.ZnZ.sqrt2 in
  let wB = base w_digits in
  let w_Bm2 = w_pred w_Bm1 in
  let ww_2 = ww_1 w_0 w_1 in
  let ww_Bm2 = ww_Bm1 w_Bm1 in
  let w_add2 = fun a b ->
    match w_add_c a b with
    | Uint63.C0 p -> WW (w_0, p)
    | Uint63.C1 p -> WW (w_1, p)
  in
  let _ww_digits = XO w_digits in
  let _ww_zdigits = w_add2 w_zdigits w_zdigits in
  let to_Z0 = zn2z_to_Z wB w_to_Z in
  let w_W0 = ZnZ.coq_WO ops0 in
  let w_0W = ZnZ.coq_OW ops0 in
  let w_WW = ZnZ.coq_WW ops0 in
  let ww_of_pos = fun p ->
    let (n0, l) = w_of_pos p in
    (match n0 with
     | N0 -> (N0, (WW (w_0, l)))
     | Npos ph -> let (n1, h) = w_of_pos ph in (n1, (w_WW h l)))
  in
  let head1 = fun x ->
    match x with
    | W0 -> _ww_zdigits
    | WW (xh, xl) ->
      (match w_compare w_0 xh with
       | Eq -> w_add2 w_zdigits (w_head0 xl)
       | _ -> w_0W (w_head0 xh))
  in
  let tail1 = fun x ->
    match x with
    | W0 -> _ww_zdigits
    | WW (xh, xl) ->
      (match w_compare w_0 xl with
       | Eq -> w_add2 w_zdigits (w_tail0 xh)
       | _ -> w_0W (w_tail0 xl))
  in
  let compare1 = fun x y ->
    match x with
    | W0 ->
      (match y with
       | W0 -> Eq
       | WW (yh, yl) ->
         (match w_compare w_0 yh with
          | Eq -> w_compare w_0 yl
          | _ -> Lt))
    | WW (xh, xl) ->
      (match y with
       | W0 -> (match w_compare xh w_0 with
                | Eq -> w_compare xl w_0
                | _ -> Gt)
       | WW (yh, yl) ->
         (match w_compare xh yh with
          | Eq -> w_compare xl yl
          | x0 -> x0))
  in
  let eq1 = fun x -> match x with
                     | W0 -> true
                     | WW (_, _) -> false in
  let opp_c0 = fun x ->
    match x with
    | W0 -> Uint63.C0 W0
    | WW (xh, xl) ->
      (match w_opp_c xl with
       | Uint63.C0 _ ->
         (match w_opp_c xh with
          | Uint63.C0 _ -> Uint63.C0 W0
          | Uint63.C1 h -> Uint63.C1 (WW (h, w_0)))
       | Uint63.C1 l -> Uint63.C1 (WW ((w_opp_carry xh), l)))
  in
  let opp1 = fun x ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      (match w_opp_c xl with
       | Uint63.C0 _ -> WW ((w_opp xh), w_0)
       | Uint63.C1 l -> WW ((w_opp_carry xh), l))
  in
  let opp_carry0 = fun x ->
    match x with
    | W0 -> ww_Bm2
    | WW (xh, xl) -> w_WW (w_opp_carry xh) (w_opp_carry xl)
  in
  let succ_c0 = fun x ->
    match x with
    | W0 -> Uint63.C0 ww_2
    | WW (xh, xl) ->
      (match w_succ_c xl with
       | Uint63.C0 l -> Uint63.C0 (WW (xh, l))
       | Uint63.C1 _ ->
         (match w_succ_c xh with
          | Uint63.C0 h -> Uint63.C0 (WW (h, w_0))
          | Uint63.C1 _ -> Uint63.C1 W0))
  in
  let add_c0 = fun x y ->
    match x with
    | W0 -> Uint63.C0 y
    | WW (xh, xl) ->
      (match y with
       | W0 -> Uint63.C0 x
       | WW (yh, yl) ->
         (match w_add_c xl yl with
          | Uint63.C0 l ->
            (match w_add_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))
          | Uint63.C1 l ->
            (match w_add_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))))
  in
  let add_carry_c0 = fun x y ->
    match x with
    | W0 ->
      (match y with
       | W0 -> Uint63.C0 ww_2
       | WW (yh, yl) ->
         (match w_succ_c yl with
          | Uint63.C0 l -> Uint63.C0 (WW (yh, l))
          | Uint63.C1 _ ->
            (match w_succ_c yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, w_0))
             | Uint63.C1 _ -> Uint63.C1 W0)))
    | WW (xh, xl) ->
      (match y with
       | W0 ->
         (match w_succ_c xl with
          | Uint63.C0 l -> Uint63.C0 (WW (xh, l))
          | Uint63.C1 _ ->
            (match w_succ_c xh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, w_0))
             | Uint63.C1 _ -> Uint63.C1 W0))
       | WW (yh, yl) ->
         (match w_add_carry_c xl yl with
          | Uint63.C0 l ->
            (match w_add_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))
          | Uint63.C1 l ->
            (match w_add_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))))
  in
  let succ1 = fun x ->
    match x with
    | W0 -> ww_2
    | WW (xh, xl) ->
      (match w_succ_c xl with
       | Uint63.C0 l -> WW (xh, l)
       | Uint63.C1 _ -> w_W0 (w_succ xh))
  in
  let add1 = fun x y ->
    match x with
    | W0 -> y
    | WW (xh, xl) ->
      (match y with
       | W0 -> x
       | WW (yh, yl) ->
         (match w_add_c xl yl with
          | Uint63.C0 l -> WW ((w_add xh yh), l)
          | Uint63.C1 l -> WW ((w_add_carry xh yh), l)))
  in
  let add_carry0 = fun x y ->
    match x with
    | W0 ->
      (match y with
       | W0 -> ww_2
       | WW (yh, yl) ->
         (match w_succ_c yl with
          | Uint63.C0 l -> WW (yh, l)
          | Uint63.C1 _ -> w_W0 (w_succ yh)))
    | WW (xh, xl) ->
      (match y with
       | W0 ->
         (match w_succ_c xl with
          | Uint63.C0 l -> WW (xh, l)
          | Uint63.C1 _ -> w_W0 (w_succ xh))
       | WW (yh, yl) ->
         (match w_add_carry_c xl yl with
          | Uint63.C0 l -> WW ((w_add xh yh), l)
          | Uint63.C1 l -> WW ((w_add_carry xh yh), l)))
  in
  let pred_c0 = fun x ->
    match x with
    | W0 -> Uint63.C1 ww_Bm2
    | WW (xh, xl) ->
      (match w_pred_c xl with
       | Uint63.C0 l -> Uint63.C0 (w_WW xh l)
       | Uint63.C1 _ ->
         (match w_pred_c xh with
          | Uint63.C0 h -> Uint63.C0 (WW (h, w_Bm1))
          | Uint63.C1 _ -> Uint63.C1 ww_Bm2))
  in
  let sub_c0 = fun x y ->
    match y with
    | W0 -> Uint63.C0 x
    | WW (yh, yl) ->
      (match x with
       | W0 ->
         (match w_opp_c yl with
          | Uint63.C0 _ ->
            (match w_opp_c yh with
             | Uint63.C0 _ -> Uint63.C0 W0
             | Uint63.C1 h -> Uint63.C1 (WW (h, w_0)))
          | Uint63.C1 l -> Uint63.C1 (WW ((w_opp_carry yh), l)))
       | WW (xh, xl) ->
         (match w_sub_c xl yl with
          | Uint63.C0 l ->
            (match w_sub_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (w_WW h l)
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))
          | Uint63.C1 l ->
            (match w_sub_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, l))
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))))
  in
  let sub_carry_c0 = fun x y ->
    match y with
    | W0 ->
      (match x with
       | W0 -> Uint63.C1 ww_Bm2
       | WW (xh, xl) ->
         (match w_pred_c xl with
          | Uint63.C0 l -> Uint63.C0 (w_WW xh l)
          | Uint63.C1 _ ->
            (match w_pred_c xh with
             | Uint63.C0 h -> Uint63.C0 (WW (h, w_Bm1))
             | Uint63.C1 _ -> Uint63.C1 ww_Bm2)))
    | WW (yh, yl) ->
      (match x with
       | W0 -> Uint63.C1 (w_WW (w_opp_carry yh) (w_opp_carry yl))
       | WW (xh, xl) ->
         (match w_sub_carry_c xl yl with
          | Uint63.C0 l ->
            (match w_sub_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (w_WW h l)
             | Uint63.C1 h -> Uint63.C1 (WW (h, l)))
          | Uint63.C1 l ->
            (match w_sub_carry_c xh yh with
             | Uint63.C0 h -> Uint63.C0 (w_WW h l)
             | Uint63.C1 h -> Uint63.C1 (w_WW h l))))
  in
  let pred2 = fun x ->
    match x with
    | W0 -> ww_Bm2
    | WW (xh, xl) ->
      (match w_pred_c xl with
       | Uint63.C0 l -> w_WW xh l
       | Uint63.C1 _ -> WW ((w_pred xh), w_Bm1))
  in
  let sub1 = fun x y ->
    match y with
    | W0 -> x
    | WW (yh, yl) ->
      (match x with
       | W0 ->
         (match w_opp_c yl with
          | Uint63.C0 _ -> WW ((w_opp yh), w_0)
          | Uint63.C1 l -> WW ((w_opp_carry yh), l))
       | WW (xh, xl) ->
         (match w_sub_c xl yl with
          | Uint63.C0 l -> w_WW (w_sub xh yh) l
          | Uint63.C1 l -> WW ((w_sub_carry xh yh), l)))
  in
  let sub_carry0 = fun x y ->
    match y with
    | W0 ->
      (match x with
       | W0 -> ww_Bm2
       | WW (xh, xl) ->
         (match w_pred_c xl with
          | Uint63.C0 l -> w_WW xh l
          | Uint63.C1 _ -> WW ((w_pred xh), w_Bm1)))
    | WW (yh, yl) ->
      (match x with
       | W0 -> w_WW (w_opp_carry yh) (w_opp_carry yl)
       | WW (xh, xl) ->
         (match w_sub_carry_c xl yl with
          | Uint63.C0 l -> w_WW (w_sub xh yh) l
          | Uint63.C1 l -> w_WW (w_sub_carry xh yh) l))
  in
  let karatsuba_c = fun x y ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      (match y with
       | W0 -> W0
       | WW (yh, yl) ->
         let hh = w_mul_c xh yh in
         let ll = w_mul_c xl yl in
         (match add_c0 hh ll with
          | Uint63.C0 m ->
            (match w_compare xl xh with
             | Eq ->
               (match m with
                | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                | WW (cch, ccl) ->
                  (match add_c0 (w_W0 ccl) ll with
                   | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                   | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))
             | Lt ->
               (match w_compare yl yh with
                | Eq ->
                  (match m with
                   | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                   | WW (cch, ccl) ->
                     (match add_c0 (w_W0 ccl) ll with
                      | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                      | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))
                | Lt ->
                  let cc = sub1 m (w_mul_c (w_sub xh xl) (w_sub yh yl)) in
                  (match cc with
                   | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                   | WW (cch, ccl) ->
                     (match add_c0 (w_W0 ccl) ll with
                      | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                      | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))
                | Gt ->
                  (match add_c0 m (w_mul_c (w_sub xh xl) (w_sub yl yh)) with
                   | Uint63.C0 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_0 cch)), l)))
                   | Uint63.C1 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_1 cch)), l)))))
             | Gt ->
               (match w_compare yl yh with
                | Eq ->
                  (match m with
                   | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                   | WW (cch, ccl) ->
                     (match add_c0 (w_W0 ccl) ll with
                      | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                      | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))
                | Lt ->
                  (match add_c0 m (w_mul_c (w_sub xl xh) (w_sub yh yl)) with
                   | Uint63.C0 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_0 cch)), l)))
                   | Uint63.C1 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_1 cch)), l))))
                | Gt ->
                  let cc = sub1 m (w_mul_c (w_sub xl xh) (w_sub yl yh)) in
                  (match cc with
                   | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                   | WW (cch, ccl) ->
                     (match add_c0 (w_W0 ccl) ll with
                      | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                      | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))))
          | Uint63.C1 m ->
            (match w_compare xl xh with
             | Eq ->
               (match m with
                | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                | WW (cch, ccl) ->
                  (match add_c0 (w_W0 ccl) ll with
                   | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                   | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_1 cch)), l)))
             | Lt ->
               (match w_compare yl yh with
                | Eq ->
                  (match m with
                   | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                   | WW (cch, ccl) ->
                     (match add_c0 (w_W0 ccl) ll with
                      | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                      | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_1 cch)), l)))
                | Lt ->
                  (match sub_c0 m (w_mul_c (w_sub xh xl) (w_sub yh yl)) with
                   | Uint63.C0 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_1 cch)), l)))
                   | Uint63.C1 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_0 cch)), l))))
                | Gt ->
                  (match add_c0 m (w_mul_c (w_sub xh xl) (w_sub yl yh)) with
                   | Uint63.C0 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_1 cch)), l)))
                   | Uint63.C1 m1 ->
                     let wc = w_2 w_1 w_add in
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 wc)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW wc cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW wc cch)), l)))))
             | Gt ->
               (match w_compare yl yh with
                | Eq ->
                  (match m with
                   | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                   | WW (cch, ccl) ->
                     (match add_c0 (w_W0 ccl) ll with
                      | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                      | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_1 cch)), l)))
                | Lt ->
                  (match add_c0 m (w_mul_c (w_sub xl xh) (w_sub yh yl)) with
                   | Uint63.C0 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_1 cch)), l)))
                   | Uint63.C1 m1 ->
                     let wc = w_2 w_1 w_add in
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 wc)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW wc cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW wc cch)), l))))
                | Gt ->
                  (match sub_c0 m (w_mul_c (w_sub xl xh) (w_sub yl yh)) with
                   | Uint63.C0 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_1 cch)), l)))
                   | Uint63.C1 m1 ->
                     (match m1 with
                      | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
                      | WW (cch, ccl) ->
                        (match add_c0 (w_W0 ccl) ll with
                         | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
                         | Uint63.C1 l ->
                           WW ((add_carry0 hh (w_WW w_0 cch)), l))))))))
  in
  let mul1 = fun x y ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      (match y with
       | W0 -> W0
       | WW (yh, yl) ->
         let ccl = w_add (w_mul xh yl) (w_mul xl yh) in
         add1 (w_W0 ccl) (w_mul_c xl yl))
  in
  let square_c0 = fun x ->
    match x with
    | W0 -> W0
    | WW (xh, xl) ->
      let hh = w_square_c xh in
      let ll = w_square_c xl in
      let xhxl = w_mul_c xh xl in
      (match add_c0 xhxl xhxl with
       | Uint63.C0 cc ->
         (match cc with
          | W0 -> WW ((add1 hh (w_W0 w_0)), ll)
          | WW (cch, ccl) ->
            (match add_c0 (w_W0 ccl) ll with
             | Uint63.C0 l -> WW ((add1 hh (w_WW w_0 cch)), l)
             | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_0 cch)), l)))
       | Uint63.C1 cc ->
         (match cc with
          | W0 -> WW ((add1 hh (w_W0 w_1)), ll)
          | WW (cch, ccl) ->
            (match add_c0 (w_W0 ccl) ll with
             | Uint63.C0 l -> WW ((add1 hh (w_WW w_1 cch)), l)
             | Uint63.C1 l -> WW ((add_carry0 hh (w_WW w_1 cch)), l))))
  in
  let div32 = fun a1 a2 a3 b1 b2 ->
    match w_compare a1 b1 with
    | Eq ->
      (match w_add_c a3 b2 with
       | Uint63.C0 l ->
         (match w_add_c (w_sub a2 b2) b1 with
          | Uint63.C0 h ->
            (w_Bm2,
              (match w_add_c l b2 with
               | Uint63.C0 l0 -> WW ((w_add h b1), l0)
               | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
          | Uint63.C1 h -> (w_Bm1, (w_WW h l)))
       | Uint63.C1 l ->
         (match w_add_carry_c (w_sub a2 b2) b1 with
          | Uint63.C0 h ->
            (w_Bm2,
              (match w_add_c l b2 with
               | Uint63.C0 l0 -> WW ((w_add h b1), l0)
               | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
          | Uint63.C1 h -> (w_Bm1, (w_WW h l))))
    | Lt ->
      let (q, r) = w_div21 a1 a2 b1 in
      (match sub_c0 (w_WW r a3) (w_mul_c q b2) with
       | Uint63.C0 r1 -> (q, r1)
       | Uint63.C1 r1 ->
         let q0 = w_pred q in
         (match r1 with
          | W0 ->
            ((w_pred q0),
              (match w_add_c b2 b2 with
               | Uint63.C0 l -> WW ((w_add b1 b1), l)
               | Uint63.C1 l -> WW ((w_add_carry b1 b1), l)))
          | WW (xh, xl) ->
            (match w_add_c xl b2 with
             | Uint63.C0 l ->
               (match w_add_c xh b1 with
                | Uint63.C0 h ->
                  ((w_pred q0),
                    (match w_add_c l b2 with
                     | Uint63.C0 l0 -> WW ((w_add h b1), l0)
                     | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
                | Uint63.C1 h -> (q0, (w_WW h l)))
             | Uint63.C1 l ->
               (match w_add_carry_c xh b1 with
                | Uint63.C0 h ->
                  ((w_pred q0),
                    (match w_add_c l b2 with
                     | Uint63.C0 l0 -> WW ((w_add h b1), l0)
                     | Uint63.C1 l0 -> WW ((w_add_carry h b1), l0)))
                | Uint63.C1 h -> (q0, (w_WW h l))))))
    | Gt -> (w_0, W0)
  in
  let div22 = fun a1 a2 b ->
    match a1 with
    | W0 ->
      (match compare1 a2 b with
       | Eq -> (ww_2, W0)
       | Lt -> (W0, a2)
       | Gt -> (ww_2, (sub1 a2 b)))
    | WW (a1h, a1l) ->
      (match a2 with
       | W0 ->
         (match b with
          | W0 -> (W0, W0)
          | WW (b1, b2) ->
            let (q1, r) = div32 a1h a1l w_0 b1 b2 in
            (match r with
             | W0 -> ((WW (q1, w_0)), W0)
             | WW (r1, r2) ->
               let (q2, s) = div32 r1 r2 w_0 b1 b2 in ((WW (q1, q2)), s)))
       | WW (a2h, a2l) ->
         (match b with
          | W0 -> (W0, W0)
          | WW (b1, b2) ->
            let (q1, r) = div32 a1h a1l a2h b1 b2 in
            (match r with
             | W0 -> ((WW (q1, w_0)), (w_0W a2l))
             | WW (r1, r2) ->
               let (q2, s) = div32 r1 r2 a2l b1 b2 in ((WW (q1, q2)), s))))
  in
  let low = fun p -> match p with
                     | W0 -> w_0
                     | WW (_, p1) -> p1 in
  let add_mul_div0 = fun p x y ->
    let zdigits0 = w_0W w_zdigits in
    (match x with
     | W0 ->
       (match y with
        | W0 -> W0
        | WW (yh, yl) ->
          (match compare1 p zdigits0 with
           | Eq -> w_0W yh
           | Lt -> w_0W (w_add_mul_div (low p) w_0 yh)
           | Gt ->
             let n0 = low (sub1 p zdigits0) in
             w_WW (w_add_mul_div n0 w_0 yh) (w_add_mul_div n0 yh yl)))
     | WW (xh, xl) ->
       (match y with
        | W0 ->
          (match compare1 p zdigits0 with
           | Eq -> w_W0 xl
           | Lt ->
             w_WW (w_add_mul_div (low p) xh xl) (w_add_mul_div (low p) xl w_0)
           | Gt ->
             let n0 = low (sub1 p zdigits0) in w_W0 (w_add_mul_div n0 xl w_0))
        | WW (yh, yl) ->
          (match compare1 p zdigits0 with
           | Eq -> w_WW xl yh
           | Lt ->
             w_WW (w_add_mul_div (low p) xh xl) (w_add_mul_div (low p) xl yh)
           | Gt ->
             let n0 = low (sub1 p zdigits0) in
             w_WW (w_add_mul_div n0 xl yh) (w_add_mul_div n0 yh yl))))
  in
  let div_gt0 = fun a b ->
    match a with
    | W0 -> (W0, W0)
    | WW (ah, al) ->
      (match b with
       | W0 -> (W0, W0)
       | WW (bh, bl) ->
         if w_eq0 ah
         then let (q, r) = w_div_gt al bl in ((WW (w_0, q)), (w_0W r))
         else (match w_compare w_0 bh with
               | Eq ->
                 let (q, r) =
                   let p = w_head0 bl in
                   (match w_compare p w_0 with
                    | Gt ->
                      let b2p = w_add_mul_div p bl w_0 in
                      let ha = high w_0 (Stdlib.Int.succ 0) (Obj.magic a) in
                      let k = w_sub w_zdigits p in
                      let lsr_n = w_add_mul_div k w_0 in
                      let r0 = w_add_mul_div p w_0 ha in
                      (match a with
                       | W0 ->
                         let (qh, rh) =
                           w_div21 r0 (w_add_mul_div p w_0 w_0) b2p
                         in
                         let (ql, rl) =
                           w_div21 rh (w_add_mul_div p w_0 w_0) b2p
                         in
                         let q = w_WW qh ql in (q, (lsr_n rl))
                       | WW (h, l) ->
                         let (qh, rh) = w_div21 r0 (w_add_mul_div p h l) b2p
                         in
                         let (ql, rl) = w_div21 rh (w_add_mul_div p l w_0) b2p
                         in
                         let q = w_WW qh ql in (q, (lsr_n rl)))
                    | _ ->
                      (match a with
                       | W0 ->
                         let (qh, rh) = w_div21 w_0 w_0 bl in
                         let (ql, rl) = w_div21 rh w_0 bl in
                         ((w_WW qh ql), rl)
                       | WW (h, l) ->
                         let (qh, rh) = w_div21 w_0 h bl in
                         let (ql, rl) = w_div21 rh l bl in ((w_WW qh ql), rl)))
                 in
                 (q, (w_0W r))
               | Lt ->
                 let p = w_head0 bh in
                 (match w_compare p w_0 with
                  | Gt ->
                    let b1 = w_add_mul_div p bh bl in
                    let b2 = w_add_mul_div p bl w_0 in
                    let a1 = w_add_mul_div p w_0 ah in
                    let a2 = w_add_mul_div p ah al in
                    let a3 = w_add_mul_div p al w_0 in
                    let (q, r) = div32 a1 a2 a3 b1 b2 in
                    ((WW (w_0, q)),
                    (add_mul_div0
                      (match w_0W p with
                       | W0 -> _ww_zdigits
                       | WW (yh, yl) ->
                         (match _ww_zdigits with
                          | W0 ->
                            (match w_opp_c yl with
                             | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                             | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                          | WW (xh, xl) ->
                            (match w_sub_c xl yl with
                             | Uint63.C0 l -> w_WW (w_sub xh yh) l
                             | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
                      W0 r))
                  | _ ->
                    (ww_2,
                      (match w_sub_c al bl with
                       | Uint63.C0 l -> w_WW (w_sub ah bh) l
                       | Uint63.C1 l -> WW ((w_sub_carry ah bh), l))))
               | Gt -> (W0, W0)))
  in
  let div1 = fun a b ->
    match compare1 a b with
    | Eq -> (ww_2, W0)
    | Lt -> (W0, a)
    | Gt -> div_gt0 a b
  in
  let mod_gt = fun a b ->
    match a with
    | W0 -> W0
    | WW (ah, al) ->
      (match b with
       | W0 -> W0
       | WW (bh, bl) ->
         if w_eq0 ah
         then w_0W (w_mod_gt al bl)
         else (match w_compare w_0 bh with
               | Eq ->
                 w_0W
                   (let p = w_head0 bl in
                    match w_compare p w_0 with
                    | Gt ->
                      let b2p = w_add_mul_div p bl w_0 in
                      let ha = high w_0 (Stdlib.Int.succ 0) (Obj.magic a) in
                      let k = w_sub w_zdigits p in
                      let lsr_n = w_add_mul_div k w_0 in
                      let r0 = w_add_mul_div p w_0 ha in
                      let r =
                        match a with
                        | W0 ->
                          let (_, y) =
                            w_div21
                              (let (_, y) =
                                 w_div21 r0 (w_add_mul_div p w_0 w_0) b2p
                               in
                               y)
                              (w_add_mul_div p w_0 w_0) b2p
                          in
                          y
                        | WW (h, l) ->
                          let (_, y) =
                            w_div21
                              (let (_, y) =
                                 w_div21 r0 (w_add_mul_div p h l) b2p
                               in
                               y)
                              (w_add_mul_div p l w_0) b2p
                          in
                          y
                      in
                      lsr_n r
                    | _ ->
                      (match a with
                       | W0 ->
                         let (_, y) =
                           w_div21 (let (_, y) = w_div21 w_0 w_0 bl in y) w_0
                             bl
                         in
                         y
                       | WW (h, l) ->
                         let (_, y) =
                           w_div21 (let (_, y) = w_div21 w_0 h bl in y) l bl
                         in
                         y))
               | Lt ->
                 let p = w_head0 bh in
                 (match w_compare p w_0 with
                  | Gt ->
                    let b1 = w_add_mul_div p bh bl in
                    let b2 = w_add_mul_div p bl w_0 in
                    let a1 = w_add_mul_div p w_0 ah in
                    let a2 = w_add_mul_div p ah al in
                    let a3 = w_add_mul_div p al w_0 in
                    let (_, r) = div32 a1 a2 a3 b1 b2 in
                    add_mul_div0
                      (match w_0W p with
                       | W0 -> _ww_zdigits
                       | WW (yh, yl) ->
                         (match _ww_zdigits with
                          | W0 ->
                            (match w_opp_c yl with
                             | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                             | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                          | WW (xh, xl) ->
                            (match w_sub_c xl yl with
                             | Uint63.C0 l -> w_WW (w_sub xh yh) l
                             | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
                      W0 r
                  | _ ->
                    (match w_sub_c al bl with
                     | Uint63.C0 l -> w_WW (w_sub ah bh) l
                     | Uint63.C1 l -> WW ((w_sub_carry ah bh), l)))
               | Gt -> W0))
  in
  let mod_ = fun a b ->
    match compare1 a b with
    | Eq -> W0
    | Lt -> a
    | Gt -> mod_gt a b
  in
  let pos_mod1 = fun p x ->
    let zdigits0 = w_0W w_zdigits in
    (match x with
     | W0 -> W0
     | WW (xh, xl) ->
       (match compare1 p zdigits0 with
        | Eq -> w_WW w_0 xl
        | Lt -> w_WW w_0 (w_pos_mod (low p) xl)
        | Gt ->
          (match compare1 p _ww_zdigits with
           | Lt -> let n0 = low (sub1 p zdigits0) in w_WW (w_pos_mod n0 xh) xl
           | _ -> x)))
  in
  let is_even0 = fun x -> match x with
                          | W0 -> true
                          | WW (_, xl) -> w_is_even xl
  in
  let sqrt3 =
    let wwBm1 = ww_Bm1 w_Bm1 in
    let w_div21c = fun x y z0 ->
      match w_compare x z0 with
      | Eq ->
        (match w_compare y z0 with
         | Eq -> ((Uint63.C1 w_1), w_0)
         | Lt -> ((Uint63.C1 w_0), y)
         | Gt -> ((Uint63.C1 w_1), (w_sub y z0)))
      | Lt -> let (q, r) = w_div21 x y z0 in ((Uint63.C0 q), r)
      | Gt ->
        let x1 = w_sub x z0 in
        let (q, r) = w_div21 x1 y z0 in ((Uint63.C1 q), r)
    in
    let w_div2s = fun x y s ->
      match x with
      | Uint63.C0 x1 ->
        let (q, r) = w_div21c x1 y s in
        (match q with
         | Uint63.C0 q1 ->
           if w_is_even q1
           then ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (w_add_c r s))
         | Uint63.C1 q1 ->
           if w_is_even q1
           then ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (w_add_c r s)))
      | Uint63.C1 x1 ->
        let x2 = w_sub x1 s in
        let (q, r) = w_div21c x2 y s in
        (match q with
         | Uint63.C0 q1 ->
           if w_is_even q1
           then ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C0 (w_add_mul_div (w_pred w_zdigits) w_1 q1)),
                  (w_add_c r s))
         | Uint63.C1 q1 ->
           if w_is_even q1
           then ((Uint63.C1 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (Uint63.C0 r))
           else ((Uint63.C1 (w_add_mul_div (w_pred w_zdigits) w_0 q1)),
                  (w_add_c r s)))
    in
    (fun x y ->
    let (x1, x2) = split w_0 x in
    let (y1, y2) = split w_0 y in
    let (q, r) = w_sqrt2 x1 x2 in
    let (q1, r1) = w_div2s r y1 q in
    (match q1 with
     | Uint63.C0 q2 ->
       let q3 = w_square_c q2 in
       let a = WW (q, q2) in
       (match r1 with
        | Uint63.C0 r2 ->
          (match sub_c0 (WW (r2, y2)) q3 with
           | Uint63.C0 r3 -> (a, (Uint63.C0 r3))
           | Uint63.C1 r3 ->
             let a2 = add_mul_div0 (w_0W w_1) a W0 in
             (match pred_c0 a2 with
              | Uint63.C0 a3 -> ((pred2 a), (add_c0 a3 r3))
              | Uint63.C1 a3 -> ((pred2 a), (Uint63.C0 (add1 a3 r3)))))
        | Uint63.C1 r2 ->
          (match sub_c0 (WW (r2, y2)) q3 with
           | Uint63.C0 r3 -> (a, (Uint63.C1 r3))
           | Uint63.C1 r3 -> (a, (Uint63.C0 r3))))
     | Uint63.C1 _ ->
       let a1 = WW (q, w_Bm1) in
       let a2 = add_mul_div0 (w_0W w_1) a1 wwBm1 in (a1, (add_c0 a2 y))))
  in
  let sqrt0 = fun x ->
    if ww_is_zero compare1 x
    then W0
    else let p = ww_head1 w_is_even pred2 head1 x in
         (match compare1 p W0 with
          | Eq ->
            (match x with
             | W0 -> W0
             | WW (x1, x2) -> WW (w_0, (fst (w_sqrt2 x1 x2))))
          | Lt ->
            (match x with
             | W0 -> W0
             | WW (x1, x2) -> WW (w_0, (fst (w_sqrt2 x1 x2))))
          | Gt ->
            (match add_mul_div0 p x W0 with
             | W0 -> W0
             | WW (x1, x2) ->
               let (r, _) = w_sqrt2 x1 x2 in
               WW (w_0,
               (w_add_mul_div
                 (w_sub w_zdigits
                   (low (add_mul_div0 (pred2 _ww_zdigits) W0 p)))
                 w_0 r))))
  in
  let gcd_gt_fix =
    let rec ww_gcd_gt_aux p cont ah al bh bl =
      match w_compare w_0 bh with
      | Eq ->
        (match w_compare w_0 bl with
         | Eq -> WW (ah, al)
         | Lt ->
           let m =
             let p0 = w_head0 bl in
             (match w_compare p0 w_0 with
              | Gt ->
                let b2p = w_add_mul_div p0 bl w_0 in
                let ha =
                  high w_0 (Stdlib.Int.succ 0) (Obj.magic (WW (ah, al)))
                in
                let k = w_sub w_zdigits p0 in
                let lsr_n = w_add_mul_div k w_0 in
                let r0 = w_add_mul_div p0 w_0 ha in
                let r =
                  let (_, y) =
                    w_div21
                      (let (_, y) = w_div21 r0 (w_add_mul_div p0 ah al) b2p in
                       y)
                      (w_add_mul_div p0 al w_0) b2p
                  in
                  y
                in
                lsr_n r
              | _ ->
                let (_, y) =
                  w_div21 (let (_, y) = w_div21 w_0 ah bl in y) al bl
                in
                y)
           in
           WW (w_0, (w_gcd_gt bl m))
         | Gt -> W0)
      | Lt ->
        let m =
          let p0 = w_head0 bh in
          (match w_compare p0 w_0 with
           | Gt ->
             let b1 = w_add_mul_div p0 bh bl in
             let b2 = w_add_mul_div p0 bl w_0 in
             let a1 = w_add_mul_div p0 w_0 ah in
             let a2 = w_add_mul_div p0 ah al in
             let a3 = w_add_mul_div p0 al w_0 in
             let (_, r) = div32 a1 a2 a3 b1 b2 in
             add_mul_div0
               (match w_0W p0 with
                | W0 -> _ww_zdigits
                | WW (yh, yl) ->
                  (match _ww_zdigits with
                   | W0 ->
                     (match w_opp_c yl with
                      | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                      | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                   | WW (xh, xl) ->
                     (match w_sub_c xl yl with
                      | Uint63.C0 l -> w_WW (w_sub xh yh) l
                      | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
               W0 r
           | _ ->
             (match w_sub_c al bl with
              | Uint63.C0 l -> w_WW (w_sub ah bh) l
              | Uint63.C1 l -> WW ((w_sub_carry ah bh), l)))
        in
        (match m with
         | W0 -> WW (bh, bl)
         | WW (mh, ml) ->
           (match w_compare w_0 mh with
            | Eq ->
              (match w_compare w_0 ml with
               | Eq -> WW (bh, bl)
               | _ ->
                 let r =
                   let p0 = w_head0 ml in
                   (match w_compare p0 w_0 with
                    | Gt ->
                      let b2p = w_add_mul_div p0 ml w_0 in
                      let ha =
                        high w_0 (Stdlib.Int.succ 0) (Obj.magic (WW (bh, bl)))
                      in
                      let k = w_sub w_zdigits p0 in
                      let lsr_n = w_add_mul_div k w_0 in
                      let r0 = w_add_mul_div p0 w_0 ha in
                      let r =
                        let (_, y) =
                          w_div21
                            (let (_, y) =
                               w_div21 r0 (w_add_mul_div p0 bh bl) b2p
                             in
                             y)
                            (w_add_mul_div p0 bl w_0) b2p
                        in
                        y
                      in
                      lsr_n r
                    | _ ->
                      let (_, y) =
                        w_div21 (let (_, y) = w_div21 w_0 bh ml in y) bl ml
                      in
                      y)
                 in
                 WW (w_0, (w_gcd_gt ml r)))
            | Lt ->
              let r =
                let p0 = w_head0 mh in
                (match w_compare p0 w_0 with
                 | Gt ->
                   let b1 = w_add_mul_div p0 mh ml in
                   let b2 = w_add_mul_div p0 ml w_0 in
                   let a1 = w_add_mul_div p0 w_0 bh in
                   let a2 = w_add_mul_div p0 bh bl in
                   let a3 = w_add_mul_div p0 bl w_0 in
                   let (_, r) = div32 a1 a2 a3 b1 b2 in
                   add_mul_div0
                     (match w_0W p0 with
                      | W0 -> _ww_zdigits
                      | WW (yh, yl) ->
                        (match _ww_zdigits with
                         | W0 ->
                           (match w_opp_c yl with
                            | Uint63.C0 _ -> WW ((w_opp yh), w_0)
                            | Uint63.C1 l -> WW ((w_opp_carry yh), l))
                         | WW (xh, xl) ->
                           (match w_sub_c xl yl with
                            | Uint63.C0 l -> w_WW (w_sub xh yh) l
                            | Uint63.C1 l -> WW ((w_sub_carry xh yh), l))))
                     W0 r
                 | _ ->
                   (match w_sub_c bl ml with
                    | Uint63.C0 l -> w_WW (w_sub bh mh) l
                    | Uint63.C1 l -> WW ((w_sub_carry bh mh), l)))
              in
              (match r with
               | W0 -> m
               | WW (rh, rl) ->
                 (match p with
                  | XI p0 ->
                    ww_gcd_gt_aux p0 (ww_gcd_gt_aux p0 cont) mh ml rh rl
                  | XO p0 ->
                    ww_gcd_gt_aux p0 (ww_gcd_gt_aux p0 cont) mh ml rh rl
                  | XH -> cont mh ml rh rl))
            | Gt -> W0))
      | Gt -> W0
    in ww_gcd_gt_aux
  in
  let gcd_cont = fun xh xl _ yl ->
    match w_compare w_1 yl with
    | Eq -> ww_2
    | _ -> WW (xh, xl)
  in
  let gcd_gt0 = fun a b ->
    match a with
    | W0 -> b
    | WW (ah, al) ->
      (match b with
       | W0 -> a
       | WW (bh, bl) ->
         if w_eq0 ah
         then WW (w_0, (w_gcd_gt al bl))
         else gcd_gt_fix _ww_digits gcd_cont ah al bh bl)
  in
  let gcd0 = fun a b ->
    match compare1 a b with
    | Eq -> a
    | Lt ->
      (match b with
       | W0 -> a
       | WW (ah, al) ->
         (match a with
          | W0 -> b
          | WW (bh, bl) ->
            if w_eq0 ah
            then WW (w_0, (w_gcd_gt al bl))
            else gcd_gt_fix _ww_digits gcd_cont ah al bh bl))
    | Gt ->
      (match a with
       | W0 -> b
       | WW (ah, al) ->
         (match b with
          | W0 -> a
          | WW (bh, bl) ->
            if w_eq0 ah
            then WW (w_0, (w_gcd_gt al bl))
            else gcd_gt_fix _ww_digits gcd_cont ah al bh bl))
  in
  { ZnZ.digits = _ww_digits; ZnZ.zdigits = _ww_zdigits; ZnZ.to_Z = to_Z0;
  ZnZ.of_pos = ww_of_pos; ZnZ.head0 = head1; ZnZ.tail0 = tail1; ZnZ.zero =
  W0; ZnZ.one = ww_2; ZnZ.minus_one = ww_Bm2; ZnZ.compare = compare1;
  ZnZ.eq0 = eq1; ZnZ.opp_c = opp_c0; ZnZ.opp = opp1; ZnZ.opp_carry =
  opp_carry0; ZnZ.succ_c = succ_c0; ZnZ.add_c = add_c0; ZnZ.add_carry_c =
  add_carry_c0; ZnZ.succ = succ1; ZnZ.add = add1; ZnZ.add_carry = add_carry0;
  ZnZ.pred_c = pred_c0; ZnZ.sub_c = sub_c0; ZnZ.sub_carry_c = sub_carry_c0;
  ZnZ.pred = pred2; ZnZ.sub = sub1; ZnZ.sub_carry = sub_carry0; ZnZ.mul_c =
  karatsuba_c; ZnZ.mul = mul1; ZnZ.square_c = square_c0; ZnZ.div21 = div22;
  ZnZ.div_gt = div_gt0; ZnZ.div = div1; ZnZ.modulo_gt = mod_gt; ZnZ.modulo =
  mod_; ZnZ.gcd_gt = gcd_gt0; ZnZ.gcd = gcd0; ZnZ.add_mul_div = add_mul_div0;
  ZnZ.pos_mod = pos_mod1; ZnZ.is_even = is_even0; ZnZ.sqrt2 = sqrt3;
  ZnZ.sqrt = sqrt0; ZnZ.coq_lor = (lor1 ops0); ZnZ.coq_land = (land1 ops0);
  ZnZ.coq_lxor = (lxor1 ops0) }

(** val plength : positive -> positive **)

let rec plength = function
| XI p1 -> Coq_Pos.succ (plength p1)
| XO p1 -> Coq_Pos.succ (plength p1)
| XH -> XH

(** val pdiv : positive -> positive -> positive **)

let pdiv p q =
  match Coq_Z.div (Zpos p) (Zpos q) with
  | Zpos q1 ->
    (match Coq_Z.sub (Zpos p) (Coq_Z.mul (Zpos q) (Zpos q1)) with
     | Z0 -> q1
     | _ -> Coq_Pos.succ q1)
  | _ -> XH

(** val is_one : positive -> bool **)

let is_one = function
| XH -> true
| _ -> false

(** val get_height : positive -> positive -> positive **)

let get_height digits0 p =
  let r = pdiv p digits0 in
  if is_one r then XH else Coq_Pos.succ (plength (Coq_Pos.pred r))

(** val diff : int -> int -> int * int **)

let rec diff m n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (0, n0))
    (fun m1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (m, 0))
      (fun n1 -> diff m1 n1)
      n0)
    m

(** val castm : int -> int -> 'a1 word -> 'a1 word **)

let castm _ _ x =
  x

(** val extend_tr : int -> 'a1 word -> int -> 'a1 word **)

let rec extend_tr m v n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> v)
    (fun n1 -> Obj.magic (WW ((Obj.magic W0), (extend_tr m v n1))))
    n0

(** val compare0_mn : ('a1 -> comparison) -> int -> 'a1 word -> comparison **)

let rec compare0_mn compare0_m n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic compare0_m)
    (fun m x ->
    match Obj.magic x with
    | W0 -> Eq
    | WW (xh, xl) ->
      (match compare0_mn compare0_m m xh with
       | Eq -> compare0_mn compare0_m m xl
       | _ -> Lt))
    n0

(** val compare_mn_1 :
    'a2 -> ('a2 -> 'a2 -> comparison) -> ('a1 -> comparison) -> ('a1 -> 'a2
    -> comparison) -> int -> 'a1 word -> 'a2 -> comparison **)

let rec compare_mn_1 w_0 compare1 compare0_m compare_m n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic compare_m)
    (fun m x y ->
    match Obj.magic x with
    | W0 -> compare1 w_0 y
    | WW (xh, xl) ->
      (match compare0_mn compare0_m m xh with
       | Eq -> compare_mn_1 w_0 compare1 compare0_m compare_m m xl y
       | _ -> Gt))
    n0

module BigN =
 struct
  type w1 = Uint63Cyclic.t zn2z

  type w2 = w1 zn2z

  type w3 = w2 zn2z

  type w4 = w3 zn2z

  type w5 = w4 zn2z

  type w6 = w5 zn2z

  (** val w1_op : w1 ZnZ.coq_Ops **)

  let w1_op =
    mk_zn2z_ops Uint63Cyclic.ops

  (** val w2_op : w2 ZnZ.coq_Ops **)

  let w2_op =
    mk_zn2z_ops w1_op

  (** val w3_op : w3 ZnZ.coq_Ops **)

  let w3_op =
    mk_zn2z_ops w2_op

  (** val w4_op : w4 ZnZ.coq_Ops **)

  let w4_op =
    mk_zn2z_ops_karatsuba w3_op

  (** val w5_op : w5 ZnZ.coq_Ops **)

  let w5_op =
    mk_zn2z_ops_karatsuba w4_op

  (** val w6_op : w6 ZnZ.coq_Ops **)

  let w6_op =
    mk_zn2z_ops_karatsuba w5_op

  (** val w7_op : w6 word ZnZ.coq_Ops **)

  let w7_op =
    Obj.magic mk_zn2z_ops_karatsuba w6_op

  (** val w8_op : w6 word ZnZ.coq_Ops **)

  let w8_op =
    Obj.magic mk_zn2z_ops_karatsuba w7_op

  (** val w9_op : w6 word ZnZ.coq_Ops **)

  let w9_op =
    Obj.magic mk_zn2z_ops_karatsuba w8_op

  (** val make_op_aux :
      (__ -> __ ZnZ.coq_Ops -> __ zn2z ZnZ.coq_Ops) -> int -> w6 word
      ZnZ.coq_Ops **)

  let rec make_op_aux mk n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> w7_op)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> w8_op)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> w9_op)
          (fun n3 ->
          Obj.magic mk __ (Obj.magic mk __ (mk __ (make_op_aux mk n3))))
          n2)
        n1)
      n0

  (** val omake_op : int -> w6 word ZnZ.coq_Ops **)

  let omake_op =
    make_op_aux (fun _ -> mk_zn2z_ops_karatsuba)

  (** val make_op_list : w6 word ZnZ.coq_Ops memo_val stream **)

  let make_op_list =
    dmemo_list omake_op

  (** val make_op : int -> w6 word ZnZ.coq_Ops **)

  let make_op n0 =
    dmemo_get omake_op n0 make_op_list

  type t' =
  | N0 of Uint63Cyclic.t
  | N1 of w1
  | N2 of w2
  | N3 of w3
  | N4 of w4
  | N5 of w5
  | N6 of w6
  | Nn of int * w6 word

  type t = t'

  type dom_t = __

  (** val dom_op : int -> dom_t ZnZ.coq_Ops **)

  let dom_op n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic Uint63Cyclic.ops)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic w1_op)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic w2_op)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic w3_op)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Obj.magic w4_op)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> Obj.magic w5_op)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> Obj.magic w6_op)
                  (fun n7 -> make_op n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0

  (** val mk_t : int -> dom_t -> t **)

  let mk_t n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic (fun x -> N0 x))
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic (fun x -> N1 x))
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic (fun x -> N2 x))
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic (fun x -> N3 x))
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Obj.magic (fun x -> N4 x))
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> Obj.magic (fun x -> N5 x))
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> Obj.magic (fun x -> N6 x))
                  (fun n7 x -> Nn (n7, x))
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0

  (** val zero0 : Uint63Cyclic.t **)

  let zero0 =
    Uint63Cyclic.ops.ZnZ.zero

  (** val succ_t : int -> dom_t zn2z -> dom_t **)

  let succ_t n0 x =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic x)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic x)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic x)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic x)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Obj.magic x)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> Obj.magic x)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> Obj.magic x)
                  (fun _ -> Obj.magic x)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0

  (** val zn2z_map : ('a1 -> 'a2) -> 'a1 zn2z -> 'a2 zn2z **)

  let zn2z_map f = function
  | W0 -> W0
  | WW (h, l) -> WW ((f h), (f l))

  (** val plus_t : int -> int -> dom_t word -> dom_t **)

  let rec plus_t n0 m x =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun m0 -> succ_t (add m0 n0) (zn2z_map (plus_t n0 m0) (Obj.magic x)))
      m

  (** val mk_t_w : int -> int -> dom_t word -> t **)

  let mk_t_w n0 m x =
    mk_t (add m n0) (plus_t n0 m x)

  (** val mk_t_0w : int -> Uint63Cyclic.t word -> t **)

  let mk_t_0w m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic (fun x -> N1 x))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic (fun x -> N2 x))
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic (fun x -> N3 x))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic (fun x -> N4 x))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Obj.magic (fun x -> N5 x))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> Obj.magic (fun x -> N6 x))
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ x -> Nn (0, x))
                  (fun n6 ->
                  mk_t_w 0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ (Stdlib.Int.succ n6)))))))))
                  n5)
                n4)
              n3)
            n2)
          n1)
        n0)
      m

  (** val mk_t_1w : int -> w1 word -> t **)

  let mk_t_1w m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic (fun x -> N2 x))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic (fun x -> N3 x))
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic (fun x -> N4 x))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic (fun x -> N5 x))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Obj.magic (fun x -> N6 x))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ x -> Nn (0, x))
                (fun n5 ->
                mk_t_w (Stdlib.Int.succ 0) (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ n5))))))))
                n4)
              n3)
            n2)
          n1)
        n0)
      m

  (** val mk_t_2w : int -> w2 word -> t **)

  let mk_t_2w m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic (fun x -> N3 x))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic (fun x -> N4 x))
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic (fun x -> N5 x))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic (fun x -> N6 x))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ x -> Nn (0, x))
              (fun n4 ->
              mk_t_w (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ n4)))))))
              n3)
            n2)
          n1)
        n0)
      m

  (** val mk_t_3w : int -> w3 word -> t **)

  let mk_t_3w m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic (fun x -> N4 x))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic (fun x -> N5 x))
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic (fun x -> N6 x))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ x -> Nn (0, x))
            (fun n3 ->
            mk_t_w (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ n3))))))
            n2)
          n1)
        n0)
      m

  (** val mk_t_4w : int -> w4 word -> t **)

  let mk_t_4w m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic (fun x -> N5 x))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic (fun x -> N6 x))
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ x -> Nn (0, x))
          (fun n2 ->
          mk_t_w (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ 0)))) (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ n2)))))
          n1)
        n0)
      m

  (** val mk_t_5w : int -> w5 word -> t **)

  let mk_t_5w m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic (fun x -> N6 x))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ x -> Nn (0, x))
        (fun n1 ->
        mk_t_w (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ 0))))) (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ n1))))
        n0)
      m

  (** val extend_size : int -> dom_t -> dom_t word **)

  let extend_size =
    extend (fun x -> WW ((Obj.magic W0), x))

  (** val eq00 : Uint63Cyclic.t -> bool **)

  let eq00 =
    Uint63Cyclic.ops.ZnZ.eq0

  (** val eq01 : w1 -> bool **)

  let eq01 =
    w1_op.ZnZ.eq0

  (** val eq02 : w2 -> bool **)

  let eq02 =
    w2_op.ZnZ.eq0

  (** val eq03 : w3 -> bool **)

  let eq03 =
    w3_op.ZnZ.eq0

  (** val eq04 : w4 -> bool **)

  let eq04 =
    w4_op.ZnZ.eq0

  (** val eq05 : w5 -> bool **)

  let eq05 =
    w5_op.ZnZ.eq0

  (** val eq06 : w6 -> bool **)

  let eq06 =
    w6_op.ZnZ.eq0

  (** val reduce_0 : Uint63Cyclic.t -> t' **)

  let reduce_0 x =
    N0 x

  (** val reduce_1 : Uint63Cyclic.t zn2z -> t' **)

  let reduce_1 x = match x with
  | W0 -> N0 zero0
  | WW (xh, xl) -> if eq00 xh then reduce_0 xl else N1 x

  (** val reduce_2 : w1 zn2z -> t' **)

  let reduce_2 x = match x with
  | W0 -> N0 zero0
  | WW (xh, xl) -> if eq01 xh then reduce_1 xl else N2 x

  (** val reduce_3 : w2 zn2z -> t' **)

  let reduce_3 x = match x with
  | W0 -> N0 zero0
  | WW (xh, xl) -> if eq02 xh then reduce_2 xl else N3 x

  (** val reduce_4 : w3 zn2z -> t' **)

  let reduce_4 x = match x with
  | W0 -> N0 zero0
  | WW (xh, xl) -> if eq03 xh then reduce_3 xl else N4 x

  (** val reduce_5 : w4 zn2z -> t' **)

  let reduce_5 x = match x with
  | W0 -> N0 zero0
  | WW (xh, xl) -> if eq04 xh then reduce_4 xl else N5 x

  (** val reduce_6 : w5 zn2z -> t' **)

  let reduce_6 x = match x with
  | W0 -> N0 zero0
  | WW (xh, xl) -> if eq05 xh then reduce_5 xl else N6 x

  (** val reduce_7 : w6 zn2z -> t' **)

  let reduce_7 x = match x with
  | W0 -> N0 zero0
  | WW (xh, xl) -> if eq06 xh then reduce_6 xl else Nn (0, (Obj.magic x))

  (** val reduce_n : int -> w6 word -> t' **)

  let rec reduce_n n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic reduce_7)
      (fun m x ->
      match Obj.magic x with
      | W0 -> N0 zero0
      | WW (xh, xl) ->
        (match xh with
         | W0 -> Obj.magic reduce_n m xl
         | WW (_, _) -> Nn ((Stdlib.Int.succ m), x)))
      n0

  (** val reduce : int -> dom_t -> t **)

  let reduce n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Obj.magic reduce_0)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Obj.magic reduce_1)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic reduce_2)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Obj.magic reduce_3)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Obj.magic reduce_4)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> Obj.magic reduce_5)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> Obj.magic reduce_6)
                  (fun n7 -> reduce_n n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0

  (** val zero : t **)

  let zero =
    mk_t 0 (Obj.magic Uint63Cyclic.ops).ZnZ.zero

  (** val one : t **)

  let one =
    mk_t 0 (Obj.magic Uint63Cyclic.ops).ZnZ.one

  (** val add : t -> t -> t **)

  let add =
    let f0 =
      let add_c0 = Uint63Cyclic.ops.ZnZ.add_c in
      let one0 = Uint63Cyclic.ops.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> N0 r
      | Uint63.C1 r -> N1 (WW (one0, r)))
    in
    let f1 =
      let add_c0 = w1_op.ZnZ.add_c in
      let one0 = w1_op.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> N1 r
      | Uint63.C1 r -> N2 (WW (one0, r)))
    in
    let f2 =
      let add_c0 = w2_op.ZnZ.add_c in
      let one0 = w2_op.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> N2 r
      | Uint63.C1 r -> N3 (WW (one0, r)))
    in
    let f3 =
      let add_c0 = w3_op.ZnZ.add_c in
      let one0 = w3_op.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> N3 r
      | Uint63.C1 r -> N4 (WW (one0, r)))
    in
    let f4 =
      let add_c0 = w4_op.ZnZ.add_c in
      let one0 = w4_op.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> N4 r
      | Uint63.C1 r -> N5 (WW (one0, r)))
    in
    let f5 =
      let add_c0 = w5_op.ZnZ.add_c in
      let one0 = w5_op.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> N5 r
      | Uint63.C1 r -> N6 (WW (one0, r)))
    in
    let f6 =
      let add_c0 = w6_op.ZnZ.add_c in
      let one0 = w6_op.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> N6 r
      | Uint63.C1 r -> Nn (0, (Obj.magic (WW (one0, r)))))
    in
    let fn = fun n0 ->
      let op = make_op n0 in
      let add_c0 = op.ZnZ.add_c in
      let one0 = op.ZnZ.one in
      (fun x y ->
      match add_c0 x y with
      | Uint63.C0 r -> Nn (n0, r)
      | Uint63.C1 r -> Nn ((Stdlib.Int.succ n0), (Obj.magic (WW (one0, r)))))
    in
    (fun x y ->
    match x with
    | N0 wx ->
      (match y with
       | N0 wy -> f0 wx wy
       | N1 wy -> f1 (WW (zero0, wx)) wy
       | N2 wy -> f2 (WW (W0, (WW (zero0, wx)))) wy
       | N3 wy -> f3 (WW (W0, (WW (W0, (WW (zero0, wx)))))) wy
       | N4 wy -> f4 (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wx)))))))) wy
       | N5 wy ->
         f5 (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wx)))))))))) wy
       | N6 wy ->
         f6 (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
           wx)))))))))))) wy
       | Nn (m, wy) ->
         fn m
           (extend_size m
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW
               (zero0, wx))))))))))))))
           wy)
    | N1 wx ->
      (match y with
       | N0 wy -> f1 wx (WW (zero0, wy))
       | N1 wy -> f1 wx wy
       | N2 wy -> f2 (WW (W0, wx)) wy
       | N3 wy -> f3 (WW (W0, (WW (W0, wx)))) wy
       | N4 wy -> f4 (WW (W0, (WW (W0, (WW (W0, wx)))))) wy
       | N5 wy -> f5 (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))) wy
       | N6 wy ->
         f6 (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))))) wy
       | Nn (m, wy) ->
         fn m
           (extend_size m
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0,
               wx))))))))))))
           wy)
    | N2 wx ->
      (match y with
       | N0 wy -> f2 wx (WW (W0, (WW (zero0, wy))))
       | N1 wy -> f2 wx (WW (W0, wy))
       | N2 wy -> f2 wx wy
       | N3 wy -> f3 (WW (W0, wx)) wy
       | N4 wy -> f4 (WW (W0, (WW (W0, wx)))) wy
       | N5 wy -> f5 (WW (W0, (WW (W0, (WW (W0, wx)))))) wy
       | N6 wy -> f6 (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))) wy
       | Nn (m, wy) ->
         fn m
           (extend_size m
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx))))))))))
           wy)
    | N3 wx ->
      (match y with
       | N0 wy -> f3 wx (WW (W0, (WW (W0, (WW (zero0, wy))))))
       | N1 wy -> f3 wx (WW (W0, (WW (W0, wy))))
       | N2 wy -> f3 wx (WW (W0, wy))
       | N3 wy -> f3 wx wy
       | N4 wy -> f4 (WW (W0, wx)) wy
       | N5 wy -> f5 (WW (W0, (WW (W0, wx)))) wy
       | N6 wy -> f6 (WW (W0, (WW (W0, (WW (W0, wx)))))) wy
       | Nn (m, wy) ->
         fn m (extend_size m (Obj.magic (WW (W0, (WW (W0, (WW (W0, wx))))))))
           wy)
    | N4 wx ->
      (match y with
       | N0 wy -> f4 wx (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wy))))))))
       | N1 wy -> f4 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N2 wy -> f4 wx (WW (W0, (WW (W0, wy))))
       | N3 wy -> f4 wx (WW (W0, wy))
       | N4 wy -> f4 wx wy
       | N5 wy -> f5 (WW (W0, wx)) wy
       | N6 wy -> f6 (WW (W0, (WW (W0, wx)))) wy
       | Nn (m, wy) ->
         fn m (extend_size m (Obj.magic (WW (W0, (WW (W0, wx)))))) wy)
    | N5 wx ->
      (match y with
       | N0 wy ->
         f5 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wy))))))))))
       | N1 wy -> f5 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N2 wy -> f5 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N3 wy -> f5 wx (WW (W0, (WW (W0, wy))))
       | N4 wy -> f5 wx (WW (W0, wy))
       | N5 wy -> f5 wx wy
       | N6 wy -> f6 (WW (W0, wx)) wy
       | Nn (m, wy) -> fn m (extend_size m (Obj.magic (WW (W0, wx)))) wy)
    | N6 wx ->
      (match y with
       | N0 wy ->
         f6 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
           wy))))))))))))
       | N1 wy ->
         f6 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))))
       | N2 wy -> f6 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N3 wy -> f6 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N4 wy -> f6 wx (WW (W0, (WW (W0, wy))))
       | N5 wy -> f6 wx (WW (W0, wy))
       | N6 wy -> f6 wx wy
       | Nn (m, wy) -> fn m (extend_size m (Obj.magic wx)) wy)
    | Nn (n0, wx) ->
      (match y with
       | N0 wy ->
         fn n0 wx
           (extend_size n0
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW
               (zero0, wy))))))))))))))
       | N1 wy ->
         fn n0 wx
           (extend_size n0
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0,
               wy))))))))))))
       | N2 wy ->
         fn n0 wx
           (extend_size n0
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))))
       | N3 wy ->
         fn n0 wx
           (extend_size n0 (Obj.magic (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N4 wy ->
         fn n0 wx (extend_size n0 (Obj.magic (WW (W0, (WW (W0, wy))))))
       | N5 wy -> fn n0 wx (extend_size n0 (Obj.magic (WW (W0, wy))))
       | N6 wy -> fn n0 wx (extend_size n0 (Obj.magic wy))
       | Nn (m, wy) ->
         let mn = Nat.max n0 m in
         let d = diff n0 m in
         fn mn
           (castm (add (snd (diff n0 m)) n0) (Nat.max n0 m)
             (extend_tr n0 wx (snd d)))
           (castm (add (fst (diff n0 m)) m) (Nat.max n0 m)
             (extend_tr m wy (fst d)))))

  (** val sub : t -> t -> t **)

  let sub =
    let f0 =
      let sub_c0 = Uint63Cyclic.ops.ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_0 r
      | Uint63.C1 _ -> zero)
    in
    let f1 =
      let sub_c0 = w1_op.ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_1 r
      | Uint63.C1 _ -> zero)
    in
    let f2 =
      let sub_c0 = w2_op.ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_2 r
      | Uint63.C1 _ -> zero)
    in
    let f3 =
      let sub_c0 = w3_op.ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_3 r
      | Uint63.C1 _ -> zero)
    in
    let f4 =
      let sub_c0 = w4_op.ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_4 r
      | Uint63.C1 _ -> zero)
    in
    let f5 =
      let sub_c0 = w5_op.ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_5 r
      | Uint63.C1 _ -> zero)
    in
    let f6 =
      let sub_c0 = w6_op.ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_6 r
      | Uint63.C1 _ -> zero)
    in
    let fn = fun n0 ->
      let sub_c0 = (make_op n0).ZnZ.sub_c in
      (fun x y ->
      match sub_c0 x y with
      | Uint63.C0 r -> reduce_n n0 r
      | Uint63.C1 _ -> zero)
    in
    (fun x y ->
    match x with
    | N0 wx ->
      (match y with
       | N0 wy -> f0 wx wy
       | N1 wy -> f1 (WW (zero0, wx)) wy
       | N2 wy -> f2 (WW (W0, (WW (zero0, wx)))) wy
       | N3 wy -> f3 (WW (W0, (WW (W0, (WW (zero0, wx)))))) wy
       | N4 wy -> f4 (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wx)))))))) wy
       | N5 wy ->
         f5 (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wx)))))))))) wy
       | N6 wy ->
         f6 (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
           wx)))))))))))) wy
       | Nn (m, wy) ->
         fn m
           (extend_size m
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW
               (zero0, wx))))))))))))))
           wy)
    | N1 wx ->
      (match y with
       | N0 wy -> f1 wx (WW (zero0, wy))
       | N1 wy -> f1 wx wy
       | N2 wy -> f2 (WW (W0, wx)) wy
       | N3 wy -> f3 (WW (W0, (WW (W0, wx)))) wy
       | N4 wy -> f4 (WW (W0, (WW (W0, (WW (W0, wx)))))) wy
       | N5 wy -> f5 (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))) wy
       | N6 wy ->
         f6 (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))))) wy
       | Nn (m, wy) ->
         fn m
           (extend_size m
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0,
               wx))))))))))))
           wy)
    | N2 wx ->
      (match y with
       | N0 wy -> f2 wx (WW (W0, (WW (zero0, wy))))
       | N1 wy -> f2 wx (WW (W0, wy))
       | N2 wy -> f2 wx wy
       | N3 wy -> f3 (WW (W0, wx)) wy
       | N4 wy -> f4 (WW (W0, (WW (W0, wx)))) wy
       | N5 wy -> f5 (WW (W0, (WW (W0, (WW (W0, wx)))))) wy
       | N6 wy -> f6 (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))) wy
       | Nn (m, wy) ->
         fn m
           (extend_size m
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx))))))))))
           wy)
    | N3 wx ->
      (match y with
       | N0 wy -> f3 wx (WW (W0, (WW (W0, (WW (zero0, wy))))))
       | N1 wy -> f3 wx (WW (W0, (WW (W0, wy))))
       | N2 wy -> f3 wx (WW (W0, wy))
       | N3 wy -> f3 wx wy
       | N4 wy -> f4 (WW (W0, wx)) wy
       | N5 wy -> f5 (WW (W0, (WW (W0, wx)))) wy
       | N6 wy -> f6 (WW (W0, (WW (W0, (WW (W0, wx)))))) wy
       | Nn (m, wy) ->
         fn m (extend_size m (Obj.magic (WW (W0, (WW (W0, (WW (W0, wx))))))))
           wy)
    | N4 wx ->
      (match y with
       | N0 wy -> f4 wx (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wy))))))))
       | N1 wy -> f4 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N2 wy -> f4 wx (WW (W0, (WW (W0, wy))))
       | N3 wy -> f4 wx (WW (W0, wy))
       | N4 wy -> f4 wx wy
       | N5 wy -> f5 (WW (W0, wx)) wy
       | N6 wy -> f6 (WW (W0, (WW (W0, wx)))) wy
       | Nn (m, wy) ->
         fn m (extend_size m (Obj.magic (WW (W0, (WW (W0, wx)))))) wy)
    | N5 wx ->
      (match y with
       | N0 wy ->
         f5 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0, wy))))))))))
       | N1 wy -> f5 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N2 wy -> f5 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N3 wy -> f5 wx (WW (W0, (WW (W0, wy))))
       | N4 wy -> f5 wx (WW (W0, wy))
       | N5 wy -> f5 wx wy
       | N6 wy -> f6 (WW (W0, wx)) wy
       | Nn (m, wy) -> fn m (extend_size m (Obj.magic (WW (W0, wx)))) wy)
    | N6 wx ->
      (match y with
       | N0 wy ->
         f6 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
           wy))))))))))))
       | N1 wy ->
         f6 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))))
       | N2 wy -> f6 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N3 wy -> f6 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N4 wy -> f6 wx (WW (W0, (WW (W0, wy))))
       | N5 wy -> f6 wx (WW (W0, wy))
       | N6 wy -> f6 wx wy
       | Nn (m, wy) -> fn m (extend_size m (Obj.magic wx)) wy)
    | Nn (n0, wx) ->
      (match y with
       | N0 wy ->
         fn n0 wx
           (extend_size n0
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW
               (zero0, wy))))))))))))))
       | N1 wy ->
         fn n0 wx
           (extend_size n0
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0,
               wy))))))))))))
       | N2 wy ->
         fn n0 wx
           (extend_size n0
             (Obj.magic (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))))
       | N3 wy ->
         fn n0 wx
           (extend_size n0 (Obj.magic (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N4 wy ->
         fn n0 wx (extend_size n0 (Obj.magic (WW (W0, (WW (W0, wy))))))
       | N5 wy -> fn n0 wx (extend_size n0 (Obj.magic (WW (W0, wy))))
       | N6 wy -> fn n0 wx (extend_size n0 (Obj.magic wy))
       | Nn (m, wy) ->
         let mn = Nat.max n0 m in
         let d = diff n0 m in
         fn mn
           (castm (Coq__1.add (snd (diff n0 m)) n0) (Nat.max n0 m)
             (extend_tr n0 wx (snd d)))
           (castm (Coq__1.add (fst (diff n0 m)) m) (Nat.max n0 m)
             (extend_tr m wy (fst d)))))

  (** val comparenm : int -> int -> w6 word -> w6 word -> comparison **)

  let comparenm n0 m wx wy =
    let mn = Nat.max n0 m in
    let d = diff n0 m in
    let op = make_op mn in
    op.ZnZ.compare
      (castm (Coq__1.add (snd (diff n0 m)) n0) (Nat.max n0 m)
        (extend_tr n0 wx (snd d)))
      (castm (Coq__1.add (fst (diff n0 m)) m) (Nat.max n0 m)
        (extend_tr m wy (fst d)))

  (** val compare : t -> t -> comparison **)

  let compare =
    let f0 = Uint63Cyclic.ops.ZnZ.compare in
    let f1 = w1_op.ZnZ.compare in
    let f2 = w2_op.ZnZ.compare in
    let f3 = w3_op.ZnZ.compare in
    let f4 = w4_op.ZnZ.compare in
    let f5 = w5_op.ZnZ.compare in
    let f6 = w6_op.ZnZ.compare in
    let fn0 =
      let zero1 = Uint63Cyclic.ops.ZnZ.zero in
      let compare1 = Uint63Cyclic.ops.ZnZ.compare in
      let compare2 = compare1 zero1 in
      (fun m ->
      compare_mn_1 zero1 compare1 compare2 compare1 (Stdlib.Int.succ m))
    in
    let fn1 =
      let zero1 = w1_op.ZnZ.zero in
      let compare1 = w1_op.ZnZ.compare in
      let compare2 = compare1 zero1 in
      (fun m ->
      compare_mn_1 zero1 compare1 compare2 compare1 (Stdlib.Int.succ m))
    in
    let fn2 =
      let zero1 = w2_op.ZnZ.zero in
      let compare1 = w2_op.ZnZ.compare in
      let compare2 = compare1 zero1 in
      (fun m ->
      compare_mn_1 zero1 compare1 compare2 compare1 (Stdlib.Int.succ m))
    in
    let fn3 =
      let zero1 = w3_op.ZnZ.zero in
      let compare1 = w3_op.ZnZ.compare in
      let compare2 = compare1 zero1 in
      (fun m ->
      compare_mn_1 zero1 compare1 compare2 compare1 (Stdlib.Int.succ m))
    in
    let fn4 =
      let zero1 = w4_op.ZnZ.zero in
      let compare1 = w4_op.ZnZ.compare in
      let compare2 = compare1 zero1 in
      (fun m ->
      compare_mn_1 zero1 compare1 compare2 compare1 (Stdlib.Int.succ m))
    in
    let fn5 =
      let zero1 = w5_op.ZnZ.zero in
      let compare1 = w5_op.ZnZ.compare in
      let compare2 = compare1 zero1 in
      (fun m ->
      compare_mn_1 zero1 compare1 compare2 compare1 (Stdlib.Int.succ m))
    in
    let fn6 =
      let zero1 = w6_op.ZnZ.zero in
      let compare1 = w6_op.ZnZ.compare in
      let compare2 = compare1 zero1 in
      (fun m ->
      compare_mn_1 zero1 compare1 compare2 compare1 (Stdlib.Int.succ m))
    in
    (fun x y ->
    match x with
    | N0 wx ->
      (match y with
       | N0 wy -> f0 wx wy
       | N1 wy -> compOpp (Obj.magic fn0 0 wy wx)
       | N2 wy -> compOpp (Obj.magic fn0 (Stdlib.Int.succ 0) wy wx)
       | N3 wy ->
         compOpp (Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx)
       | N4 wy ->
         compOpp
           (Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             0))) wy wx)
       | N5 wy ->
         compOpp
           (Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))) wy wx)
       | N6 wy ->
         compOpp
           (Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ 0))))) wy wx)
       | Nn (m, wy) ->
         compOpp
           (fn6 m wy (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
             wx))))))))))))))
    | N1 wx ->
      (match y with
       | N0 wy -> Obj.magic fn0 0 wx wy
       | N1 wy -> f1 wx wy
       | N2 wy -> compOpp (Obj.magic fn1 0 wy wx)
       | N3 wy -> compOpp (Obj.magic fn1 (Stdlib.Int.succ 0) wy wx)
       | N4 wy ->
         compOpp (Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx)
       | N5 wy ->
         compOpp
           (Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             0))) wy wx)
       | N6 wy ->
         compOpp
           (Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))) wy wx)
       | Nn (m, wy) ->
         compOpp
           (fn6 m wy (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0,
             wx))))))))))))
    | N2 wx ->
      (match y with
       | N0 wy -> Obj.magic fn0 (Stdlib.Int.succ 0) wx wy
       | N1 wy -> Obj.magic fn1 0 wx wy
       | N2 wy -> f2 wx wy
       | N3 wy -> compOpp (Obj.magic fn2 0 wy wx)
       | N4 wy -> compOpp (Obj.magic fn2 (Stdlib.Int.succ 0) wy wx)
       | N5 wy ->
         compOpp (Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx)
       | N6 wy ->
         compOpp
           (Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             0))) wy wx)
       | Nn (m, wy) ->
         compOpp (fn6 m wy (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx))))))))))
    | N3 wx ->
      (match y with
       | N0 wy -> Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N1 wy -> Obj.magic fn1 (Stdlib.Int.succ 0) wx wy
       | N2 wy -> Obj.magic fn2 0 wx wy
       | N3 wy -> f3 wx wy
       | N4 wy -> compOpp (Obj.magic fn3 0 wy wx)
       | N5 wy -> compOpp (Obj.magic fn3 (Stdlib.Int.succ 0) wy wx)
       | N6 wy ->
         compOpp (Obj.magic fn3 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx)
       | Nn (m, wy) -> compOpp (fn6 m wy (WW (W0, (WW (W0, (WW (W0, wx))))))))
    | N4 wx ->
      (match y with
       | N0 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wx wy
       | N1 wy -> Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N2 wy -> Obj.magic fn2 (Stdlib.Int.succ 0) wx wy
       | N3 wy -> Obj.magic fn3 0 wx wy
       | N4 wy -> f4 wx wy
       | N5 wy -> compOpp (Obj.magic fn4 0 wy wx)
       | N6 wy -> compOpp (Obj.magic fn4 (Stdlib.Int.succ 0) wy wx)
       | Nn (m, wy) -> compOpp (fn6 m wy (WW (W0, (WW (W0, wx))))))
    | N5 wx ->
      (match y with
       | N0 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))) wx wy
       | N1 wy ->
         Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wx wy
       | N2 wy -> Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N3 wy -> Obj.magic fn3 (Stdlib.Int.succ 0) wx wy
       | N4 wy -> Obj.magic fn4 0 wx wy
       | N5 wy -> f5 wx wy
       | N6 wy -> compOpp (Obj.magic fn5 0 wy wx)
       | Nn (m, wy) -> compOpp (fn6 m wy (WW (W0, wx))))
    | N6 wx ->
      (match y with
       | N0 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ 0))))) wx wy
       | N1 wy ->
         Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))) wx wy
       | N2 wy ->
         Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wx wy
       | N3 wy -> Obj.magic fn3 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N4 wy -> Obj.magic fn4 (Stdlib.Int.succ 0) wx wy
       | N5 wy -> Obj.magic fn5 0 wx wy
       | N6 wy -> f6 wx wy
       | Nn (m, wy) -> compOpp (fn6 m wy wx))
    | Nn (n0, wx) ->
      (match y with
       | N0 wy ->
         fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
           wy))))))))))))
       | N1 wy ->
         fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))))
       | N2 wy -> fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N3 wy -> fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N4 wy -> fn6 n0 wx (WW (W0, (WW (W0, wy))))
       | N5 wy -> fn6 n0 wx (WW (W0, wy))
       | N6 wy -> fn6 n0 wx wy
       | Nn (m, wy) -> comparenm n0 m wx wy))

  (** val eqb : t -> t -> bool **)

  let eqb x y =
    match compare x y with
    | Eq -> true
    | _ -> false

  (** val mulnm : int -> int -> w6 word -> w6 word -> t' **)

  let mulnm n0 m x y =
    let mn = Nat.max n0 m in
    let d = diff n0 m in
    let op = make_op mn in
    reduce_n (Stdlib.Int.succ mn)
      (Obj.magic op.ZnZ.mul_c
        (castm (Coq__1.add (snd (diff n0 m)) n0) (Nat.max n0 m)
          (extend_tr n0 x (snd d)))
        (castm (Coq__1.add (fst (diff n0 m)) m) (Nat.max n0 m)
          (extend_tr m y (fst d))))

  (** val mul : t -> t -> t **)

  let mul =
    let f0 =
      let mul_c0 = Uint63Cyclic.ops.ZnZ.mul_c in
      (fun x y -> reduce_1 (mul_c0 x y))
    in
    let f1 =
      let mul_c0 = w1_op.ZnZ.mul_c in (fun x y -> reduce_2 (mul_c0 x y))
    in
    let f2 =
      let mul_c0 = w2_op.ZnZ.mul_c in (fun x y -> reduce_3 (mul_c0 x y))
    in
    let f3 =
      let mul_c0 = w3_op.ZnZ.mul_c in (fun x y -> reduce_4 (mul_c0 x y))
    in
    let f4 =
      let mul_c0 = w4_op.ZnZ.mul_c in (fun x y -> reduce_5 (mul_c0 x y))
    in
    let f5 =
      let mul_c0 = w5_op.ZnZ.mul_c in (fun x y -> reduce_6 (mul_c0 x y))
    in
    let f6 =
      let mul_c0 = w6_op.ZnZ.mul_c in
      (fun x y -> reduce_n 0 (Obj.magic mul_c0 x y))
    in
    let fn0 =
      let zero1 = Uint63Cyclic.ops.ZnZ.zero in
      let succ1 = Uint63Cyclic.ops.ZnZ.succ in
      let add_c0 = Uint63Cyclic.ops.ZnZ.add_c in
      let mul_c0 = Uint63Cyclic.ops.ZnZ.mul_c in
      let ww = ZnZ.coq_WW Uint63Cyclic.ops in
      let ow = ZnZ.coq_OW Uint63Cyclic.ops in
      let eq1 = Uint63Cyclic.ops.ZnZ.eq0 in
      let mul_add = fun x y r ->
        match mul_c0 x y with
        | W0 -> (zero1, r)
        | WW (h, l) ->
          (match add_c0 l r with
           | Uint63.C0 lr -> (h, lr)
           | Uint63.C1 lr -> ((succ1 h), lr))
      in
      let mul_add_n1 = double_mul_add_n1 zero1 ww ow mul_add in
      (fun m x y ->
      let (w, r) = mul_add_n1 (Stdlib.Int.succ m) x y zero1 in
      if eq1 w
      then mk_t_0w m r
      else mk_t_0w (Stdlib.Int.succ m)
             (Obj.magic (WW ((extend_aux m (WW (zero0, w))), r))))
    in
    let fn1 =
      let zero1 = w1_op.ZnZ.zero in
      let succ1 = w1_op.ZnZ.succ in
      let add_c0 = w1_op.ZnZ.add_c in
      let mul_c0 = w1_op.ZnZ.mul_c in
      let ww = ZnZ.coq_WW w1_op in
      let ow = ZnZ.coq_OW w1_op in
      let eq1 = w1_op.ZnZ.eq0 in
      let mul_add = fun x y r ->
        match mul_c0 x y with
        | W0 -> (zero1, r)
        | WW (h, l) ->
          (match add_c0 l r with
           | Uint63.C0 lr -> (h, lr)
           | Uint63.C1 lr -> ((succ1 h), lr))
      in
      let mul_add_n1 = double_mul_add_n1 zero1 ww ow mul_add in
      (fun m x y ->
      let (w, r) = mul_add_n1 (Stdlib.Int.succ m) x y zero1 in
      if eq1 w
      then mk_t_1w m r
      else mk_t_1w (Stdlib.Int.succ m)
             (Obj.magic (WW ((extend_aux m (WW (W0, w))), r))))
    in
    let fn2 =
      let zero1 = w2_op.ZnZ.zero in
      let succ1 = w2_op.ZnZ.succ in
      let add_c0 = w2_op.ZnZ.add_c in
      let mul_c0 = w2_op.ZnZ.mul_c in
      let ww = ZnZ.coq_WW w2_op in
      let ow = ZnZ.coq_OW w2_op in
      let eq1 = w2_op.ZnZ.eq0 in
      let mul_add = fun x y r ->
        match mul_c0 x y with
        | W0 -> (zero1, r)
        | WW (h, l) ->
          (match add_c0 l r with
           | Uint63.C0 lr -> (h, lr)
           | Uint63.C1 lr -> ((succ1 h), lr))
      in
      let mul_add_n1 = double_mul_add_n1 zero1 ww ow mul_add in
      (fun m x y ->
      let (w, r) = mul_add_n1 (Stdlib.Int.succ m) x y zero1 in
      if eq1 w
      then mk_t_2w m r
      else mk_t_2w (Stdlib.Int.succ m)
             (Obj.magic (WW ((extend_aux m (WW (W0, w))), r))))
    in
    let fn3 =
      let zero1 = w3_op.ZnZ.zero in
      let succ1 = w3_op.ZnZ.succ in
      let add_c0 = w3_op.ZnZ.add_c in
      let mul_c0 = w3_op.ZnZ.mul_c in
      let ww = ZnZ.coq_WW w3_op in
      let ow = ZnZ.coq_OW w3_op in
      let eq1 = w3_op.ZnZ.eq0 in
      let mul_add = fun x y r ->
        match mul_c0 x y with
        | W0 -> (zero1, r)
        | WW (h, l) ->
          (match add_c0 l r with
           | Uint63.C0 lr -> (h, lr)
           | Uint63.C1 lr -> ((succ1 h), lr))
      in
      let mul_add_n1 = double_mul_add_n1 zero1 ww ow mul_add in
      (fun m x y ->
      let (w, r) = mul_add_n1 (Stdlib.Int.succ m) x y zero1 in
      if eq1 w
      then mk_t_3w m r
      else mk_t_3w (Stdlib.Int.succ m)
             (Obj.magic (WW ((extend_aux m (WW (W0, w))), r))))
    in
    let fn4 =
      let zero1 = w4_op.ZnZ.zero in
      let succ1 = w4_op.ZnZ.succ in
      let add_c0 = w4_op.ZnZ.add_c in
      let mul_c0 = w4_op.ZnZ.mul_c in
      let ww = ZnZ.coq_WW w4_op in
      let ow = ZnZ.coq_OW w4_op in
      let eq1 = w4_op.ZnZ.eq0 in
      let mul_add = fun x y r ->
        match mul_c0 x y with
        | W0 -> (zero1, r)
        | WW (h, l) ->
          (match add_c0 l r with
           | Uint63.C0 lr -> (h, lr)
           | Uint63.C1 lr -> ((succ1 h), lr))
      in
      let mul_add_n1 = double_mul_add_n1 zero1 ww ow mul_add in
      (fun m x y ->
      let (w, r) = mul_add_n1 (Stdlib.Int.succ m) x y zero1 in
      if eq1 w
      then mk_t_4w m r
      else mk_t_4w (Stdlib.Int.succ m)
             (Obj.magic (WW ((extend_aux m (WW (W0, w))), r))))
    in
    let fn5 =
      let zero1 = w5_op.ZnZ.zero in
      let succ1 = w5_op.ZnZ.succ in
      let add_c0 = w5_op.ZnZ.add_c in
      let mul_c0 = w5_op.ZnZ.mul_c in
      let ww = ZnZ.coq_WW w5_op in
      let ow = ZnZ.coq_OW w5_op in
      let eq1 = w5_op.ZnZ.eq0 in
      let mul_add = fun x y r ->
        match mul_c0 x y with
        | W0 -> (zero1, r)
        | WW (h, l) ->
          (match add_c0 l r with
           | Uint63.C0 lr -> (h, lr)
           | Uint63.C1 lr -> ((succ1 h), lr))
      in
      let mul_add_n1 = double_mul_add_n1 zero1 ww ow mul_add in
      (fun m x y ->
      let (w, r) = mul_add_n1 (Stdlib.Int.succ m) x y zero1 in
      if eq1 w
      then mk_t_5w m r
      else mk_t_5w (Stdlib.Int.succ m)
             (Obj.magic (WW ((extend_aux m (WW (W0, w))), r))))
    in
    let fn6 =
      let zero1 = w6_op.ZnZ.zero in
      let succ1 = w6_op.ZnZ.succ in
      let add_c0 = w6_op.ZnZ.add_c in
      let mul_c0 = w6_op.ZnZ.mul_c in
      let ww = ZnZ.coq_WW w6_op in
      let ow = ZnZ.coq_OW w6_op in
      let eq1 = w6_op.ZnZ.eq0 in
      let mul_add = fun x y r ->
        match mul_c0 x y with
        | W0 -> (zero1, r)
        | WW (h, l) ->
          (match add_c0 l r with
           | Uint63.C0 lr -> (h, lr)
           | Uint63.C1 lr -> ((succ1 h), lr))
      in
      let mul_add_n1 = double_mul_add_n1 zero1 ww ow mul_add in
      (fun m x y ->
      let (w, r) = mul_add_n1 (Stdlib.Int.succ m) x y zero1 in
      if eq1 w
      then Nn (m, r)
      else Nn ((Stdlib.Int.succ m),
             (Obj.magic (WW ((extend_aux m (WW (W0, w))), r)))))
    in
    (fun x y ->
    match x with
    | N0 wx ->
      (match y with
       | N0 wy -> f0 wx wy
       | N1 wy -> Obj.magic fn0 0 wy wx
       | N2 wy -> Obj.magic fn0 (Stdlib.Int.succ 0) wy wx
       | N3 wy -> Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx
       | N4 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wy wx
       | N5 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))) wy wx
       | N6 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ 0))))) wy wx
       | Nn (m, wy) ->
         fn6 m wy (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
           wx)))))))))))))
    | N1 wx ->
      (match y with
       | N0 wy -> Obj.magic fn0 0 wx wy
       | N1 wy -> f1 wx wy
       | N2 wy -> Obj.magic fn1 0 wy wx
       | N3 wy -> Obj.magic fn1 (Stdlib.Int.succ 0) wy wx
       | N4 wy -> Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx
       | N5 wy ->
         Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wy wx
       | N6 wy ->
         Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))) wy wx
       | Nn (m, wy) ->
         fn6 m wy (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))))))
    | N2 wx ->
      (match y with
       | N0 wy -> Obj.magic fn0 (Stdlib.Int.succ 0) wx wy
       | N1 wy -> Obj.magic fn1 0 wx wy
       | N2 wy -> f2 wx wy
       | N3 wy -> Obj.magic fn2 0 wy wx
       | N4 wy -> Obj.magic fn2 (Stdlib.Int.succ 0) wy wx
       | N5 wy -> Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx
       | N6 wy ->
         Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wy wx
       | Nn (m, wy) -> fn6 m wy (WW (W0, (WW (W0, (WW (W0, (WW (W0, wx)))))))))
    | N3 wx ->
      (match y with
       | N0 wy -> Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N1 wy -> Obj.magic fn1 (Stdlib.Int.succ 0) wx wy
       | N2 wy -> Obj.magic fn2 0 wx wy
       | N3 wy -> f3 wx wy
       | N4 wy -> Obj.magic fn3 0 wy wx
       | N5 wy -> Obj.magic fn3 (Stdlib.Int.succ 0) wy wx
       | N6 wy -> Obj.magic fn3 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wy wx
       | Nn (m, wy) -> fn6 m wy (WW (W0, (WW (W0, (WW (W0, wx)))))))
    | N4 wx ->
      (match y with
       | N0 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wx wy
       | N1 wy -> Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N2 wy -> Obj.magic fn2 (Stdlib.Int.succ 0) wx wy
       | N3 wy -> Obj.magic fn3 0 wx wy
       | N4 wy -> f4 wx wy
       | N5 wy -> Obj.magic fn4 0 wy wx
       | N6 wy -> Obj.magic fn4 (Stdlib.Int.succ 0) wy wx
       | Nn (m, wy) -> fn6 m wy (WW (W0, (WW (W0, wx)))))
    | N5 wx ->
      (match y with
       | N0 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))) wx wy
       | N1 wy ->
         Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wx wy
       | N2 wy -> Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N3 wy -> Obj.magic fn3 (Stdlib.Int.succ 0) wx wy
       | N4 wy -> Obj.magic fn4 0 wx wy
       | N5 wy -> f5 wx wy
       | N6 wy -> Obj.magic fn5 0 wy wx
       | Nn (m, wy) -> fn6 m wy (WW (W0, wx)))
    | N6 wx ->
      (match y with
       | N0 wy ->
         Obj.magic fn0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ 0))))) wx wy
       | N1 wy ->
         Obj.magic fn1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0)))) wx wy
       | N2 wy ->
         Obj.magic fn2 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           0))) wx wy
       | N3 wy -> Obj.magic fn3 (Stdlib.Int.succ (Stdlib.Int.succ 0)) wx wy
       | N4 wy -> Obj.magic fn4 (Stdlib.Int.succ 0) wx wy
       | N5 wy -> Obj.magic fn5 0 wx wy
       | N6 wy -> f6 wx wy
       | Nn (m, wy) -> fn6 m wy wx)
    | Nn (n0, wx) ->
      (match y with
       | N0 wy ->
         fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (zero0,
           wy))))))))))))
       | N1 wy ->
         fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))))
       | N2 wy -> fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, (WW (W0, wy))))))))
       | N3 wy -> fn6 n0 wx (WW (W0, (WW (W0, (WW (W0, wy))))))
       | N4 wy -> fn6 n0 wx (WW (W0, (WW (W0, wy))))
       | N5 wy -> fn6 n0 wx (WW (W0, wy))
       | N6 wy -> fn6 n0 wx wy
       | Nn (m, wy) -> mulnm n0 m wx wy))

  (** val pheight : positive -> int **)

  let pheight p =
    pred (Coq_Pos.to_nat (get_height (dom_op 0).ZnZ.digits (plength p)))

  (** val of_pos : positive -> t **)

  let of_pos x =
    let n0 = pheight x in reduce n0 (snd ((dom_op n0).ZnZ.of_pos x))

  (** val of_N : n -> t **)

  let of_N = function
  | Coq__2.N0 -> zero
  | Npos p -> of_pos p
 end

module BigZ =
 struct
  type t_ =
  | Pos of BigN.t
  | Neg of BigN.t

  type t = t_

  (** val zero : t_ **)

  let zero =
    Pos BigN.zero

  (** val one : t_ **)

  let one =
    Pos BigN.one

  (** val minus_one : t_ **)

  let minus_one =
    Neg BigN.one

  (** val of_Z : z -> t_ **)

  let of_Z = function
  | Z0 -> zero
  | Zpos x0 -> Pos (BigN.of_N (Npos x0))
  | Zneg x0 -> Neg (BigN.of_N (Npos x0))

  (** val compare : t_ -> t_ -> comparison **)

  let compare x y =
    match x with
    | Pos nx ->
      (match y with
       | Pos ny -> BigN.compare nx ny
       | Neg ny ->
         (match BigN.compare nx BigN.zero with
          | Gt -> Gt
          | _ -> BigN.compare ny BigN.zero))
    | Neg nx ->
      (match y with
       | Pos ny ->
         (match BigN.compare BigN.zero nx with
          | Lt -> Lt
          | _ -> BigN.compare BigN.zero ny)
       | Neg ny -> BigN.compare ny nx)

  (** val to_N : t_ -> BigN.t **)

  let to_N = function
  | Pos nx -> nx
  | Neg nx -> nx

  (** val opp : t_ -> t_ **)

  let opp = function
  | Pos nx -> Neg nx
  | Neg nx -> Pos nx

  (** val add : t_ -> t_ -> t_ **)

  let add x y =
    match x with
    | Pos nx ->
      (match y with
       | Pos ny -> Pos (BigN.add nx ny)
       | Neg ny ->
         (match BigN.compare nx ny with
          | Eq -> zero
          | Lt -> Neg (BigN.sub ny nx)
          | Gt -> Pos (BigN.sub nx ny)))
    | Neg nx ->
      (match y with
       | Pos ny ->
         (match BigN.compare nx ny with
          | Eq -> zero
          | Lt -> Pos (BigN.sub ny nx)
          | Gt -> Neg (BigN.sub nx ny))
       | Neg ny -> Neg (BigN.add nx ny))

  (** val mul : t_ -> t_ -> t_ **)

  let mul x y =
    match x with
    | Pos nx ->
      (match y with
       | Pos ny -> Pos (BigN.mul nx ny)
       | Neg ny -> Neg (BigN.mul nx ny))
    | Neg nx ->
      (match y with
       | Pos ny -> Neg (BigN.mul nx ny)
       | Neg ny -> Pos (BigN.mul nx ny))
 end

module BigN_BigZ =
 struct
  (** val coq_Z_of_N : BigN.t -> BigZ.t_ **)

  let coq_Z_of_N x =
    BigZ.Pos x

  (** val coq_Zabs_N : BigZ.t_ -> BigN.t **)

  let coq_Zabs_N =
    BigZ.to_N
 end

module BigQ =
 struct
  type t_ =
  | Qz of BigZ.t
  | Qq of BigZ.t * BigN.t

  type t = t_

  (** val zero : t **)

  let zero =
    Qz BigZ.zero

  (** val compare : t -> t -> comparison **)

  let compare x y =
    match x with
    | Qz zx ->
      (match y with
       | Qz zy -> BigZ.compare zx zy
       | Qq (ny, dy) ->
         if BigN.eqb dy BigN.zero
         then BigZ.compare zx BigZ.zero
         else BigZ.compare (BigZ.mul zx (BigN_BigZ.coq_Z_of_N dy)) ny)
    | Qq (nx, dx) ->
      (match y with
       | Qz zy ->
         if BigN.eqb dx BigN.zero
         then BigZ.compare BigZ.zero zy
         else BigZ.compare nx (BigZ.mul zy (BigN_BigZ.coq_Z_of_N dx))
       | Qq (ny, dy) ->
         if BigN.eqb dx BigN.zero
         then if BigN.eqb dy BigN.zero then Eq else BigZ.compare BigZ.zero ny
         else if BigN.eqb dy BigN.zero
              then BigZ.compare nx BigZ.zero
              else BigZ.compare (BigZ.mul nx (BigN_BigZ.coq_Z_of_N dy))
                     (BigZ.mul ny (BigN_BigZ.coq_Z_of_N dx)))

  (** val eq_bool : t -> t -> bool **)

  let eq_bool n0 m =
    match compare n0 m with
    | Eq -> true
    | _ -> false

  (** val add : t -> t -> t **)

  let add x y =
    match x with
    | Qz zx ->
      (match y with
       | Qz zy -> Qz (BigZ.add zx zy)
       | Qq (ny, dy) ->
         if BigN.eqb dy BigN.zero
         then x
         else Qq ((BigZ.add (BigZ.mul zx (BigN_BigZ.coq_Z_of_N dy)) ny), dy))
    | Qq (nx, dx) ->
      if BigN.eqb dx BigN.zero
      then y
      else (match y with
            | Qz zy ->
              Qq ((BigZ.add nx (BigZ.mul zy (BigN_BigZ.coq_Z_of_N dx))), dx)
            | Qq (ny, dy) ->
              if BigN.eqb dy BigN.zero
              then x
              else let n0 =
                     BigZ.add (BigZ.mul nx (BigN_BigZ.coq_Z_of_N dy))
                       (BigZ.mul ny (BigN_BigZ.coq_Z_of_N dx))
                   in
                   let d = BigN.mul dx dy in Qq (n0, d))

  (** val opp : t -> t **)

  let opp = function
  | Qz zx -> Qz (BigZ.opp zx)
  | Qq (nx, dx) -> Qq ((BigZ.opp nx), dx)

  (** val sub : t -> t -> t **)

  let sub x y =
    add x (opp y)

  (** val mul : t -> t -> t **)

  let mul x y =
    match x with
    | Qz zx ->
      (match y with
       | Qz zy -> Qz (BigZ.mul zx zy)
       | Qq (ny, dy) -> Qq ((BigZ.mul zx ny), dy))
    | Qq (nx, dx) ->
      (match y with
       | Qz zy -> Qq ((BigZ.mul nx zy), dx)
       | Qq (ny, dy) -> Qq ((BigZ.mul nx ny), (BigN.mul dx dy)))

  (** val inv : t -> t **)

  let inv = function
  | Qz z0 ->
    (match BigZ.compare BigZ.zero z0 with
     | Eq -> zero
     | Lt -> Qq (BigZ.one, (BigN_BigZ.coq_Zabs_N z0))
     | Gt -> Qq (BigZ.minus_one, (BigN_BigZ.coq_Zabs_N z0)))
  | Qq (n0, d) ->
    (match BigZ.compare BigZ.zero n0 with
     | Eq -> zero
     | Lt -> Qq ((BigN_BigZ.coq_Z_of_N d), (BigN_BigZ.coq_Zabs_N n0))
     | Gt ->
       Qq ((BigZ.opp (BigN_BigZ.coq_Z_of_N d)), (BigN_BigZ.coq_Zabs_N n0)))

  (** val div : t -> t -> t **)

  let div x y =
    mul x (inv y)

  (** val eqb : t -> t -> bool **)

  let eqb =
    eq_bool
 end

type 't vector = { val0 : 't list; size0 : BigQ.t }

type c = BigQ.t * BigQ.t

(** val width : int **)

let width =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val height : int **)

let height =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))

(** val iterations : int **)

let iterations =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))

(** val inject_nat : int -> BigQ.t **)

let inject_nat n0 =
  BigQ.Qq ((BigZ.of_Z (Coq_Z.of_nat n0)), (BigN.N0 (Uint63.of_int (1))))

(** val lebQ : BigQ.t -> BigQ.t -> bool **)

let lebQ alpha beta =
  match BigQ.compare alpha beta with
  | Gt -> false
  | _ -> true

(** val toChar : BigQ.t -> char list **)

let toChar q =
  if BigQ.eqb q (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (0)))))
  then '-'::[]
  else if BigQ.eqb q (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (1)))))
       then '#'::[]
       else if BigQ.eqb q (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (2)))))
            then '%'::[]
            else ' '::[]

(** val scale : c -> c **)

let scale coord =
  let scaleX =
    BigQ.div (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (3)))))
      (inject_nat width)
  in
  let scaleY =
    BigQ.div (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (2)))))
      (inject_nat height)
  in
  let lowerX = BigQ.Qz (BigZ.Neg (BigN.N0 (Uint63.of_int (2)))) in
  let lowerY = BigQ.Qq ((BigZ.Neg (BigN.N0 (Uint63.of_int (12)))), (BigN.N0
    (Uint63.of_int (10))))
  in
  ((BigQ.add (BigQ.mul (fst coord) scaleX) lowerX),
  (BigQ.add (BigQ.mul (snd coord) scaleY) lowerY))

(** val points : c list **)

let points =
  sort (fun x y -> lebQ (snd x) (snd y))
    (map scale
      (flat_map (fun x ->
        map (fun y -> ((inject_nat x), (inject_nat y))) (seq 0 height))
        (seq 0 width)))

(** val cPlus : c -> c -> c **)

let cPlus c1 c2 =
  ((BigQ.add (fst c1) (fst c2)), (BigQ.add (snd c1) (snd c2)))

(** val cMul : c -> c -> c **)

let cMul c1 c2 =
  ((BigQ.sub (BigQ.mul (fst c1) (fst c2)) (BigQ.mul (snd c1) (snd c2))),
    (BigQ.add (BigQ.mul (fst c1) (snd c2)) (BigQ.mul (snd c1) (fst c2))))

(** val cModSq : c -> BigQ.t **)

let cModSq c1 =
  let x = fst c1 in let y = snd c1 in BigQ.add (BigQ.mul x x) (BigQ.mul y y)

(** val nAppl : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 vector **)

let nAppl f c0 n0 =
  let go =
    let rec go x n1 =
      let x' = f x in
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> [])
         (fun n' -> x' :: (go x' n'))
         n1)
    in go
  in
  { val0 = (go c0 n0); size0 = (inject_nat n0) }

(** val mandelbrotF : c -> c -> c **)

let mandelbrotF c0 z0 =
  cPlus (cMul z0 z0) c0

(** val nApplMandelbrot : c -> c -> int -> c vector **)

let nApplMandelbrot c0 z0 fuel =
  nAppl (mandelbrotF c0) z0 fuel

(** val escapeCount : c vector -> BigQ.t **)

let escapeCount l0 =
  let llength = l0.size0 in
  let sum' =
    fold_left (fun acc x ->
      if lebQ (cModSq x) (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (4)))))
      then acc
      else BigQ.add acc (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (1))))))
      l0.val0 (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (0)))))
  in
  if BigQ.eqb sum' (BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (0)))))
  then BigQ.Qz (BigZ.Pos (BigN.N0 (Uint63.of_int (0))))
  else BigQ.sub llength sum'

(** val buildStr : c list -> char list -> char list **)

let rec buildStr pts acc =
  match pts with
  | [] -> acc
  | c0 :: l ->
    buildStr (skipn width (c0 :: l))
      (append acc
        (append
          (concat []
            (map (fun x ->
              toChar
                (escapeCount
                  (nApplMandelbrot x ((BigQ.Qz (BigZ.Pos (BigN.N0
                    (Uint63.of_int (0))))), (BigQ.Qz (BigZ.Pos (BigN.N0
                    (Uint63.of_int (0)))))) iterations)))
              (firstn width (c0 :: l))))
          ((ascii_of_N (Npos (XO (XI (XO XH)))))::[])))

let () = 
  List.iter print_char (buildStr points [])
