
type __ = Obj.t

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val pred : int -> int

val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val max : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

type positive =
| XI of positive
| XO of positive
| XH

module Coq__2 : sig
 type n =
 | N0
 | Npos of positive
end
include module type of struct include Coq__2 end

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val of_succ_nat : int -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val pred_double : positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val pred : positive -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z
 end

module Coq_Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val of_nat : int -> z

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z
 end

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : positive -> char

val ascii_of_N : n -> char

val append : char list -> char list -> char list

val concat : char list -> char list list -> char list

val base : positive -> z

type 'znz zn2z =
| W0
| WW of 'znz * 'znz

val zn2z_to_Z : z -> ('a1 -> z) -> 'a1 zn2z -> z

type 'w word = __

val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val lor0 : Uint63.t -> Uint63.t -> Uint63.t

val lxor0 : Uint63.t -> Uint63.t -> Uint63.t

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val mulc : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val div0 : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val leb0 : Uint63.t -> Uint63.t -> bool

val addc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry

val addcarryc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry

val subc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry

val subcarryc : Uint63.t -> Uint63.t -> Uint63.t Uint63.carry

val diveucl : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val diveucl_21 : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val addmuldiv : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val compare0 : Uint63.t -> Uint63.t -> comparison

val head0 : Uint63.t -> Uint63.t

val tail0 : Uint63.t -> Uint63.t

val size : int

val digits : Uint63.t

val max_int : Uint63.t

val is_zero : Uint63.t -> bool

val is_even : Uint63.t -> bool

val to_Z_rec : int -> Uint63.t -> z

val to_Z : Uint63.t -> z

val addcarry : Uint63.t -> Uint63.t -> Uint63.t

val opp0 : Uint63.t -> Uint63.t

val oppcarry : Uint63.t -> Uint63.t

val succ0 : Uint63.t -> Uint63.t

val pred0 : Uint63.t -> Uint63.t

val subcarry : Uint63.t -> Uint63.t -> Uint63.t

val oppc : Uint63.t -> Uint63.t Uint63.carry

val succc : Uint63.t -> Uint63.t Uint63.carry

val predc : Uint63.t -> Uint63.t Uint63.carry

val iter_sqrt :
  int -> (Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t ->
  Uint63.t

val sqrt : Uint63.t -> Uint63.t

val high_bit : Uint63.t

val iter2_sqrt :
  int -> (Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t

val sqrt2 : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t Uint63.carry

val gcd_rec : int -> Uint63.t -> Uint63.t -> Uint63.t

val gcd : Uint63.t -> Uint63.t -> Uint63.t

type 't pred1 = 't -> bool

type 't rel = 't -> 't pred1

val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list

val merge_sort_rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

val sort : 'a1 rel -> 'a1 list -> 'a1 list

module ZnZ :
 sig
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

  val digits : 'a1 coq_Ops -> positive

  val zdigits : 'a1 coq_Ops -> 'a1

  val to_Z : 'a1 coq_Ops -> 'a1 -> z

  val of_pos : 'a1 coq_Ops -> positive -> n * 'a1

  val head0 : 'a1 coq_Ops -> 'a1 -> 'a1

  val tail0 : 'a1 coq_Ops -> 'a1 -> 'a1

  val zero : 'a1 coq_Ops -> 'a1

  val one : 'a1 coq_Ops -> 'a1

  val minus_one : 'a1 coq_Ops -> 'a1

  val compare : 'a1 coq_Ops -> 'a1 -> 'a1 -> comparison

  val eq0 : 'a1 coq_Ops -> 'a1 -> bool

  val opp_c : 'a1 coq_Ops -> 'a1 -> 'a1 Uint63.carry

  val opp : 'a1 coq_Ops -> 'a1 -> 'a1

  val opp_carry : 'a1 coq_Ops -> 'a1 -> 'a1

  val succ_c : 'a1 coq_Ops -> 'a1 -> 'a1 Uint63.carry

  val add_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry

  val add_carry_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry

  val succ : 'a1 coq_Ops -> 'a1 -> 'a1

  val add : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val add_carry : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val pred_c : 'a1 coq_Ops -> 'a1 -> 'a1 Uint63.carry

  val sub_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry

  val sub_carry_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 Uint63.carry

  val pred : 'a1 coq_Ops -> 'a1 -> 'a1

  val sub : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val sub_carry : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val mul_c : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 zn2z

  val mul : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val square_c : 'a1 coq_Ops -> 'a1 -> 'a1 zn2z

  val div21 : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 -> 'a1 * 'a1

  val div_gt : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 * 'a1

  val modulo_gt : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val gcd_gt : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val add_mul_div : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 -> 'a1

  val pos_mod : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val is_even : 'a1 coq_Ops -> 'a1 -> bool

  val sqrt2 : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 * 'a1 Uint63.carry

  val coq_lor : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val coq_land : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val coq_lxor : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1

  val coq_WO : 'a1 coq_Ops -> 'a1 -> 'a1 zn2z

  val coq_OW : 'a1 coq_Ops -> 'a1 -> 'a1 zn2z

  val coq_WW : 'a1 coq_Ops -> 'a1 -> 'a1 -> 'a1 zn2z
 end

val pdigits : positive

val positive_to_int_rec : int -> positive -> n * Uint63.t

val positive_to_int : positive -> n * Uint63.t

val mulc_WW : Uint63.t -> Uint63.t -> Uint63.t zn2z

val pos_mod0 : Uint63.t -> Uint63.t -> Uint63.t

val int_ops : Uint63.t ZnZ.coq_Ops

module Uint63Cyclic :
 sig
  type t = Uint63.t

  val ops : Uint63.t ZnZ.coq_Ops
 end

val ww_1 : 'a1 -> 'a1 -> 'a1 zn2z

val ww_Bm1 : 'a1 -> 'a1 zn2z

val double_WW :
  ('a1 -> 'a1 -> 'a1 zn2z) -> int -> 'a1 word -> 'a1 word -> 'a1 word

val extend_aux : int -> 'a1 zn2z -> 'a1 word

val extend : ('a1 -> 'a1 zn2z) -> int -> 'a1 -> 'a1 word

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Cons of 'a * 'a stream

val hd : 'a1 stream -> 'a1

val tl : 'a1 stream -> 'a1 stream

val memo_make : (int -> 'a1) -> int -> 'a1 stream

val memo_list : (int -> 'a1) -> 'a1 stream

val memo_get : int -> 'a1 stream -> 'a1

type 'a memo_val =
| Memo_mval of int * 'a

val is_eq : int -> int -> bool

val memo_get_val : (int -> 'a1) -> int -> 'a1 memo_val -> 'a1

val dmemo_list : (int -> 'a1) -> 'a1 memo_val stream

val dmemo_get : (int -> 'a1) -> int -> 'a1 memo_val stream -> 'a1

val w_2 : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1

val double_mul_add_n1 :
  'a1 -> ('a1 -> 'a1 -> 'a1 zn2z) -> ('a1 -> 'a1 zn2z) -> ('a1 -> 'a1 -> 'a1
  -> 'a1 * 'a1) -> int -> 'a1 word -> 'a1 -> 'a1 -> 'a1 * 'a1 word

val ww_is_even : ('a1 -> bool) -> 'a1 zn2z -> bool

val split : 'a1 -> 'a1 zn2z -> 'a1 * 'a1

val ww_is_zero : ('a1 zn2z -> 'a1 zn2z -> comparison) -> 'a1 zn2z -> bool

val ww_head1 :
  ('a1 -> bool) -> ('a1 zn2z -> 'a1 zn2z) -> ('a1 zn2z -> 'a1 zn2z) -> 'a1
  zn2z -> 'a1 zn2z

val high : 'a1 -> int -> 'a1 word -> 'a1

val lor1 : 'a1 ZnZ.coq_Ops -> 'a1 zn2z -> 'a1 zn2z -> 'a1 zn2z

val land1 : 'a1 ZnZ.coq_Ops -> 'a1 zn2z -> 'a1 zn2z -> 'a1 zn2z

val lxor1 : 'a1 ZnZ.coq_Ops -> 'a1 zn2z -> 'a1 zn2z -> 'a1 zn2z

val mk_zn2z_ops : 'a1 ZnZ.coq_Ops -> 'a1 zn2z ZnZ.coq_Ops

val mk_zn2z_ops_karatsuba : 'a1 ZnZ.coq_Ops -> 'a1 zn2z ZnZ.coq_Ops

val plength : positive -> positive

val pdiv : positive -> positive -> positive

val is_one : positive -> bool

val get_height : positive -> positive -> positive

val diff : int -> int -> int * int

val castm : int -> int -> 'a1 word -> 'a1 word

val extend_tr : int -> 'a1 word -> int -> 'a1 word

val compare0_mn : ('a1 -> comparison) -> int -> 'a1 word -> comparison

val compare_mn_1 :
  'a2 -> ('a2 -> 'a2 -> comparison) -> ('a1 -> comparison) -> ('a1 -> 'a2 ->
  comparison) -> int -> 'a1 word -> 'a2 -> comparison

module BigN :
 sig
  type w1 = Uint63Cyclic.t zn2z

  type w2 = w1 zn2z

  type w3 = w2 zn2z

  type w4 = w3 zn2z

  type w5 = w4 zn2z

  type w6 = w5 zn2z

  val w1_op : w1 ZnZ.coq_Ops

  val w2_op : w2 ZnZ.coq_Ops

  val w3_op : w3 ZnZ.coq_Ops

  val w4_op : w4 ZnZ.coq_Ops

  val w5_op : w5 ZnZ.coq_Ops

  val w6_op : w6 ZnZ.coq_Ops

  val w7_op : w6 word ZnZ.coq_Ops

  val w8_op : w6 word ZnZ.coq_Ops

  val w9_op : w6 word ZnZ.coq_Ops

  val make_op_aux :
    (__ -> __ ZnZ.coq_Ops -> __ zn2z ZnZ.coq_Ops) -> int -> w6 word
    ZnZ.coq_Ops

  val omake_op : int -> w6 word ZnZ.coq_Ops

  val make_op_list : w6 word ZnZ.coq_Ops memo_val stream

  val make_op : int -> w6 word ZnZ.coq_Ops

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

  val dom_op : int -> dom_t ZnZ.coq_Ops

  val mk_t : int -> dom_t -> t

  val zero0 : Uint63Cyclic.t

  val succ_t : int -> dom_t zn2z -> dom_t

  val zn2z_map : ('a1 -> 'a2) -> 'a1 zn2z -> 'a2 zn2z

  val plus_t : int -> int -> dom_t word -> dom_t

  val mk_t_w : int -> int -> dom_t word -> t

  val mk_t_0w : int -> Uint63Cyclic.t word -> t

  val mk_t_1w : int -> w1 word -> t

  val mk_t_2w : int -> w2 word -> t

  val mk_t_3w : int -> w3 word -> t

  val mk_t_4w : int -> w4 word -> t

  val mk_t_5w : int -> w5 word -> t

  val extend_size : int -> dom_t -> dom_t word

  val eq00 : Uint63Cyclic.t -> bool

  val eq01 : w1 -> bool

  val eq02 : w2 -> bool

  val eq03 : w3 -> bool

  val eq04 : w4 -> bool

  val eq05 : w5 -> bool

  val eq06 : w6 -> bool

  val reduce_0 : Uint63Cyclic.t -> t'

  val reduce_1 : Uint63Cyclic.t zn2z -> t'

  val reduce_2 : w1 zn2z -> t'

  val reduce_3 : w2 zn2z -> t'

  val reduce_4 : w3 zn2z -> t'

  val reduce_5 : w4 zn2z -> t'

  val reduce_6 : w5 zn2z -> t'

  val reduce_7 : w6 zn2z -> t'

  val reduce_n : int -> w6 word -> t'

  val reduce : int -> dom_t -> t

  val zero : t

  val one : t

  val add : t -> t -> t

  val sub : t -> t -> t

  val comparenm : int -> int -> w6 word -> w6 word -> comparison

  val compare : t -> t -> comparison

  val eqb : t -> t -> bool

  val mulnm : int -> int -> w6 word -> w6 word -> t'

  val mul : t -> t -> t

  val pheight : positive -> int

  val of_pos : positive -> t

  val of_N : n -> t
 end

module BigZ :
 sig
  type t_ =
  | Pos of BigN.t
  | Neg of BigN.t

  type t = t_

  val zero : t_

  val one : t_

  val minus_one : t_

  val of_Z : z -> t_

  val compare : t_ -> t_ -> comparison

  val to_N : t_ -> BigN.t

  val opp : t_ -> t_

  val add : t_ -> t_ -> t_

  val mul : t_ -> t_ -> t_
 end

module BigN_BigZ :
 sig
  val coq_Z_of_N : BigN.t -> BigZ.t_

  val coq_Zabs_N : BigZ.t_ -> BigN.t
 end

module BigQ :
 sig
  type t_ =
  | Qz of BigZ.t
  | Qq of BigZ.t * BigN.t

  type t = t_

  val zero : t

  val compare : t -> t -> comparison

  val eq_bool : t -> t -> bool

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val inv : t -> t

  val div : t -> t -> t

  val eqb : t -> t -> bool
 end

type 't vector = { val0 : 't list; size0 : BigQ.t }

type c = BigQ.t * BigQ.t

val width : int

val height : int

val iterations : int

val inject_nat : int -> BigQ.t

val lebQ : BigQ.t -> BigQ.t -> bool

val toChar : BigQ.t -> char list

val scale : c -> c

val points : c list

val cPlus : c -> c -> c

val cMul : c -> c -> c

val cModSq : c -> BigQ.t

val nAppl : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 vector

val mandelbrotF : c -> c -> c

val nApplMandelbrot : c -> c -> int -> c vector

val escapeCount : c vector -> BigQ.t

val buildStr : c list -> char list -> char list

val result : char list
