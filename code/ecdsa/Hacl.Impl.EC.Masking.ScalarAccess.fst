module Hacl.Impl.EC.Masking.ScalarAccess

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.Loops

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Impl.EC.Masking

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.PointDouble

open FStar.Mul

module BV = FStar.BitVector

open FStar.Math.Lemmas
open Hacl.Impl.EC.Masking.ScalarAccess.Lemmas


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val getScalarBit_leftEndian: #c: curve 
  -> #buf_type: buftype 
  -> s:lbuffer_t buf_type uint8 (getScalarLenBytes c) 
  -> n:size_t{v n < v (getScalarLen c)}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == ith_bit #c (as_seq h0 s) (v n) /\ v r <= 1)

let getScalarBit_leftEndian #c #buf_type s n =
  let h0 = ST.get () in
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1)); 
  to_u64 ((s.(getScalarLenBytes c -. 1ul -. n /. 8ul) >>. (n %. 8ul)) &. u8 1)


inline_for_extraction noextract
val getScalarBit_l: #c: curve 
  -> #buf_type: buftype 
  -> s:lbuffer_t buf_type uint8 (getScalarLenBytes c) 
  -> n:size_t{v n < v (getScalarLen c)}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ r == ith_bit #c (as_seq h0 s) (v n) /\ v r <= 1)

let getScalarBit_l #c #b s n = 
  push_frame();
    let temp = create (size 1) (u64 0) in 
    let h0 = ST.get() in 
    let inv h i = modifies (loc temp) h0 h /\ live h0 temp /\ (
      let temp0 = Lib.Sequence.index (as_seq h temp) 0 in v temp0 <= 1 /\ (
      if i > v n then v temp0 == v (ith_bit (as_seq h0 s) (v n)) else True)) in 

  for 0ul (getScalarLen c) inv (fun i -> 
    let bit = getScalarBit_leftEndian s n in 
    let mask = eq_mask (size_to_uint64 n) (size_to_uint64 i) in 
      eq_mask_lemma (size_to_uint64 n) (size_to_uint64 i);
    copy_conditional_u64 bit temp mask);

  let result = index temp (size 0) in
  let h1 = ST.get() in 
  pop_frame();
  result


val getScalar_4: #c: curve
  -> #buf_type: buftype 
  -> s: scalar_t #buf_type #c
  -> i: size_t {v i < v (getScalarLenBytes c) * 2} -> 
  Stack uint32
  (requires fun h -> live h s)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let radix = 4 in 
    v r == FStar.Math.Lib.arithmetic_shift_right (scalar_as_nat #c (as_seq h0 s)) (v (getScalarLen c) - (v i + 1) * radix) % pow2 radix))


let getScalar_4 #c scalar i = 
  let h0 = ST.get() in
  
  let half = shift_right i 1ul in 
    shift_right_lemma i 1ul;
  let word = to_u32 (index scalar half) in 
  let bitShift = logand i (size 1) in 
    logand_mask i (size 1) 1; 
  let bitShiftAsPrivate = size_to_uint32 bitShift in 
  
  let mask = cmovznz01 (u32 0xf0) (u32 0x0f) bitShiftAsPrivate in  
  let shiftMask = cmovznz01 (size 0x4) (size 0x0) bitShift in
  
  let result0 = logand word mask in 
  let result = shift_right result0 shiftMask in 

  let index = v i in 

  if index % 2 = 0 then 
    begin
      logand_spec word mask;
      lemma_and_both_parts_32 word mask;
      UInt.logand_lemma_1 #4 (v (get_low_part_4 word));
      UInt.logand_mask #32 (v word / pow2 4) 4; 
      assert (v result ==  (v (Lib.Sequence.index (as_seq h0 scalar) (index / 2)) / pow2 4) % pow2 4);

      let s = as_seq h0 scalar in 
      calc (==) {
	v result;
	   (==) {lemma_index_scalar_as_nat #c s (index / 2)}
	((scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 2) * 4) % pow2 8) / pow2 4) % pow2 4; 
	  (==) {pow2_modulo_division_lemma_1 (scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 2) * 4)) 4 8}
	((scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 2) * 4) / pow2 4) % pow2 4) % pow2 4;
	  (==) {lemma_mod_twice ((scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 2) * 4) / pow2 4)) (pow2 4)}
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 2) * 4) / pow2 4) % pow2 4; };

      calc (==) {
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 2) * 4) / pow2 4);
	(==) {division_multiplication_lemma (scalar_as_nat #c s) (pow2 (v (getScalarLen c) - (index + 2) * 4)) (pow2 4)}
	scalar_as_nat #c s / (pow2 (v (getScalarLen c) - (v i + 2) * 4) * pow2 4);
	(==) {pow2_plus (v (getScalarLen c) - (v i + 2) * 4) 4} 
	scalar_as_nat #c s / (pow2 (v (getScalarLen c) - (v i + 1) * 4));}

      end
  else
    begin

      logand_mask word mask 4;
      assert(v result = v (Lib.Sequence.index (as_seq h0 scalar) (index / 2)) % pow2 4);
      
      let s = as_seq h0 scalar in 

      calc (==) {
	v result;
      (==) {}
	v (Lib.Sequence.index (as_seq h0 scalar) (index / 2)) % pow2 4;
      (==) {lemma_index_scalar_as_nat #c s (index / 2)}
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index / 2 + 1) * 8) % pow2 8) % pow2 4;
      (==) {euclidean_division_definition index 2}
	(scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 1) * 4) % pow2 8) % pow2 4;
      (==) {pow2_modulo_modulo_lemma_1 (scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 1) * 4)) 4 8}
      	scalar_as_nat #c s / pow2 (v (getScalarLen c) - (index + 1) * 4) % pow2 4; }
    end;

  result

inline_for_extraction noextract
val getScalar_4_byBit: #c: curve
  -> #buf_type: buftype 
  -> s: scalar_t #buf_type #c
  -> i: size_t {v i < v (getScalarLenBytes c) * 2} -> 
  Stack uint64
  (requires fun h -> live h s)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    let radix = 4 in 
    v r == FStar.Math.Lib.arithmetic_shift_right (scalar_as_nat #c (as_seq h0 s)) (v (getScalarLen c) - (v i + 1) * radix) % pow2 radix))

let getScalar_4_byBit #c s i = 
  let h0 = ST.get() in 
  let bit = getScalarLen c -! 1ul -! (shift_left i 2ul) in 
  
  let bit0 = shift_left (getScalarBit_leftEndian s bit) 3ul in 
  let bit1 = shift_left (getScalarBit_leftEndian s (bit -! 1ul)) 2ul in 
  let bit2 = shift_left (getScalarBit_leftEndian s (bit -! 2ul)) 1ul in 
  let bit3 = shift_left (getScalarBit_leftEndian s (bit -! 3ul)) 0ul in 

  let r = logxor (logxor bit0 bit1) (logxor bit2 bit3) in 


  let l = v (getScalarLen c) in 
  
  assert(v bit0 = v (ith_bit (as_seq h0 s) (l - 1 - 4 * v i)) * 8);
  assert(v bit1 = v (ith_bit (as_seq h0 s) (l - 1 - 4 * v i - 1)) * 4);
  assert(v bit2 = v (ith_bit (as_seq h0 s) (l - 1 - 4 * v i - 2)) * 2);
  assert(v bit3 = v (ith_bit (as_seq h0 s) (l - 1 - 4 * v i - 3)));

  logxor_spec bit0 bit1;
  logxor_spec bit2 bit3;
  logxor_spec (logxor bit0 bit1) (logxor bit2 bit3);
  lemma_xor_of_4 
    (ith_bit (as_seq h0 s) (l - 1 - 4 * v i))
    (ith_bit (as_seq h0 s) (l - 1 - 4 * v i - 1)) 
    (ith_bit (as_seq h0 s) (l - 1 - 4 * v i - 2))
    (ith_bit (as_seq h0 s) (l - 1 - 4 * v i - 3));

  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 1);
  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 2);
  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 3);
  scalar_as_nat_def #c (as_seq h0 s) (4 * v i + 4);

  scalar_as_sub_radix4 (as_seq h0 s) (v i); 
  r




open Hacl.Impl.EC.Precomputed

inline_for_extraction noextract
val getPointPrecomputedMixed_: #c: curve -> scalar: scalar_t #MUT #c -> 
  i:size_t{v i < 64} -> pointToAdd: lbuffer uint64 (size 8) ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> True)

let getPointPrecomputedMixed_ #c scalar i pointToAdd = 
  push_frame();
    let bits = getScalar_4_byBit scalar i in 
  (*   let r =  shift_right (to_u64 bits) 18ul in 
    let bits = getScalar_4 #c scalar i in *)
   let invK h (k: nat) = True in 
    Lib.Loops.for 0ul 16ul invK
    (fun k -> 
      recall_contents points_radix_16 (Lib.Sequence.of_list points_radix_16_list_p256);
      let mask = eq_mask (to_u64 bits) (to_u64 k) in 
      let lut_cmb_x = sub points_radix_16 (k *! 8ul) (size 4) in 
      let lut_cmb_y = sub points_radix_16 (k *! 8ul +! (size 4)) (size 4) in 

      admit();
      copy_conditional #c (sub pointToAdd (size 0) (size 4)) lut_cmb_x mask;
      copy_conditional #c (sub pointToAdd (size 4) (size 4)) lut_cmb_y mask);
  pop_frame()


let getPointPrecomputedMixed_p256 = getPointPrecomputedMixed_ #P256


inline_for_extraction noextract
val getPointPrecomputedMixed: #c: curve -> scalar: lbuffer uint8 (size 32) -> 
  i:size_t{v i < 64} -> pointToAdd: lbuffer uint64 (size 8) ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h pointToAdd)
  (ensures fun h0 _ h1 -> True)

let getPointPrecomputedMixed scalar i pointToAdd = getPointPrecomputedMixed_p256 scalar i pointToAdd


