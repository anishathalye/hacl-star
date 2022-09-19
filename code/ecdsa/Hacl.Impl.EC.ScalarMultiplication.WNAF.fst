module Hacl.Impl.EC.ScalarMultiplication.WNAF

open FStar.HyperStack.All
open FStar.HyperStack

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.ECC.Curves
open Spec.ECC
open Spec.ECC.WNAF

open Hacl.Impl.EC.LowLevel
open Hacl.Spec.EC.Definition

open Hacl.Spec.MontgomeryMultiplication

open FStar.Mul

open Hacl.Impl.EC.Masking
open Hacl.Impl.EC.Masking.ScalarAccess
open Lib.IntTypes.Intrinsics

open FStar.Math.Lemmas
open Hacl.Impl.EC.ScalarMultiplication.WNAF.Lemmas


#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0" 

val scalar_rwnaf_step_compute_di: #c: curve -> w0: uint64 
  -> out: lbuffer uint64 (size ((getPower c / Spec.ECC.WNAF.w + 1) * 2))
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1} 
  -> r: lbuffer uint64 (size 1) -> i: size_t {v i < getPower c / Spec.ECC.WNAF.w} -> 
  Stack unit
  (requires fun h -> live h out /\ live h r /\ disjoint r out /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc r) h0 h1 /\ (
    let sign = Lib.Sequence.index (as_seq h1 out) (2 * v i + 1) in 
    let abs =  Lib.Sequence.index (as_seq h1 out) (2 * v i) in 
    (if v sign = 0 then v w0 - v dradix == v abs else - (v w0 - v dradix) == v abs) /\ 
    (if (v w0 - v dradix) >= 0 then v sign == 0 else v sign = pow2 64 - 1)) /\ (
    forall (j: nat {j < 2 * v i}).
      Lib.Sequence.index (as_seq h0 out) j == Lib.Sequence.index (as_seq h1 out) j) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
    v signLast == 0))

let scalar_rwnaf_step_compute_di w out mask r i =
  let h0 = ST.get() in 
  let c = Lib.IntTypes.Intrinsics.sub_borrow_u64 (u64 0) w dradix r in 
  let r0 = index r (size 0) in 
    let h1 = ST.get() in 

  let r2 = u64 0 -. r0 in 
    
  let cAsFlag = eq1_u64 c in 
  let r3 = cmovznz2 r2 r0 cAsFlag in 

  upd out (size 2 *! i) r3;
  upd out (size 2 *! i +! size 1) cAsFlag


#set-options "--z3rlimit 300"

val scalar_rwnaf_step_compute_window_: #c: curve 
  -> wStart: uint64 {v wStart < pow2 (64 - 5)}
  -> scalar: scalar_t #MUT #c 
  -> k: size_t {v k < getPower c / Spec.ECC.WNAF.w - 1} -> 
  Stack uint64 
  (requires fun h -> live h scalar)
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ v w0 - v wStart = 
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 1)) * pow2 1 + 
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 2)) * pow2 2 +
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 3)) * pow2 3 +
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 4)) * pow2 4 +
    v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 5)) * pow2 5)

let scalar_rwnaf_step_compute_window_ #c wStart scalar k = 
  let h0 = ST.get() in 
    assert_norm (pow2 (64 - 5) + pow2 1 + pow2 2 + pow2 3 + pow2 4 + pow2 5 < pow2 64);

  let i = (size 1 +! k) *! radix_u32 in 
  let w0 = wStart +! (shift_left (getScalarBit_leftEndian #c scalar (i +! size 1)) (size 1)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 2))) (size 2)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 3))) (size 3)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 4))) (size 4)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 5))) (size 5)) in 

    assert(v w0 - v wStart = 
      v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 1)) * pow2 1 + 
      v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 2)) * pow2 2 +
      v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 3)) * pow2 3 +
      v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 4)) * pow2 4 +
      v (ith_bit (as_seq h0 scalar) ((v k + 1) * w + 5)) * pow2 5);
  
  w0


inline_for_extraction noextract
val scalar_rwnaf_step_compute_window: #c: curve 
  -> wStart: uint64 {v wStart < pow2 (64 - 5)}
  -> scalar: scalar_t #MUT #c 
  -> k: size_t {v k < getPower c / Spec.ECC.WNAF.w - 1} -> 
  Stack uint64 
  (requires fun h -> live h scalar /\ scalar_as_nat #c (as_seq h scalar) < pow2 (v (getScalarLen c)))
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ (
    let t = (v k + 1) * w in
    let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in
    d / pow2 (t + 1) % m * 2 == v w0 - v wStart))

let scalar_rwnaf_step_compute_window #c wStart scalar k = 
  let h0 = ST.get() in 
  scalar_compute_window_lemma (as_seq h0 scalar) k;
  scalar_rwnaf_step_compute_window_ #c wStart scalar k  


inline_for_extraction noextract
val scalar_rwnaf_step: #c: curve -> out: lbuffer uint64 (size ((getPower c / Spec.ECC.WNAF.w + 1) * 2))
  -> scalar: scalar_t #MUT #c
  -> window: lbuffer uint64 (size 1) 
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1}
  -> r: lbuffer uint64 (size 1) 
  -> i: size_t {v i < getPower c / Spec.ECC.WNAF.w - 1} -> 
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ live h window /\ live h r /\ 
    scalar_as_nat (as_seq h scalar) < pow2 (getPower c) /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc out; loc scalar; loc window; loc r] /\ (
    let w0 = v (Lib.Sequence.index (as_seq h window) 0) in 
    let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h scalar)) in
    w0 == d / pow2 (v i * w + 1) % pow2 w * 2 + 1 /\
    w0 < 2 * m) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc window |+| loc r) h0 h1 /\ (
    let k = v i + 1 in 
    let w0 = v (Lib.Sequence.index (as_seq h0 window) 0) in
    let wUpd = v (Lib.Sequence.index (as_seq h1 window) 0) in
    let sign = Lib.Sequence.index (as_seq h1 out) (2 * v i + 1) in 
    let abs =  Lib.Sequence.index (as_seq h1 out) (2 * v i) in 
    let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in
    (if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs) /\
    (if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\
    wUpd < 2 * m /\ 
    wUpd == d % pow2 (k * w + w + 1) / pow2 (k * w) / 2 * 2 + 1 /\
    wUpd == d / pow2 (k * w + 1) % pow2 w * 2 + 1 /\ (
    forall (j: nat {j < 2 * v i}). 
      Lib.Sequence.index (as_seq h0 out) j == Lib.Sequence.index (as_seq h1 out) j)) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
    v signLast == 0))


let scalar_rwnaf_step #c out scalar window mask r i = 
    let h0 = ST.get() in 
  let wVar = to_u64 (index window (size 0)) in 
    assert(v wVar = v (Lib.Sequence.index (as_seq h0 window) 0));
  let wMask = logand wVar mask in 
    logand_mask wVar mask (v radix + 1); 
    FStar.Math.Lemmas.pow2_double_sum (v radix); 
  scalar_rwnaf_step_compute_di wMask out mask r i; 
    let h1 = ST.get() in 
  let d = wMask -. dradix in 
  let wStart = shift_right (wVar -. d) radix_shiftval in 
  
  FStar.Math.Lemmas.lemma_div_lt_nat (v (wVar -. d)) 64 (v radix_shiftval);

  let w0 = scalar_rwnaf_step_compute_window wStart scalar i in 
  upd window (size 0) w0;

    let h2 = ST.get() in   
    let d_i = v wVar % (2 * m) - m in 

      let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in
	assert (v wStart = (v wVar - (d_i % pow2 64)) % pow2 64 / m);
      lemma_mod_sub_distr (v wVar)  (d_i) (pow2 64); 
	assert (v wStart = (v wVar - d_i) % pow2 64 / m);
	assert (v wStart =  (v wVar - v wVar % (2 * m) + m) % pow2 64  / m);
      small_mod ((v wVar / (2 * m) * (2 * m)) + m) (pow2 64);
	assert (v wStart =  v wVar / (2 * m) * 2 + 1);
      pow2_multiplication_modulo_lemma_2 (d / pow2 ((v i + 1) * w  + 1)) (w + 1) 1;
	assert(d / pow2 ((v i + 1) * w  + 1) % m * 2 + (v wVar / (2 * m) * 2 + 1) == v w0);
	assert(d / pow2 ((v i + 1) * w  + 1) * 2 % pow2 (w + 1)  + (v wVar / (2 * m) * 2 + 1) == v w0);
      
	assert(v wVar < 2 * m);
      small_division_lemma_1 (v wVar) (2 * m);
	assert(v wVar / (2 * m) == 0);

	assert(2 * (d / pow2 ((v i + 1) * w  + 1)) % (2 * m) + 1 == v w0);
      pow2_plus (v i * w) (w + 1); 
      division_multiplication_lemma (d) (pow2 (w + 1)) (pow2 (v i * w));

      division_multiplication_lemma (d / (pow2 w)) 2 (pow2 (v i * w));
      pow2_double_mult (v i * w);
	assert((d / (pow2 w) / (2 * pow2 (v i * w))) % (pow2 w) * 2 + 1 == v w0);
    
	assert ((d / (pow2 w) / (pow2 (v i * w + 1))) % (pow2 w) * 2 + 1 == v w0);
      pow2_modulo_division_lemma_1 (d  / pow2 w) (v i * w + 1) (v i * w + 1 + w);
      pow2_double_mult (v i * w); 
    
      division_multiplication_lemma (d / (pow2 w) % pow2 (v i * w + 1 + w)) (pow2 (v i * w)) (pow2 1);

	assert(d / (pow2 w)  % pow2 (v i * w + 1 + w) / pow2 (v i * w) / pow2 1  * 2 + 1 == v w0);

      let k = v i + 1 in 
   
	assert(2 * (d / pow2 (k * w  + 1)) % (pow2 (w + 1)) + 1 == v w0);
	assert(d / pow2 (k * w  + 1) % pow2 w * 2 + 1 == v w0);

      pow2_modulo_division_lemma_1 d (k * w + 1) (k * w + 1 + w);
      pow2_double_mult (k * w);
      division_multiplication_lemma (d % pow2 (k * w + w + 1)) (pow2 (k * w)) 2;
      
	assert(d % pow2 (k * w + w + 1) / pow2 (k * w) / 2 * 2 + 1 == v w0);
	assert(v w0 < 2 * m)


val scalar_rwnaf_loop: #c: curve -> out: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1))) 
  -> scalar: scalar_t #MUT #c 
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1}
  -> window: lbuffer uint64 (size 1) -> 
  Stack unit
  (requires fun h -> live h out /\ live h scalar /\ live h window /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc out; loc scalar; loc window] /\ (
    let w0 = v (Lib.Sequence.index (as_seq h window) 0) in 
    w0 == scalar_as_nat #c (as_seq h scalar) / 2 % pow2 w * 2 + 1 /\
    scalar_as_nat (as_seq h scalar) < pow2 (getPower c) /\
    w0 < 2 * m) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out |+| loc window) h0 h1 /\ (
    let w0 = v (Lib.Sequence.index (as_seq h1 window) 0) in 
    let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in 
    w0 == d / pow2 ((v (getScalarLen c) / w - 1) * w + 1) % pow2 w * 2 + 1 /\
    w0 < 2 * m) /\ (
    forall (j: nat {j < v (getScalarLen c) / w - 1}). 
      let wUpd = v (Lib.Sequence.index (as_seq h1 window) 0) in
      let sign = Lib.Sequence.index (as_seq h1 out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h1 out) (2 * j) in 
      let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in
      let w0 = d / pow2 (j * w + 1) % pow2 w * 2 + 1 in
      (if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs) /\ (
      let lastIndex = v (getScalarLen c) / w in 
      let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
      v signLast == 0)))

let scalar_rwnaf_loop #c out scalar mask window = 
  push_frame(); 
  let r = create (size 1) (u64 0) in 
    let h0 = ST.get() in 
  
  let inv h (i:nat {i <= v (getScalarLen c) / w}) = 
    live h out /\ live h scalar /\ live h window /\ live h r /\
    modifies (loc out |+| loc window |+| loc r) h0 h /\ (
    let w0 = v (Lib.Sequence.index (as_seq h window) 0) in 
    let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in 
    w0 == d / pow2 (i * w + 1) % pow2 w * 2 + 1 /\
    w0 < 2 * m /\ (
    forall (j: nat {j < i}). 
      let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in
      let w0 = d / pow2 (j * w + 1) % pow2 w * 2 + 1 in
      let wUpd = v (Lib.Sequence.index (as_seq h window) 0) in
      let sign = Lib.Sequence.index (as_seq h out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h out) (2 * j) in 
      (if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then (w0 % (2 * m) - m) == v abs else - (w0 % (2 * m) - m) == v abs)) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0)) in 

  Lib.Loops.for 0ul (getLenWnaf #c -. 1ul) inv (scalar_rwnaf_step #c out scalar window mask r);
  pop_frame()


inline_for_extraction noextract
val scalar_rwnaf_compute_start_window: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> mask: uint64 {v mask = pow2 (v radix + 1) - 1} -> 
  Stack uint64
  (requires fun h -> live h scalar /\ scalar_as_nat #c (as_seq h scalar) < pow2 (getPower c))
  (ensures fun h0 window h1 -> modifies0 h0 h1 /\ (
    let d = scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)) in 
    v window == d / 2 % pow2 w * 2 + 1))

let scalar_rwnaf_compute_start_window #c scalar mask = 
  let h0 = ST.get() in 
  
  let in0 = to_u64 (index scalar (getScalarLenBytes c -! size 1)) in 
  let windowStartValue = logor (u64 1) (logand in0 mask) in 

  assert_norm (pow2 6 == 64);
    logand_mask in0 mask 6;
    scalar_rwnaf_lemma0 #c (as_seq h0 scalar); 
    logor_mask (logand in0 mask); 
    pow2_modulo_modulo_lemma_1 (scalar_as_nat #c (as_seq h0 scalar)) 6 8;

    multiply_fractions (scalar_as_nat #c (as_seq h0 scalar) % pow2 6) 2;
    pow2_double_mult w;

  assert (v windowStartValue == scalar_as_nat #c (as_seq h0 scalar) % pow2 (w + 1) / pow2 1 * 2 + 1);
    pow2_modulo_division_lemma_1 (scalar_as_nat #c (as_seq h0 scalar)) 1 (w + 1); 
  assert (v windowStartValue == scalar_as_nat #c (as_seq h0 scalar) / 2 % pow2 w * 2 + 1);
  
  windowStartValue


inline_for_extraction noextract
val scalar_rwnaf_tail_3: #c: curve -> scalar: scalar_t #MUT #c -> wStart: uint64 {v wStart < pow2 (64 - 5)} ->
  Stack uint64 
  (requires fun h -> live h scalar /\ 
    scalar_as_nat #c (as_seq h scalar) < pow2 (getPower c) /\ 
    4 == v (getScalarLen c) - v (getScalarLen c) / w * w)
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ (
    let d = scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)) in 
    2 * (d / pow2 (v (getScalarLen c) / w * w + 1)) = v w0 - v wStart))

let scalar_rwnaf_tail_3 #c scalar wStart = 
  let h0 = ST.get() in 

  let i = getLenWnaf #c *! radix_u32 in 
  scalar_as_nat_def #c (as_seq h0 scalar) (v (getScalarLen c) - (v i + 1));
  scalar_as_nat_def #c (as_seq h0 scalar) (v (getScalarLen c) - (v i + 2));
  scalar_as_nat_def #c (as_seq h0 scalar) (v (getScalarLen c) - (v i + 3));

  Hacl.Impl.EC.Masking.ScalarAccess.Lemmas.test #c (as_seq h0 scalar) (v (getScalarLen c) - v (getScalarLen c) / w * w - 1);
  scalar_as_nat_zero (as_seq h0 scalar);

  assert_norm (pow2 (64 - 5) + pow2 1 + pow2 2 + pow2 3  < pow2 64);
  let w0 = wStart +! (shift_left (getScalarBit_leftEndian #c scalar (i +! size 1)) (size 1)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 2))) (size 2)) in 
  let w0 = w0 +! (shift_left (getScalarBit_leftEndian #c scalar (i +! (size 3))) (size 3)) in 

  scalar_as_nat_is_same_as_scalar_to_odd #c (as_seq h0 scalar) (v (getScalarLen c) / w * w + 1); 
  
  w0
  

val scalar_rwnaf_tail__: #c: curve -> scalar: scalar_t #MUT #c -> wStart: uint64 {v wStart < pow2 (64 - 5)} ->
  Stack uint64 
  (requires fun h -> live h scalar /\ scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)))
  (ensures fun h0 w0 h1 -> modifies0 h0 h1 /\ (
    let d = scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)) in 
    2 * (d / pow2 (v (getScalarLen c) / w * w + 1)) = v w0 - v wStart))

let scalar_rwnaf_tail__ #c scalar wStart = 
  let h0 = ST.get() in 
  match c with 
  |P256 -> 
    assert(scalar_as_nat (as_seq h0 scalar) < pow2 (v (getScalarLen c)));
    small_div (scalar_as_nat (as_seq h0 scalar)) (pow2 (v (getScalarLen c)));

    assert (
      let d = scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)) in 
      2 * (d / pow2 (v (getScalarLen c) / w * w + 1)) = 0);
      
    wStart
  |P384 -> scalar_rwnaf_tail_3 #P384 scalar wStart


val scalar_rwnaf_tail_: #c: curve
  -> scalar: scalar_t #MUT #c 
  -> mask: uint64 
  -> wVar: uint64 {v wVar < 2 * m /\ v mask == v wVar % pow2 (w + 1)} ->
  Stack uint64 
  (requires fun h -> live h scalar /\ scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)))
  (ensures fun h0 wLast h1 -> modifies0 h0 h1 /\ (
    let d = scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)) in 
    2 * (d / pow2 (v (getScalarLen c) / w * w + 1)) + 
     (v wVar / pow2 (w + 1) * pow2 (w + 1) + m) % pow2 64  / m = v wLast))

let scalar_rwnaf_tail_ #c scalar mask wVar = 
  let h0 = ST.get() in 
  let d = mask -. dradix in 
  let wStart = shift_right (wVar -. d) radix_shiftval in 
  
    shift_right_lemma (wVar -. d) radix_shiftval;
      assert(v d == (v mask - m) % pow2 64);
    lemma_mod_sub_distr (v wVar) (v mask - m) (pow2 64);
      assert(v wStart == (v wVar - v mask + m) % pow2 64  / pow2 w);
    lemma_div_lt_nat ((v wVar - v mask + m) % pow2 64) (64) w;
  
  scalar_rwnaf_tail__ scalar wStart


val scalar_rwnaf_tail: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> mask: uint64 
  -> wVar: uint64 {v wVar < 2 * m /\ v mask == v wVar % pow2 (w + 1)} ->
  Stack uint64 
  (requires fun h -> live h scalar /\ scalar_as_nat (as_seq h scalar) < pow2 (getPower c) /\ (
    let d = scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h scalar)) in 
    v wVar = d / pow2 ((v (getScalarLen c) / w - 1) * w + 1) % pow2 w * 2 + 1))
  (ensures fun h0 wLast h1 -> modifies0 h0 h1 /\ (
    let d = scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)) in 
    let len = v (getScalarLen c) in 
    v wLast == 2 * (d / pow2 (len / w * w + 1)) + 1))

let scalar_rwnaf_tail #c scalar mask wVar = 
  let h0 = ST.get() in 
  let wLast = scalar_rwnaf_tail_ #c scalar mask wVar in 
    scalar_as_nat_upperbound (as_seq h0 scalar) (v (getScalarLen c));
    
    scalar_rwnaf_lemma_tail #c (scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)));
    scalar_rwnaf_lemma0_tail #c (scalarToOdd (getPower c) (scalar_as_nat #c (as_seq h0 scalar)));
  wLast


inline_for_extraction noextract
val scalar_rwnaf_: #c: curve -> out: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> scalar: scalar_t #MUT #c ->
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ disjoint out scalar /\
    scalar_as_nat (as_seq h scalar) < pow2 (getPower c) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    forall (j: nat {j < v (getScalarLen c) / w }). 
      let sign = Lib.Sequence.index (as_seq h1 out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h1 out) (2 * j) in 
      let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in 
      let w0 = d / pow2 (j * w + 1) % pow2 w * 2 + 1 in (
      if w0 % (2 * m) - m >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then 
	w0 % (2 * m) - m == v abs 
      else 
	- (w0 % (2 * m) - m) == v abs)) /\ (  
    let lastIndex = v (getScalarLen c) / w in 
    let absLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex) in 
    let signLast = Lib.Sequence.index (as_seq h1 out) (2 * lastIndex + 1) in 
    let d = scalarToOdd (v (getScalarLen c)) (scalar_as_nat #c (as_seq h0 scalar)) in 
    v signLast == 0 /\
    v absLast = d / pow2 (v (getScalarLen c) / w * w + 1) * 2 + 1))

let scalar_rwnaf_ #c out scalar = 
  push_frame();
  let mask = dradix_wnaf -! (u64 1) in 
  let in0 = to_u64 (index scalar (getScalarLenBytes c -! size 1)) in 
    assert_norm (pow2 6 == 64);
  let windowStartValue = scalar_rwnaf_compute_start_window scalar mask in 
  let window = create (size 1) windowStartValue in 
  let r = create (size 1) (u64 0) in 

  scalar_rwnaf_loop #c out scalar mask window; 

  let wVar = index window (size 0) in 
  let wMask = logand wVar mask in 
    logand_mask wVar mask 6;

  scalar_rwnaf_step_compute_di #c wMask out mask r (getLenWnaf #c -! 1ul);
  let wLast = scalar_rwnaf_tail scalar wMask wVar in 

  upd out (size 2 *! getLenWnaf #c) wLast; 

  pop_frame()


inline_for_extraction noextract
val scalar_rwnaf: #c: curve -> out: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1))) 
  -> scalar: scalar_t #MUT #c ->
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ disjoint out scalar /\ 
    scalar_as_nat (as_seq h scalar) < pow2 (getPower c) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    let n = v (getScalarLen c) in 
    let d = scalar_as_nat (as_seq h0 scalar) in
    let wnaf_repr = to_wnaf n (scalarToOdd n d) in 
    forall (j: nat {j <= v (getScalarLen c) / w }). 
      let sign = Lib.Sequence.index (as_seq h1 out) (2 * j + 1) in 
      let abs =  Lib.Sequence.index (as_seq h1 out) (2 * j) in 
      let wf = Lib.Sequence.index #_ #(n / w + 1) wnaf_repr j in 
      (if wf >= 0 then v sign = 0 else v sign = maxint U64) /\ (
      if v sign = 0 then wf == v abs else - wf == v abs)))

let scalar_rwnaf #c out scalar = 
    let h0 = ST.get() in
  scalar_rwnaf_ #c out scalar;
    scalar_as_nat_upperbound (as_seq h0 scalar) (v (getScalarLen c));
    let h1 = ST.get() in 

    let n = v (getScalarLen c) in 
    let d = scalar_as_nat (as_seq h0 scalar) in
    
    rwnaf_lemma0 (scalarToOdd n d);
    scalar_rwnaf_lemma_to_spec (v (getScalarLen c)) d out h1


let rwnaf_invariant (#c: curve) (rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))) (h: mem) = (
 forall (i: nat {i < getPower c / w + 1}). 
      let ri = Lib.Sequence.index (as_seq h rnaf) (2 * i) in 
      v ri >= 1 /\ v ri < pow2 w) /\ (
    forall (i: nat {i < getPower c / w + 1}). 
      let ri = Lib.Sequence.index (as_seq h rnaf) (2 * i + 1) in 
      v ri == 0 \/ v ri == maxint U64)


inline_for_extraction noextract 
val scalar_rwnaf0: #c: curve -> out: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1))) 
  -> scalar: scalar_t #MUT #c ->
  Stack unit 
  (requires fun h -> live h out /\ live h scalar /\ disjoint out scalar /\ 
    scalar_as_nat (as_seq h scalar) < pow2 (v (getScalarLen c)) /\ (
    let lastIndex = v (getScalarLen c) / w in 
    let signLast = Lib.Sequence.index (as_seq h out) (2 * lastIndex + 1) in 
    v signLast == 0))
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ rwnaf_invariant #c out h1 /\ (
    let n = getPower c in 
    let d = scalarToOdd n (scalar_as_nat #c (as_seq h0 scalar)) in 
    rnaf_to_spec #c (as_seq h1 out) == to_wnaf n d))
    
let scalar_rwnaf0 #c out scalar = 
  let h0 = ST.get() in 
    scalar_rwnaf #c out scalar;
  let h1 = ST.get() in 

  let n = getPower c in 
  let d = scalarToOdd n (scalar_as_nat #c (as_seq h0 scalar)) in
  let wnaf_repr = to_wnaf n d in 
  
  let r = rnaf_to_spec #c (as_seq h1 out) in 
  
  assert(
    forall (j: nat {j <= v (getScalarLen c) / w }). 
      Seq.index wnaf_repr j == Seq.index r j);

  assert(Lib.Sequence.equal #_  #(n / w + 1) wnaf_repr r);

  assert(wnaf_repr == r);


  scalar_rwnaf_to_invariant_lemma0 #c d;
  scalar_rwnaf_to_invariant_lemma1 #c d


assume val getPointPrecomputed_P256: index: size_t {v index < (getPower P256 / w + 1) * pow2 (w - 1)} 
  -> result: pointAffine P256 ->
  Stack unit
  (requires fun h -> live h result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ point_aff_eval P256 h1 result /\ (
    let j = v index / pow2 (w - 1) in 
    let i = 2 * (v index % pow2 (w - 1)) + 1 in 
    let p_i = point_mult #P256 (pow2 (j * w) * i) (basePoint #P256) in 
    let r = fromDomainPoint #P256 #DH (toJacobianCoordinates (point_affine_as_nat P256 h1 result)) in 
    pointEqual r p_i))


assume val getPointPrecomputed_P384: index: size_t {v index < (getPower P384 / w + 1) * pow2 (w - 1)} 
  -> result: pointAffine P384 ->
  Stack unit
  (requires fun h -> live h result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ point_aff_eval P384 h1 result /\ (
    let j = v index / pow2 (w - 1) in 
    let i = 2 * (v index % pow2 (w - 1)) + 1 in 
    let p_i = point_mult #P384 (pow2 (j * w) * i) (basePoint #P384) in 
    let r = fromDomainPoint #P384 #DH (toJacobianCoordinates (point_affine_as_nat P384 h1 result)) in 
    pointEqual r p_i))


val getPointPrecomputed: #c: curve 
  -> index: size_t {v index < (getPower c / w + 1) * pow2 (w - 1)}
  -> result: pointAffine c ->
  Stack unit
  (requires fun h -> live h result)
  (ensures fun h0 r h1 -> modifies (loc result) h0 h1 /\ point_aff_eval c h1 result /\ (
    let j = v index / pow2 (w - 1) in 
    let i = 2 * (v index % pow2 (w - 1)) + 1 in 
    let p_i = point_mult #c (pow2 (j * w) * i) (basePoint #c) in 
    let r = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)) in 
    pointEqual r p_i))

let getPointPrecomputed #c index result = 
  match c with 
  |P256 -> getPointPrecomputed_P256 index result
  |P384 -> getPointPrecomputed_P384 index result
  

val copy_point_conditional_affine: #c: curve 
  -> result: pointAffine c 
  -> p: pointAffine c 
  -> mask: uint64 {v mask = 0 \/ v mask = pow2 64 - 1} ->
  Stack unit
  (requires fun h -> 
    live h result /\ live h p /\ disjoint result p /\ point_aff_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let pX, pY = gsub p (size 0) len, gsub p len len in 
    let rX, rY = gsub result (size 0) len, gsub result len len in 
    (v mask = pow2 64 - 1 ==> point_aff_eval c h1 result) /\ (
    if v mask = 0 then
      as_nat c h1 rX == as_nat c h0 rX /\ as_nat c h1 rY == as_nat c h0 rY
    else 
      as_nat c h1 rX == as_nat c h0 pX /\ as_nat c h1 rY == as_nat c h0 pY)))

let copy_point_conditional_affine #c result p mask = 
  let len = getCoordinateLenU64 c in
  let pX, pY = sub p (size 0) len, sub p len len in 
  Hacl.Impl.EC.Precomputed.copy_point_conditional_affine #MUT #c result pX pY mask


val loopK_step: #c: curve -> d: uint64 -> result: pointAffine c 
  -> j: size_t {v j < (getPower c / w + 1)} 
  -> k: size_t {v k < pow2 (w - 1)}
  -> tempPoint: pointAffine c -> Stack unit
  (requires fun h -> live h result /\ live h tempPoint /\ disjoint result tempPoint)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempPoint) h0 h1 /\ (
    let len = getCoordinateLenU64 c in 
    let rX, rY = gsub result (size 0) len, gsub result len len in 
    (v d == v k ==> point_aff_eval c h1 result) /\ (
    if v d <> v k then
      as_nat c h1 rX == as_nat c h0 rX /\ as_nat c h1 rY == as_nat c h0 rY
    else 
      pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result))) (point_mult #c (pow2 (v j * w) * (2 * v k + 1)) (basePoint #c)))))


let loopK_step #c d result j k tempPoint = 
  let mask = eq_mask d (to_u64 k) in 
    eq_mask_lemma d (to_u64 k); 
    let h0 = ST.get() in 
  
  getPointPrecomputed #c (j *! size 16 +! k) tempPoint;
  let h1 = ST.get() in 
  
   assert (
    let index = (j *! size 16 +! k) in 
    let i =  2 * ((v j * 16 + v k) % pow2 (w - 1)) + 1 in 
    let j = v index / pow2 (w - 1) in 
    let p_i = point_mult #c (pow2 (j * w) * i) (basePoint #c) in 
    let r = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 tempPoint)) in 
    pointEqual r p_i);

  copy_point_conditional_affine result tempPoint mask;
    let h2 = ST.get() in 

  calc (==) {
    (v j * pow2 (w - 1) + v k) / pow2 (w - 1);
  (==) {}
    v j + v k / pow2 (w - 1);
  (==) {small_div (v k) (pow2 (w - 1))}
    v j;
  };

  calc (==) {
    (v j * pow2 (w - 1) + v k) % pow2 (w - 1);
  (==) {lemma_mod_plus (v k) (v j) (pow2 (w - 1))}
    v k;
  }


val loopK_loop: #c: curve 
  -> d: uint64 {v d < pow2 (w - 1)}
  -> result: pointAffine c
  -> j: size_t {v j < (getPower c / w + 1)} 
  -> tempPoint: pointAffine c -> Stack unit 
  (requires fun h -> live h result /\ live h tempPoint /\ disjoint result tempPoint)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempPoint) h0 h1 /\ 
    point_aff_eval c h1 result /\
    pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)))
      (point_mult #c (pow2 (v j * w) * (2 * v d + 1)) (basePoint #c)))

let loopK_loop #c d result j tempPoint = 
  let h0 = ST.get() in 
   let invK h (k: nat) = live h result /\ live h tempPoint /\ modifies (loc result |+| loc tempPoint) h0 h /\ (
    let len = getCoordinateLenU64 c in 
    let rX, rY = gsub result (size 0) len, gsub result len len in 
    if k > v d then 
      point_aff_eval c h result /\
      pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h result))) (point_mult #c (pow2 (v j * w) * (2 * v d + 1)) (basePoint #c))
    else 
      as_nat c h rX == as_nat c h0 rX /\ as_nat c h rY == as_nat c h0 rY) in 
  Lib.Loops.for 0ul 16ul invK (fun k -> loopK_step d result j k tempPoint) 


val loopK: #c: curve -> d: uint64 {v d < pow2 (w - 1)} -> result: pointAffine c
  -> j: size_t {v j < (getPower c / w + 1)} -> Stack unit 
  (requires fun h -> live h result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    point_aff_eval c h1 result /\
  pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)))
    (point_mult #c (pow2 (v j * w) * (2 * v d + 1)) (basePoint #c)))

let loopK #c d result j = 
    let h0 = ST.get() in 
    push_frame(); 
  let tempPoint : pointAffine c = create (getCoordinateLenU64 c *! 2ul) (u64 0) in 
  loopK_loop d result j tempPoint; 
    let h1 = ST.get() in 
    pop_frame()


val point_affine_neg: #c: curve -> p: pointAffine c -> result: pointAffine c -> Stack unit 
  (requires fun h -> live h p /\ live h result /\ disjoint p result /\ point_aff_eval c h p /\
    ~ (isPointAtInfinity (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h p)))))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ point_aff_eval c h1 result /\ (
    let pJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 p)) in
    let b = getDLP #c pJ in 
    let rJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result)) in 
    pointEqual rJ (Spec.ECC.point_mult #c (-b) (basePoint #c))))

let point_affine_neg #c p result = 
    let h0 = ST.get() in 
  
  let len = getCoordinateLenU64 c in

  let pX, pY = sub p (size 0) len, sub p len len in 
  let rX, rY = sub result (size 0) len, sub result len len in 

  copy rX pX;
  felem_sub_zero #c pY rY;
    let h1 = ST.get() in 
    
    let prime = getPrime c in 

    let pJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 p)) in
    let b = getDLP #c pJ in 

  point_neg_lemma_infinity_indexes #c pJ;

  (* both are not 0 : the point belongs to curve; (0, 0) does not *)
  assume (~ (as_nat c h0 pX == 0 /\ as_nat c h0 pY == 0));
  assert (~ (as_nat c h0 pX == 0 /\ 0 - as_nat c h0 pY == 0));
  lemma_mod_sub_0 #c (as_nat c h0 pY);
  lemma_fromDomain0 #c;

  point_neg_infinity_when_y_minus #c (fromDomain #c (as_nat c h0 pX)) (fromDomain #c (as_nat c h0 pY)) (fromDomain #c 1);
  lemma_inverse_uniqueness pJ (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 result))) (point_mult #c (-b) (basePoint #c))


val point_neg_conditional: #c: curve -> p: pointAffine c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> mask: uint64 {v mask == 0 \/ v mask == pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_aff_eval c h p /\
    ~ (isPointAtInfinity (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h p)))))
  (ensures fun h0 _ h1 ->  modifies (loc p |+| loc tempBuffer) h0 h1 /\ 
    point_aff_eval c h1 p /\ (
    if v mask = 0 then 
      fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 p)) == 
      fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 p))
    else
      let pJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 p)) in
      let b = getDLP #c pJ in 
      let rJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 p)) in 
      pointEqual rJ (Spec.ECC.point_mult #c (- b) (basePoint #c))))


let point_neg_conditional #c p tempBuffer mask = 
    let h0 = ST.get() in 
  let len = getCoordinateLenU64 c in 
 
  let temp = sub tempBuffer (size 0) len in 
  
  let pX = sub p (size 0) len in 
  let pY = sub p len len in 
  
  felem_sub_zero #c pY temp; 
  copy_conditional #c pY temp mask;

   let pJ = fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 p)) in
   let qJ = fromDomainPoint #c #DH (as_nat c h0 pX, (0 - as_nat c h0 pY) % getPrime c, 1) in 

   let b = getDLP #c pJ in  
   (* both are not 0 : the point belongs to curve; (0, 0) does not *)
   assume (~ (as_nat c h0 pX == 0 /\ as_nat c h0 pY == 0));
   assert (~ (as_nat c h0 pX == 0 /\ 0 - as_nat c h0 pY == 0));
   lemma_mod_sub_0 #c (as_nat c h0 pY);
   lemma_fromDomain0 #c;

   point_neg_infinity_when_y_minus #c (fromDomain #c (as_nat c h0 pX)) (fromDomain #c (as_nat c h0 pY)) (fromDomain #c 1);
   point_neg_lemma_infinity_indexes #c pJ;   
   lemma_inverse_uniqueness pJ qJ (point_mult #c (-b) (basePoint #c))


val conditional_subtraction_compute_mask: #c: curve -> scalar: scalar_t #MUT #c ->
  Stack uint64 
  (requires fun h -> live h scalar)
  (ensures fun h0 mask h1 -> modifies0 h0 h1 /\ (
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 0 then v mask == maxint U64 else v mask == 0))

let conditional_subtraction_compute_mask #c scalar = 
  let len = getScalarLenBytes c -! 1ul in 
  let i0 = index scalar len in 

  logand_mask i0 (u8 1) 1; 
  lognot_lemma (u64 0 -. to_u64 (logand i0 (u8 1)));
  lognot(u64 0 -. to_u64 (logand i0 (u8 1)))


val uploadBasePointAffine: #c: curve -> p: pointAffine c 
  -> Stack unit 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_aff_eval c h1 p /\
    pointEqual #c (basePoint #c) (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 p))))
   
let uploadBasePointAffine #c p = 
  admit();
  match c with 
  |P256 -> 
    upd p (size 0) (u64 0x1fb38ab1388ad777);
    upd p (size 1) (u64 0x1dfee06615fa309d);
    upd p (size 2) (u64 0xfcac986c3afea4a7);
    upd p (size 3) (u64 0xdf65c2da29fb821a);
    
    upd p (size 4) (u64 0xeff44e23f63f8f6d);
    upd p (size 5) (u64 0xaa02cd3ed4b681a4);
    upd p (size 6) (u64 0xdd5fda3363818af8);
    upd p (size 7) (u64 0xfc53bc2629fbf0b3)
  |P384 -> 
    upd p (size 0) (u64 0x32f2345cb5536b82);
    upd p (size 1) (u64 0x33ba95da2f7d6018);
    upd p (size 2) (u64 0xf2cd7729b1c03094);
    upd p (size 3) (u64 0x3159972fc3a90663);
    upd p (size 4) (u64 0x5827e6777fec9ce6);
    upd p (size 5) (u64 0x1af1e42821b04e1b);
    
    upd p (size 6) (u64 0xbbacc6d281184b31);
    upd p (size 7) (u64 0x5a08d98b36984428);
    upd p (size 8) (u64 0x73ba86bb86816030);
    upd p (size 9) (u64 0xe77b3c32da8c0cac);
    upd p (size 10) (u64 0x594336a7bc787585);
    upd p (size 11) (u64 0x7d25d16cde0af6c9)


val uploadMinusBasePointAffine: #c: curve 
  -> basePointNegative: pointAffine c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> Stack unit 
  (requires fun h -> live h basePointNegative /\ live h tempBuffer /\ disjoint basePointNegative tempBuffer)
  (ensures fun h0 _ h1 -> modifies (loc basePointNegative |+| loc tempBuffer) h0 h1 /\
    point_aff_eval c h1 basePointNegative /\
    pointEqual #c (Spec.ECC.point_mult #c (- 1) (basePoint #c)) (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 basePointNegative))))

let uploadMinusBasePointAffine #c p tempBuffer = 
  let tempBasePoint = sub tempBuffer (size 0) (getCoordinateLenU64 c *! 2ul) in 
  uploadBasePointAffine #c tempBasePoint;
    let h1 = ST.get() in 
    point_mult_1 #c (basePoint #c);
  point_affine_neg #c tempBasePoint p;
    getDLP_point_mult #c 1 (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 tempBasePoint)))

val conditional_subtraction_upload_masked: #c: curve -> scalar: scalar_t #MUT #c
  -> tempPointJacobian: point c 
  -> result: point c ->
  Stack unit 
  (requires fun h -> live h scalar /\ live h tempPointJacobian /\ live h result /\ 
    disjoint result tempPointJacobian /\ point_eval c h result /\ point_eval c h tempPointJacobian)
  (ensures fun h0 _ h1 -> modifies (loc tempPointJacobian |+| loc result) h0 h1 /\ point_eval c h1 result /\ (
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 1 then 
      point_as_nat c h1 result == point_as_nat c h0 result
    else
      point_as_nat c h1 result == point_as_nat c h0 tempPointJacobian))
      
let conditional_subtraction_upload_masked #c scalar tempPointJacobian result = 
    let h0 = ST.get() in 
  let mask = conditional_subtraction_compute_mask #c scalar in 
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 result;
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 tempPointJacobian;
  copy_point_conditional result tempPointJacobian mask


val conditional_substraction_: #c: curve -> result: point c -> p: point c -> scalar: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c)
  -> p0: pointAffine c 
  -> p1: point c ->
  Stack unit 
  (requires fun h -> 
    live h result /\ live h p /\ live h scalar /\ live h tempBuffer /\ live h p0 /\ live h p1 /\
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc p1; loc scalar; loc tempBuffer; loc p0] /\
    eq_or_disjoint p p1 /\ disjoint p p0 /\ disjoint p tempBuffer /\
    point_eval c h p /\ point_eval c h result /\ (
    if (v (Lib.Sequence.index (as_seq h scalar) (v (getScalarLenBytes c) - 1)) % 2 = 0) then 
      ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (Spec.ECC.point_mult #c (- 1) (basePoint #c))) 
    else True))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer |+| loc p0 |+| loc p1) h0 h1 /\ point_eval c h1 result /\ (
    let p0 = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 1 then
      point_as_nat c h1 result == point_as_nat c h0 result
    else
      pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) (pointAdd #c p0 (Spec.ECC.point_mult #c (- 1) (basePoint #c)))))

let conditional_substraction_ #c result p scalar tempBuffer precompNegativePoint tempPointJacobian = 
    let h0 = ST.get() in 
  uploadMinusBasePointAffine precompNegativePoint tempBuffer;
      let h1 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 p;
  Hacl.Impl.EC.PointAddMixed.point_add_mixed p precompNegativePoint tempPointJacobian tempBuffer;
      let h2 = ST.get() in 
      Hacl.Impl.EC.ScalarMult.Radix.curve_compatibility_with_translation_lemma_1 (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h2 precompNegativePoint))) (Spec.ECC.point_mult #c (- 1) (basePoint #c)) (fromDomainPoint #c #DH (point_as_nat c h0 p));
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 result;
    conditional_subtraction_upload_masked #c scalar tempPointJacobian result


val conditional_substraction: #c: curve -> result: point c -> p: point c -> scalar: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h result /\ live h p /\ live h scalar /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc result; loc scalar; loc tempBuffer] /\ 
    disjoint p tempBuffer /\
    point_eval c h p /\ point_eval c h result /\ (
    if (v (Lib.Sequence.index (as_seq h scalar) (v (getScalarLenBytes c) - 1)) % 2 = 0) then 
      ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (Spec.ECC.point_mult #c (- 1) (basePoint #c))) 
    else True))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let p0 = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let i0 = v (Lib.Sequence.index (as_seq h0 scalar) (v (getScalarLenBytes c) - 1)) in 
    if i0 % 2 = 1 then
      point_as_nat c h1 result == point_as_nat c h0 result
    else
      pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) (pointAdd #c p0 (Spec.ECC.point_mult #c (- 1) (basePoint #c)))))

let conditional_substraction #c result p scalar tempBuffer = 
  push_frame();
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    let tempPointJacobian = create (getPointLenU64 c) (u64 0) in 
    let precompNegativePoint = create (size 2 *! len) (u64 0) in 
    conditional_substraction_ #c result p scalar tempBuffer precompNegativePoint tempPointJacobian;
  pop_frame()


val getPointDoubleNTimes: #c: curve 
  -> p: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> k: size_t ->
  Stack unit
  (requires fun h -> live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1 /\ point_eval c h1 p /\
    fromDomainPoint #c #DH (point_as_nat c h1 p) == Spec.ECC.Radix.getPointDoubleNTimes #c
      (fromDomainPoint #c #DH (point_as_nat c h0 p)) (v k))

open Lib.LoopCombinators
open Lib.Loops

let getPointDoubleNTimes #c p tempBuffer k = 
  let h0 = ST.get() in 
  let inv h (k: nat) = live h p /\ live h tempBuffer /\ disjoint p tempBuffer /\ point_eval c h p /\ 
    modifies (loc p |+| loc tempBuffer) h0 h /\
    fromDomainPoint #c #DH (point_as_nat c h p) ==
      Lib.LoopCombinators.repeat k (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) in 
  Lib.LoopCombinators.eq_repeat0 (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p));  
  for 0ul k inv (fun i -> 
    Hacl.Impl.EC.PointDouble.point_double p p tempBuffer; 
    unfold_repeat (v k) (_point_double #c) (fromDomainPoint #c #DH (point_as_nat c h0 p)) (v i))


val compute_index_rwnaf: #c: curve 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> k: size_t {v k < v (getLenWnaf #c) + 1} -> 
  Stack uint64
  (requires fun h -> live h rnaf /\ rwnaf_invariant #c rnaf h)
  (ensures fun h0 d h1 -> modifies0 h0 h1 /\ 
    v d < pow2 (w - 1) /\ v d = (v (Seq.index (as_seq h0 rnaf) (2 * v k)) - 1) / 2)
 
let compute_index_rwnaf #c rnaf k = 
    let h0 = ST.get() in 
  let d0 = index rnaf (size 2 *! k) in
    Lib.IntTypes.shift_right_lemma (d0 -! u64 1) (size 1);
    lemma_div_lt_nat (v d0) w 1;
  shift_right (d0 -! u64 1) (size 1)


inline_for_extraction noextract
val scalar_multiplication_cmb_step_2: #c: curve 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> j: size_t {v j < v (getLenWnaf #c) + 1}
  -> pointPrecomputed: pointAffine c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h pointPrecomputed /\ live h tempBuffer /\ point_eval c h result /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc pointPrecomputed; loc tempBuffer] /\ (
      let d0 = v (Lib.Sequence.index (as_seq h rnaf) (2 * v j)) in 
      let d1 = v (Lib.Sequence.index (as_seq h rnaf) (2 * v j + 1)) in 
      let b = pow2 (v j * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c in 
      if d1 = 0 then 
	~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h result)) (point_mult #c b (basePoint #c))) else
	~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h result)) (point_mult #c (- b) (basePoint #c)))) /\ 
      rwnaf_invariant #c rnaf h )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc pointPrecomputed |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h0 result) in 
    let d0 = v (Lib.Sequence.index (as_seq h0 rnaf) (2 * v j)) in 
    let is_neg = v (Lib.Sequence.index (as_seq h0 rnaf) (2 * v j + 1)) in 
    let b = 
      if is_neg = 0 then 
	(pow2 (v j * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c) 
    else 
      - (pow2 (v j * w) * ((d0 - 1) / 2 * 2 + 1) % getOrder #c) in 
    let r = pointAdd #c pD (point_mult #c b (basePoint #c)) in 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 result)) r))
  
let scalar_multiplication_cmb_step_2 #c rnaf result k pointPrecomputed tempBuffer = 
  let h0 = ST.get() in 
  let is_neg = index rnaf (size 2 *! k +! size 1) in 
  let d = compute_index_rwnaf rnaf k in 

  loopK #c d pointPrecomputed k;
    let h1 = ST.get() in
    assert_norm (pow2 (w - 1) < getOrder #c);
    scalar_mult_cmb_composite_not_infinity #c (v k * w) (2 * v d + 1);

  point_neg_conditional #c pointPrecomputed tempBuffer is_neg;

    let h2 = ST.get() in
    dlp_mod_order #c (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 pointPrecomputed))) (pow2 (v k * w) * (2 * v d + 1));
    lemma_scalar_reduce #c (basePoint #c) (pow2 (v k * w) * v d);
  
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 result;
    
  Hacl.Impl.EC.PointAddMixed.point_add_mixed result pointPrecomputed result tempBuffer;
  
    let pD = fromDomainPoint #c #DH (point_as_nat c h0 result) in 
    let b = 
      if v is_neg = 0 then 
	(pow2 (v k * w) * (2 * v d + 1) % getOrder #c) 
      else 
	- (pow2 (v k * w) * (2 * v d + 1) % getOrder #c) in 
  
  Hacl.Impl.EC.ScalarMult.Radix.curve_compatibility_with_translation_lemma_1
    (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h2 pointPrecomputed)))
    (point_mult #c b (basePoint #c)) pD


val point_add_complete_last_step_lemma0: #c: curve -> h: mem
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> Lemma 
  (requires (rwnaf_invariant #c rnaf h))
  (ensures (v (Lib.Sequence.index (as_seq h rnaf) 0) >= 1 /\ v (Lib.Sequence.index (as_seq h rnaf) 0) < pow2 w) /\ (
    v (Lib.Sequence.index (as_seq h rnaf) 1) == 0 \/ v (Lib.Sequence.index (as_seq h rnaf) 1) == pow2 64 - 1))

let point_add_complete_last_step_lemma0 #c h rnaf = 
  assert(
    forall (i: nat). i < v (getScalarLen c) / w + 1 ==> (
      let ri = Lib.Sequence.index (as_seq h rnaf) (2 * i) in 
      v ri >= 1 /\ v ri < pow2 w));

  assert(
    forall (i: nat). i < v (getScalarLen c) / w + 1 ==> (
      let ri = Lib.Sequence.index (as_seq h rnaf) (2 * i + 1) in 
      v ri == 0 \/ v ri == pow2 64 - 1))

inline_for_extraction noextract
val point_add_complete_last_step_to_jacobian: #c: curve -> d: uint64 {v d < pow2 (w - 1)} -> p: point c -> Stack unit 
  (requires fun h -> live h p /\ (
    let pAffine = gsub p (size 0) (2ul *! getCoordinateLenU64 c) in 
    point_aff_eval c h pAffine))
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_eval c h1 p /\ (
    let pAffine = gsub p (size 0) (2ul *! getCoordinateLenU64 c) in 
    (pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 pAffine)))
	(point_mult #c (2 * v d + 1) (basePoint #c)) ==> (
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 p)) (point_mult #c (2 * v d + 1) (basePoint #c)) /\ 
      ~ (isPointAtInfinity (fromDomainPoint #c #DH (point_as_nat c h1 p))))) /\
      
     (pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h0 pAffine)))
	(point_mult #c (- (2 * v d + 1)) (basePoint #c)) ==> (
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 p)) (point_mult #c ( - (2 * v d + 1)) (basePoint #c)) /\ 
      ~ (isPointAtInfinity (fromDomainPoint #c #DH (point_as_nat c h1 p)))))))


let point_add_complete_last_step_to_jacobian #c d p = 
    let h0 = ST.get() in 
  let pX = sub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c) in 
  uploadOneImpl pX;
    let h1 = ST.get() in 

    let pAffine = gsub p (size 0) (2ul *! getCoordinateLenU64 c) in 
    let pAffineX, pAffineY = point_affine_as_nat c h0 pAffine in 

    assert_norm (2 * v d + 1 < getOrder #c);

    if (pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (pAffineX, pAffineY))) (point_mult #c (2 * v d + 1) (basePoint #c))) then begin
	Hacl.Impl.EC.ScalarMult.Radix.curve_order_is_the_smallest1 #c (basePoint #c) (2 * v d + 1);
	lemma_pointAtInfInDomain #c (toJacobianCoordinates (pAffineX, pAffineY))
    end;

    if (pointEqual (fromDomainPoint #c #DH (toJacobianCoordinates (pAffineX, pAffineY))) (point_mult #c (- (2 * v d + 1)) (basePoint #c))) then begin

      lemma_scalar_reduce #c (basePoint #c) (- (2 * v d + 1));
      lemma_mod_sub_1 (2 * v d + 1) (getOrder #c);
      small_mod (2 * v d + 1) (getOrder #c);
      Hacl.Impl.EC.ScalarMult.Radix.curve_order_is_the_smallest1 #c (basePoint #c) (getOrder #c - (2 * v d + 1));
      lemma_pointAtInfInDomain #c (toJacobianCoordinates (pAffineX, pAffineY))
    end


inline_for_extraction noextract
val point_add_complete_last_step_: #c: curve 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c)
  -> temp3: point c
  -> d: uint64 {v d < pow2 (w - 1)}
  -> flag: uint64 {v flag == 0 \/ v flag == pow2 64 - 1} ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h tempBuffer /\ point_eval c h result /\ live h temp3 /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc tempBuffer; loc temp3] /\ rwnaf_invariant #c rnaf h /\
    ~ (isPointAtInfinity (point_as_nat c h result)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc temp3 |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    if v flag = 0 then
      pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 result)) (pointAdd #c (point_mult #c (2 * v d + 1) (basePoint #c)) (fromDomainPoint #c #DH (point_as_nat c h0 result)))
    else 
      pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 result)) (pointAdd #c (point_mult #c ( - (2 * v d + 1)) (basePoint #c)) (fromDomainPoint #c #DH (point_as_nat c h0 result)))))


let point_add_complete_last_step_ #c rnaf result tempBuffer temp3 d is_neg = 
    let h0 = ST.get() in 
  let temp2 = sub temp3 (size 0) (size 2 *! getCoordinateLenU64 c) in 
  loopK #c d temp2 0ul; 
    let h1 = ST.get() in
    assert_norm (pow2 (w - 1) < getOrder #c);
    scalar_mult_cmb_composite_not_infinity #c 0 (2 * v d + 1);
  point_neg_conditional #c temp2 tempBuffer is_neg;
    let h2 = ST.get() in 
    point_add_complete_last_step_lemma1 #c d (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h1 temp2))) (fromDomainPoint #c #DH (toJacobianCoordinates (point_affine_as_nat c h2 temp2)));
  point_add_complete_last_step_to_jacobian #c d temp3;
    let h3 = ST.get() in 
    assert(
      if v is_neg = 0 then 
	pointEqual (fromDomainPoint #c #DH (point_as_nat c h3 temp3)) (point_mult #c (2 * v d + 1) (basePoint #c))
      else
	pointEqual (fromDomainPoint #c #DH (point_as_nat c h3 temp3)) (point_mult #c (- (2 * v d + 1)) (basePoint #c)));

    lemma_pointAtInfInDomain #c (point_as_nat c h3 temp3);
    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h3 result;    
  Hacl.Impl.EC.PointAddC.point_add_c_ct #c temp3 result result tempBuffer;
  
    if v is_neg = 0 then 
      curve_compatibility_with_translation_lemma (fromDomainPoint #c #DH (point_as_nat c h3 temp3)) (point_mult #c (2 * v d + 1) (basePoint #c)) (fromDomainPoint #c #DH (point_as_nat c h3 result))
    else
      curve_compatibility_with_translation_lemma (fromDomainPoint #c #DH (point_as_nat c h3 temp3)) (point_mult #c (- (2 * v d + 1)) (basePoint #c)) (fromDomainPoint #c #DH (point_as_nat c h3 result))


inline_for_extraction noextract
val point_add_complete_last_step: #c: curve 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h tempBuffer /\ point_eval c h result /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc tempBuffer] /\ rwnaf_invariant #c rnaf h /\
    ~ (isPointAtInfinity (point_as_nat c h result)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let d0 = v (Lib.Sequence.index (as_seq h0 rnaf) 0) in 
    let is_neg = v (Lib.Sequence.index (as_seq h0 rnaf) 1) in 
    let result0 = fromDomainPoint #c #DH (point_as_nat c h0 result) in
    let result1 = fromDomainPoint #c #DH (point_as_nat c h1 result) in
    if is_neg = 0 then
      pointEqual result1 (pointAdd #c (point_mult #c ((d0 - 1) / 2 * 2 + 1) (basePoint #c)) result0)
    else 
      pointEqual result1 (pointAdd #c (point_mult #c ( - ((d0 - 1) / 2 * 2 + 1)) (basePoint #c)) result0)))

let point_add_complete_last_step #c rnaf result tempBuffer = 
  let h0 = ST.get() in 
  push_frame(); 
    let temp3 = create (size 3 *! getCoordinateLenU64 c) (u64 0) in 
    let d = compute_index_rwnaf rnaf 0ul in 
    let is_neg = index rnaf 1ul in 
    
      point_add_complete_last_step_lemma0 h0 rnaf; 
      let h1 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 result; 
    point_add_complete_last_step_ #c rnaf result tempBuffer temp3 d is_neg;

    let h2 = ST.get() in 
  pop_frame();
    let h3 = ST.get() in 

    Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h2 h3 result




inline_for_extraction noextract
val point_add_complete_last_step_main_: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h tempBuffer /\ point_eval c h result /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc tempBuffer] /\ rwnaf_invariant #c rnaf h /\
    ~ (isPointAtInfinity (point_as_nat c h result)) /\ (
    let d = scalar_as_nat (as_seq h scalar) in
    let n = v (getScalarLen c) in 
    d < pow2 n /\ rnaf_to_spec #c (as_seq h rnaf) == to_wnaf n (scalarToOdd n d)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let d = scalar_as_nat (as_seq h0 scalar) in
    let n = v (getScalarLen c) in 
    let s = to_wnaf n (scalarToOdd n d) in 
    let result0 = fromDomainPoint #c #DH (point_as_nat c h0 result) in
    let result1 = fromDomainPoint #c #DH (point_as_nat c h1 result) in
    let p0 = basePoint #c in 
    pointEqual result1 (wnaf_step2 #c p0 s (n / w) result0) /\
    pointEqual result1 (pointAdd #c (point_mult #c (Seq.index s 0) (basePoint #c)) result0)))

let point_add_complete_last_step_main_ #c scalar rnaf result tempBuffer = 
  let h0 = ST.get() in 
    point_add_complete_last_step rnaf result tempBuffer;
  let h1 = ST.get() in 

    let d = scalar_as_nat (as_seq h0 scalar) in
    let n = v (getScalarLen c) in 
    let s = to_wnaf n (scalarToOdd n d) in 

    point_add_complete_last_step_main_lemma0 #c (as_seq h0 rnaf) s;
    point_add_complete_last_step_main_lemma1 #c (as_seq h0 scalar) (as_seq h0 rnaf);

    let result0 = fromDomainPoint #c #DH (point_as_nat c h0 result) in
    let result1 = fromDomainPoint #c #DH (point_as_nat c h1 result) in

    lemma_wnaf_step2 #c (as_seq h0 rnaf) (n / w) result0;
    curve_commutativity_lemma result0 (point_mult  #c (Seq.index s 0) (basePoint #c))


let point_add_complete_last_step_main_p256 = point_add_complete_last_step_main_ #P256

let point_add_complete_last_step_main_p384 = point_add_complete_last_step_main_ #P384


inline_for_extraction noextract
val point_add_complete_last_step_main: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h tempBuffer /\ point_eval c h result /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc tempBuffer] /\ rwnaf_invariant #c rnaf h /\
    ~ (isPointAtInfinity (point_as_nat c h result)) /\ (
    let d = scalar_as_nat (as_seq h scalar) in
    let n = v (getScalarLen c) in 
    d < pow2 n /\ rnaf_to_spec #c (as_seq h rnaf) == to_wnaf n (scalarToOdd n d)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let d = scalar_as_nat (as_seq h0 scalar) in
    let n = v (getScalarLen c) in 
    let s = to_wnaf n (scalarToOdd n d) in 
    let result0 = fromDomainPoint #c #DH (point_as_nat c h0 result) in
    let result1 = fromDomainPoint #c #DH (point_as_nat c h1 result) in
    let p0 = basePoint #c in 
    pointEqual result1 (wnaf_step2 #c p0 s (n / w) result0) /\
    pointEqual result1 (pointAdd #c (point_mult #c (Seq.index s 0) (basePoint #c)) result0)))

let point_add_complete_last_step_main #c scalar rnaf result tempBuffer = 
  match c with 
  |P256 -> point_add_complete_last_step_main_p256 scalar rnaf result tempBuffer
  |P384 -> point_add_complete_last_step_main_p384 scalar rnaf result tempBuffer


inline_for_extraction noextract
val scalar_multiplication_cmb_step1: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> k: size_t {v k < v (getLenWnaf #c) + 1}
  -> pointPrecomputed: pointAffine c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h pointPrecomputed /\ live h tempBuffer /\ live h scalar /\ 
    point_eval c h result /\ 
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc pointPrecomputed; loc tempBuffer] /\
    rwnaf_invariant #c rnaf h /\ (
    let d = scalar_as_nat (as_seq h scalar) in
    let n = getPower c in 
    let j = v (getLenWnaf #c) - v k in 
    d < pow2 n /\ rnaf_to_spec #c (as_seq h rnaf) == to_wnaf n (scalarToOdd n d) /\ (
    let s = to_wnaf n (scalarToOdd n d) in 
    let b = pow2 (j * w) * (Seq.index s j) % getOrder #c in
      ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h result)) (point_mult #c b (basePoint #c))))))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc pointPrecomputed |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let n = getPower c in 
    let d = scalar_as_nat (as_seq h0 scalar) in
    let s = to_wnaf n (scalarToOdd n d) in 
    let pD = fromDomainPoint #c #DH (point_as_nat c h0 result) in 
    let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    let j = v (getLenWnaf #c) - v k in 
    pointEqual result (pointAdd #c pD (point_mult #c (pow2 (j * w) * Seq.index s j) (basePoint #c)))))


let scalar_multiplication_cmb_step1 #c scalar rnaf result k pointPrecomputed tempBuffer = 
    let h0 = ST.get() in 
  let j = getLenWnaf #c -! k in 
  lemma_scalar_step1 #c (as_seq h0 scalar) (as_seq h0 rnaf) (v j) (fromDomainPoint #c #DH (point_as_nat c h0 result));
  scalar_multiplication_cmb_step_2 #c rnaf result j pointPrecomputed tempBuffer;
    let h1 = ST.get() in 

  let d = scalar_as_nat (as_seq h0 scalar) in 
  let pD = fromDomainPoint #c #DH (point_as_nat c h0 result) in 
  let n = getPower c in 
  let s =  to_wnaf n (scalarToOdd n d) in 
  let bits = Seq.index s (v (getLenWnaf #c) - v k) in
  let p0 = basePoint #c in 

  let rnaf_2j = v (Lib.Sequence.index (as_seq h0 rnaf) (2 * v j)) in 
  let is_neg_rnaf_2j = v (Lib.Sequence.index (as_seq h0 rnaf) (2 * v j + 1)) in 

  assert(rnaf_to_spec #c (as_seq h0 rnaf) == s);
  
  assert(
    let rnaf_2j = v (Lib.Sequence.index (as_seq h0 rnaf) (2 * v j)) in 
    let is_neg_rnaf_2j = v (Lib.Sequence.index (as_seq h0 rnaf) (2 * v j + 1)) in 
    let b = 
      if is_neg_rnaf_2j = 0 then 
	(pow2 (v j * w) * ((rnaf_2j - 1) / 2 * 2 + 1) % getOrder #c) 
      else 
        - (pow2 (v j * w) * ((rnaf_2j - 1) / 2 * 2 + 1) % getOrder #c) in 
    let r = pointAdd #c pD (point_mult #c b (basePoint #c)) in 
    pointEqual (fromDomainPoint #c #DH (point_as_nat c h1 result)) r);

  lemma_3 #c (as_seq h0 rnaf) (as_seq h0 scalar) (v j) (fromDomainPoint #c #DH (point_as_nat c h1 result)) pD


inline_for_extraction noextract
val scalar_multiplication_cmb_step: #c: curve 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> result: point c
  -> k: size_t {v k < v (getLenWnaf #c) + 1}
  -> pointPrecomputed: pointAffine c
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) ->
  Stack unit 
  (requires fun h -> live h rnaf /\ live h result /\ live h pointPrecomputed /\ live h tempBuffer /\ live h scalar /\ 
    point_eval c h result /\ 
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc pointPrecomputed; loc tempBuffer] /\
    rwnaf_invariant #c rnaf h /\ (
    let d = scalar_as_nat (as_seq h scalar) in
    let n = getPower c in 
    let j = v (getLenWnaf #c) - v k in 
    d < pow2 n /\ rnaf_to_spec #c (as_seq h rnaf) == to_wnaf n (scalarToOdd n d) /\ (
    let s = to_wnaf n (scalarToOdd n d) in 
    let b = pow2 (j * w) * (Seq.index s j) % getOrder #c in
      ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h result)) (point_mult #c b (basePoint #c))))))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc pointPrecomputed |+| loc tempBuffer) h0 h1 /\ point_eval c h1 result /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h0 result) in 
    let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    pointEqual (wnaf_step2 #c (basePoint #c) (rnaf_to_spec #c (as_seq h0 rnaf)) (v k) pD) result))


let scalar_multiplication_cmb_step #c scalar rnaf result k pointPrecomputed tempBuffer = 
  let h0 = ST.get() in 
  scalar_multiplication_cmb_step1 #c scalar rnaf result k pointPrecomputed tempBuffer; 

  let h1 = ST.get() in 
  
  let n = getPower c in 
  let d = scalar_as_nat (as_seq h0 scalar) in

  let j = v (getLenWnaf #c) - v k in 
  let pD = fromDomainPoint #c #DH (point_as_nat c h0 result) in 
  let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 

  let s = to_wnaf n (scalarToOdd n d) in 
  let bits = Seq.index s (v (getLenWnaf #c) - v k) in 
  let p0 = (basePoint #c) in 
    assert(pointEqual result (pointAdd #c pD (point_mult #c (pow2 (j * w) * bits) p0)));
  lemma_wnaf_step2 #c (as_seq h0 rnaf) (v k) pD;
    assert(pointEqual (wnaf_step2 #c p0 s (v k) pD) (pointAdd pD (point_mult #c (pow2 (w * j) * bits) p0)));
  curve_compatibility_with_translation_lemma result (wnaf_step2 #c (basePoint #c) (rnaf_to_spec #c (as_seq h0 rnaf)) (v k) pD) (pointAdd pD (point_mult (pow2 (w * j) * bits) p0));
    assert(pointEqual (wnaf_step2 #c (basePoint #c) (rnaf_to_spec #c (as_seq h0 rnaf)) (v k) pD) result)


inline_for_extraction noextract
val scalar_multiplication_cmb_loop: #c: curve -> result: point c 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> temp: lbuffer uint64 (size 2 *! getCoordinateLenU64 c)
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h -> live h result /\ live h rnaf /\ live h temp /\ live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc temp; loc tempBuffer; loc rnaf; loc scalar] /\ 
    point_eval c h result /\ rwnaf_invariant #c rnaf h /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h result) in 
    isPointAtInfinity result) /\ (
    let n = getPower c in 
    let d = scalar_as_nat (as_seq h scalar) in
    d < getOrder #c /\ rnaf_to_spec #c (as_seq h rnaf) ==  to_wnaf n (scalarToOdd n d)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer |+| loc temp) h0 h1 /\ point_eval c h1 result /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    let j = v (getLenWnaf #c) in 
    let pointAtInfinity = (0, 0, 0) in 
    let d = scalar_as_nat (as_seq h0 scalar) in
    let n = getPower c in
    let s = to_wnaf n (scalarToOdd n d) in
    let b = from_wnaf_ s 1 * pow2 w in 
    pointEqual #c result (repeati j (wnaf_step2 (basePoint #c) (rnaf_to_spec #c (as_seq h0 rnaf))) pointAtInfinity) /\
    pointEqual #c result (point_mult #c b (basePoint #c))))

let scalar_multiplication_cmb_loop #c result scalar rnaf temp tempBuffer = 
  let h0 = ST.get() in 
  let lenWnaf = getLenWnaf #c +! 1ul in 
  let invJ h (j: nat {j <= v (getLenWnaf #c)} ) = 
    live h rnaf /\ live h result /\ live h temp /\ live h tempBuffer /\ live h scalar /\ point_eval c h result /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc temp; loc tempBuffer; loc rnaf; loc scalar] /\
    rwnaf_invariant #c rnaf h /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h result) in 
    pointEqual #c result (repeati j (wnaf_step2 (basePoint #c) (rnaf_to_spec #c (as_seq h0 rnaf))) (0, 0, 0))) /\
    modifies (loc result |+| loc temp |+| loc tempBuffer) h0 h /\ (
    
    let d = scalar_as_nat (as_seq h scalar) in
    let n = getPower c in
       d < getOrder #c /\ rnaf_to_spec #c (as_seq h rnaf) == to_wnaf n (scalarToOdd n d) /\ (
    let len = n / w + 1 in 
    let s = to_wnaf n (scalarToOdd n d) in
    let b = from_wnaf_ s (len - j) * pow2 (w * (len - j)) in 
    pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h result)) (point_mult #c b (basePoint #c)))) in 

  eq_repeati0 (v (getLenWnaf #c +! 1ul)) (wnaf_step2 #c (basePoint #c) (rnaf_to_spec #c (as_seq h0 rnaf))) (0, 0, 0);
  lemma_from_wnaf_last0 (let d = scalar_as_nat (as_seq h0 scalar) in let n = getPower c in to_wnaf n (scalarToOdd n d));
  Hacl.Impl.EC.ScalarMult.Radix.point_mult_0_for_zero #c (basePoint #c);

  Lib.Loops.for 0ul (lenWnaf -! 1ul) invJ (fun j -> 
    let h0_ = ST.get() in 

    lemma_from_domain_is_not_equal_index_main #c (as_seq h0_ scalar) (v j) (fromDomainPoint #c #DH (point_as_nat c h0_ result));
    scalar_multiplication_cmb_step scalar rnaf result j temp tempBuffer;

    let h1_ = ST.get() in 

    let f = wnaf_step2 #c (basePoint #c) (rnaf_to_spec #c (as_seq h0 rnaf)) in 
    let p0 = basePoint #c in 
    let pD = fromDomainPoint #c #DH (point_as_nat c h0_ result) in
    
    unfold_repeati (v lenWnaf) f (0, 0, 0) (v j);
    lemma_application_wnaf_step_on_equal_points #c p0 (rnaf_to_spec #c (as_seq h0 rnaf)) pD (repeati (v j) f (0, 0, 0)) (v j);
    pred1 #c (let d = scalar_as_nat (as_seq h0 scalar) in let n = getPower c in to_wnaf n (scalarToOdd n d)) p0 (v j) pD)


inline_for_extraction noextract
val scalar_multiplication_cmb_loop_last_bit_: #c: curve -> result: point c 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> temp: lbuffer uint64 (size 2 *! getCoordinateLenU64 c)
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h -> live h result /\ live h rnaf /\ live h temp /\ live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc temp; loc tempBuffer; loc rnaf; loc scalar] /\ 
    point_eval c h result /\ rwnaf_invariant #c rnaf h /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h result) in 
    isPointAtInfinity result) /\ (
    let d = scalar_as_nat (as_seq h scalar) in
    let n = getPower c in
    d < getOrder #c /\ rnaf_to_spec #c (as_seq h rnaf) == to_wnaf n (scalarToOdd n d)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer |+| loc temp) h0 h1 /\ point_eval c h1 result /\ (
    let d = scalar_as_nat (as_seq h1 scalar) in
    let n = getPower c in
    let s = to_wnaf n (scalarToOdd n d) in 
    pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) (point_mult #c (from_wnaf_ s 1 * pow2 w + Seq.index s 0) (basePoint #c)) /\
    pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) (repeati (n / w + 1) (wnaf_step2 #c (basePoint #c) s) (0, 0, 0))))

let scalar_multiplication_cmb_loop_last_bit_ #c result scalar rnaf temp tempBuffer = 
    let h0 = ST.get() in 
  scalar_multiplication_cmb_loop #c result scalar rnaf temp tempBuffer;
    let h1 = ST.get() in 
    lemma_the_last_before_one_point_add_is_not_infinity (as_seq h0 scalar) (point_as_nat c h1 result);
  point_add_complete_last_step_main scalar rnaf result tempBuffer;
    let h2 = ST.get() in 

    let d = scalar_as_nat (as_seq h1 scalar) in
    let n = getPower c in
    let s = to_wnaf n (scalarToOdd n d) in 

    let b = from_wnaf_ s 1 * pow2 w in 
    let result0 = (fromDomainPoint #c #DH (point_as_nat c h1 result))  in 
    let result1 = (fromDomainPoint #c #DH (point_as_nat c h2 result))  in 

    Hacl.Impl.EC.ScalarMult.Radix.curve_compatibility_with_translation_lemma_1 result0  (point_mult #c b (basePoint #c)) (point_mult #c (Seq.index s 0) (basePoint #c));


    let p0 = (point_mult #c b (basePoint #c)) in 
    let p1 = (point_mult #c (Seq.index s 0) (basePoint #c)) in 

    lemmaApplPointAdd #c (basePoint #c) b p0 (Seq.index s 0) p1;
    curve_commutativity_lemma p0 p1; 

    assert(pointEqual (pointAdd #c p0 p1) (point_mult (b + Seq.index s 0) (basePoint #c)));

    assert(pointEqual #c result0 p0);
    assert(pointEqual result1 (point_mult #c (b + Seq.index s 0) (basePoint #c)));

    unfold_repeati (v (getScalarLen c) / w + 1) (wnaf_step2 #c (basePoint #c) s) (0, 0, 0) (v (getScalarLen c) / w);
    lemma_application_wnaf_step_on_equal_points #c (basePoint #c) s (fromDomainPoint #c #DH (point_as_nat c h1 result)) (repeati (n / w) (wnaf_step2 (basePoint #c) s) (0, 0, 0)) (n / w)


inline_for_extraction noextract
val scalar_multiplication_cmb_loop_last_bit: #c: curve -> result: point c 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> temp: lbuffer uint64 (size 2 *! getCoordinateLenU64 c)
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h -> live h result /\ live h rnaf /\ live h temp /\ live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc temp; loc tempBuffer; loc rnaf; loc scalar] /\ 
    point_eval c h result /\ rwnaf_invariant #c rnaf h /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h result) in 
    isPointAtInfinity result) /\ (
    let d = scalar_as_nat (as_seq h scalar) in
    let n = getPower c in
    d < getOrder #c /\ rnaf_to_spec #c (as_seq h rnaf) == to_wnaf n (scalarToOdd n d)))
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer |+| loc temp) h0 h1 /\ point_eval c h1 result /\ (
    let d = scalar_as_nat (as_seq h0 scalar) in
    let n = getPower c in
    let s = to_wnaf n (scalarToOdd n d) in 
    let r = repeati (n / w + 1) (wnaf_step2 #c (basePoint #c) s) (0, 0, 0) in 
    let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    if scalar_as_nat #c (as_seq h0 scalar) % 2 = 1 then
	pointEqual #c result r
      else
	pointEqual #c result (pointAdd #c r (Spec.ECC.point_mult #c (- 1) (basePoint #c)))))

let scalar_multiplication_cmb_loop_last_bit #c result scalar rnaf temp tempBuffer = 
    let h0 = ST.get() in 
  scalar_multiplication_cmb_loop_last_bit_ result scalar rnaf temp tempBuffer;
    let h1 = ST.get() in 
    lemma_last_bit #c (as_seq h0 scalar) (fromDomainPoint #c #DH (point_as_nat c h1 result));
  conditional_substraction #c result result scalar tempBuffer;
    let h2 = ST.get() in 

    let d = scalar_as_nat (as_seq h0 scalar) in
    let n = getPower c in
    let s = to_wnaf n (scalarToOdd n d) in 


    let n_1P = (repeati (n / w + 1) (wnaf_step2 #c (basePoint #c) s) (0, 0, 0)) in 

    assert(pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) n_1P);

    scalar_multiplication_cmb_last_bit_lemma0 (as_seq h0 scalar); 
    curve_compatibility_with_translation_lemma #c (fromDomainPoint #c #DH (point_as_nat c h1 result)) n_1P (Spec.ECC.point_mult #c (- 1) (basePoint #c));

    assert(
      if scalar_as_nat #c (as_seq h0 scalar) % 2 = 1 then
	pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h2 result)) (repeati (n / w + 1) (wnaf_step2 #c (basePoint #c) s) (0, 0, 0))
      else
	pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h2 result)) (pointAdd #c n_1P (Spec.ECC.point_mult #c (- 1) (basePoint #c))))


inline_for_extraction noextract
val scalar_multiplication_cmb__: #c: curve -> result: point c 
  -> scalar: scalar_t #MUT #c 
  -> rnaf: lbuffer uint64 (size (2 * (v (getScalarLen c) / w + 1)))
  -> temp: lbuffer uint64 (size 2 *! getCoordinateLenU64 c)
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h -> live h result /\ live h rnaf /\ live h temp /\ live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint[loc result; loc temp; loc tempBuffer; loc rnaf; loc scalar] /\ 
    point_eval c h result /\
    isPointAtInfinity (fromDomainPoint #c #DH (point_as_nat c h result)) /\
    scalar_as_nat (as_seq h scalar) < getOrder #c /\ 
    v (Lib.Sequence.index (as_seq h rnaf) (2 * (v (getScalarLen c) / w) + 1)) == 0)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer |+| loc temp |+| loc rnaf) h0 h1 /\ 
    point_eval c h1 result /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    pointEqual result (wnaf_spec #c (as_seq h0 scalar) (basePoint #c)) /\
    pointEqual result (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) (basePoint #c))))
    
let scalar_multiplication_cmb__ #c result scalar rnaf temp tempBuffer = 
    let h0 = ST.get() in 
  scalar_rwnaf0 #c rnaf scalar;
    let h1 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 result;
  scalar_multiplication_cmb_loop_last_bit result scalar rnaf temp tempBuffer;
    let h2 = ST.get() in 

  let r_wnaf_spec = wnaf_spec #c (as_seq h0 scalar) (basePoint #c) in 

  let d = scalar_as_nat (as_seq h0 scalar) in
  let n = getPower c in
  let s = to_wnaf n (scalarToOdd n d) in 
  let p0 = basePoint #c in 
  
  let result = fromDomainPoint #c #DH (point_as_nat c h2 result) in 

  assert(
    let r0 = repeati (n / w + 1) (wnaf_step2 #c p0 s) (0, 0, 0) in 
    if scalar_as_nat #c (as_seq h0 scalar) % 2 = 1 then 
      pointEqual r_wnaf_spec result
    else 
      pointEqual r_wnaf_spec result)




inline_for_extraction noextract
val scalar_multiplication_cmb_: #c: curve -> result: point c -> 
  scalar: scalar_t #MUT #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h ->  live h result /\ live h tempBuffer /\ live h scalar /\ 
    disjoint result scalar /\ disjoint result tempBuffer /\ disjoint scalar tempBuffer /\
    scalar_as_nat (as_seq h scalar) < getOrder #c )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 result /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    pointEqual result (wnaf_spec #c (as_seq h0 scalar) (basePoint #c)) /\
    pointEqual result (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) (basePoint #c))))

let scalar_multiplication_cmb_ #c  result scalar tempBuffer = 
  push_frame();
    let lenWnaf = getLenWnaf #c +! 1ul in 
    let rnaf = create (size 2 *! lenWnaf) (u64 0) in 
    let temp = create (size 2 *! getCoordinateLenU64 c) (u64 0) in 

    uploadZeroPoint result;
      let h = ST.get() in 

    lemma_pointAtInfInDomain #c (point_as_nat c h result);
    scalar_multiplication_cmb__ result scalar rnaf temp tempBuffer;

  pop_frame()


let scalar_multiplication_cmb_p256 = scalar_multiplication_cmb_ #P256

let scalar_multiplication_cmb_p384 = scalar_multiplication_cmb_ #P384


inline_for_extraction noextract
val scalar_multiplication_cmb: #c: curve -> result: point c -> 
  scalar: scalar_t #MUT #c -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit
  (requires fun h ->  live h result /\ live h tempBuffer /\ live h scalar /\ 
    disjoint result scalar /\ disjoint result tempBuffer /\ disjoint scalar tempBuffer /\
    scalar_as_nat (as_seq h scalar) < getOrder #c )
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 result /\ (
    let result = fromDomainPoint #c #DH (point_as_nat c h1 result) in 
    pointEqual result (wnaf_spec #c (as_seq h0 scalar) (basePoint #c)) /\
    pointEqual result (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) (basePoint #c))))

let scalar_multiplication_cmb #c result scalar tempBuffer = 
  match c with 
  |P256 -> scalar_multiplication_cmb_p256 result scalar tempBuffer
  |P384 -> scalar_multiplication_cmb_p384 result scalar tempBuffer