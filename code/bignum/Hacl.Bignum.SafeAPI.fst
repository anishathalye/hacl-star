module Hacl.Bignum.SafeAPI

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module LSeq = Lib.Sequence

module E = Hacl.Spec.Exponentiation.Lemmas

module BL = Hacl.Bignum.Lib
module BB = Hacl.Bignum.Base
module BN = Hacl.Bignum
module MA = Hacl.Bignum.MontArithmetic
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module BR = Hacl.Bignum.ModReduction
module BC = Hacl.Bignum.Convert
module BI = Hacl.Bignum.ModInv

module SL = Hacl.Spec.Bignum.Lib
module SD = Hacl.Spec.Bignum.Definitions
module SE = Hacl.Spec.Bignum.Exponentiation
module SM = Hacl.Spec.Bignum.Montgomery
module SC = Hacl.Spec.Bignum.Convert
module SI = Hacl.Spec.Bignum.ModInv

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let new_bn_from_bytes_be_st (t:limb_t) =
    r:HS.rid
  -> #l:Ghost.erased size_t
  -> b:lbuffer uint8 l
  -> len:size_t{len = Ghost.reveal l} ->
  ST (B.buffer (limb t))
  (requires fun h ->
    live h b /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t /\
      B.len res == blocks len (size (numbytes t)) /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t (blocks len (size (numbytes t)))) == SC.bn_from_bytes_be (v len) (as_seq h0 b)))


inline_for_extraction noextract
val new_bn_from_bytes_be: #t:limb_t -> new_bn_from_bytes_be_st t
let new_bn_from_bytes_be #t r b len =
  [@inline_let]
  let numb = size (numbytes t) in
  if len = 0ul || not (blocks len numb <=. 0xfffffffful `FStar.UInt32.div` numb) then
    B.null
  else
    let h0 = ST.get () in
    let res = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t 0) (blocks len numb) in
    if B.is_null res then
      res
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len res == blocks len numb);
      let res: Lib.Buffer.buffer (limb t) = res in
      assert (B.length res == FStar.UInt32.v (blocks len numb));
      let res: lbignum t (blocks len numb) = res in
      BC.mk_bn_from_bytes_be false len res b;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      res


inline_for_extraction noextract
let new_bn_from_bytes_le_st (t:limb_t) =
    r:HS.rid
  -> #l:Ghost.erased size_t
  -> b:lbuffer uint8 l
  -> len:size_t{len = Ghost.reveal l} ->
  ST (B.buffer (limb t))
  (requires fun h ->
    live h b /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      0 < v len /\ numbytes t * v (blocks len (size (numbytes t))) <= max_size_t /\
      B.len res == blocks len (size (numbytes t)) /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
      as_seq h1 (res <: lbignum t (blocks len (size (numbytes t)))) == SC.bn_from_bytes_le (v len) (as_seq h0 b)))


inline_for_extraction noextract
val new_bn_from_bytes_le: #t:limb_t -> new_bn_from_bytes_le_st t
let new_bn_from_bytes_le #t r b len =
  [@inline_let]
  let numb = size (numbytes t) in
  if len = 0ul || not (blocks len numb <=. 0xfffffffful `FStar.UInt32.div` numb) then
    B.null
  else
    let h0 = ST.get () in
    let res = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t 0) (blocks len numb) in
    if B.is_null res then
      res
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len res == blocks len numb);
      let res: Lib.Buffer.buffer (limb t) = res in
      assert (B.length res == FStar.UInt32.v (blocks len numb));
      let res: lbignum t (blocks len numb) = res in
      BC.mk_bn_from_bytes_le false len res b;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      res


inline_for_extraction noextract
let bn_mod_slow_safe_st (t:limb_t) (len:BN.meta_len t) =
    output:lbignum t len
  -> n:lbignum t len
  -> a:lbignum t (len +! len) ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h output /\
    disjoint output n /\ disjoint output a)
  (ensures  fun h0 r h1 -> modifies (loc output) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SM.bn_check_modulus (as_seq h0 n)) /\
    (r ==> bn_v h1 output == bn_v h0 a % bn_v h0 n))


inline_for_extraction noextract
val mk_bn_mod_slow_safe:
    #t:limb_t
  -> len:BN.meta_len t
  -> bn_mod_slow:BR.bn_mod_slow_st t len ->
  bn_mod_slow_safe_st t len

let mk_bn_mod_slow_safe #t len bn_mod_slow output n a =
  let h0 = ST.get () in
  let is_valid_m = BM.bn_check_modulus n in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    bn_mod_slow nBits n a output end
  else
    memset output (uint #t 0) len;
  BB.unsafe_bool_of_limb is_valid_m


inline_for_extraction noextract
let bn_mod_exp_safe_st (t:limb_t) (len:BN.meta_len t) =
    output:lbignum t len
  -> n:lbignum t len
  -> a:lbignum t len
  -> #l:Ghost.erased size_t{bits t * v (blocks0 l (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks0 l (size (bits t)))
  -> b_bits:size_t{b_bits = Ghost.reveal l} ->
  Stack bool
  (requires fun h ->
    live h n /\ live h a /\ live h b /\ live h output /\
    disjoint output a /\ disjoint output b /\ disjoint output n /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc output) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SE.bn_check_mod_exp (as_seq h0 n) (as_seq h0 a) (v b_bits) (as_seq h0 b)) /\
    (r ==> SE.bn_mod_exp_post (as_seq h0 n) (as_seq h0 a) (v b_bits) (as_seq h0 b) (as_seq h1 output)))


inline_for_extraction noextract
val mk_bn_mod_exp_safe:
    #t:limb_t
  -> len:BN.meta_len t
  -> exp_check:BE.bn_check_mod_exp_st t len
  -> bn_mod_exp:BE.bn_mod_exp_st t len ->
  bn_mod_exp_safe_st t len

let mk_bn_mod_exp_safe #t len exp_check bn_mod_exp output n a b b_bits =
  let h0 = ST.get () in
  let is_valid_m = exp_check n a b_bits b in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    bn_mod_exp nBits n a b_bits b output end
  else
    memset output (uint #t 0) len;
  BB.unsafe_bool_of_limb is_valid_m


inline_for_extraction noextract
let bn_mod_inv_prime_safe_st (t:limb_t) (len:BN.meta_len t) =
    output:lbignum t len
  -> n:lbignum t len
  -> a:lbignum t len ->
  Stack bool
  (requires fun h -> FStar.Math.Euclid.is_prime (bn_v h n) /\
    live h n /\ live h a /\ live h output /\
    disjoint output n /\ disjoint output a /\ disjoint n a)
  (ensures  fun h0 r h1 -> modifies (loc output) h0 h1 /\
    r == BB.unsafe_bool_of_limb (SI.bn_check_mod_inv_prime (as_seq h0 n) (as_seq h0 a)) /\
   (r ==> bn_v h1 output * bn_v h0 a % bn_v h0 n = 1))


inline_for_extraction noextract
val mk_bn_mod_inv_prime_safe:
    #t:limb_t
  -> len:BN.meta_len t
  -> bn_mod_exp:BE.bn_mod_exp_st t len ->
  bn_mod_inv_prime_safe_st t len

let mk_bn_mod_inv_prime_safe #t len bn_mod_exp output n a =
  let h0 = ST.get () in
  let is_valid_m = BI.bn_check_mod_inv_prime #t len n a in
  let nBits = size (bits t) *! BB.unsafe_size_from_limb (BL.bn_get_top_index len n) in

  if BB.unsafe_bool_of_limb is_valid_m then begin
    SL.bn_low_bound_bits_lemma #t #(v len) (as_seq h0 n);
    BI.mk_bn_mod_inv_prime len bn_mod_exp nBits n a output end
  else
    memset output (uint #t 0) len;
  BB.unsafe_bool_of_limb is_valid_m


inline_for_extraction noextract
let bn_mod_slow_ctx_st (t:limb_t) (len:BN.meta_len t) =
    ctx:MA.pbn_mont_ctx t
  -> output:lbignum t len
  -> a:lbignum t (len +! len) ->
  Stack unit
  (requires fun h ->
    (B.deref h ctx).MA.len == len /\
    MA.pbn_mont_ctx_inv h ctx /\

    live h a /\ live h output /\ disjoint output a /\
    B.(loc_disjoint (MA.footprint h ctx) (loc_buffer (output <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
    bn_v h1 output == bn_v h0 a % MA.bn_v_n h0 ctx)


inline_for_extraction noextract
val bn_mod_ctx:
    #t:limb_t
  -> len:Ghost.erased _
  -> bn_mod_slow_precomp:BR.bn_mod_slow_precomp_st t len ->
  bn_mod_slow_ctx_st t len

let bn_mod_ctx #t len bn_mod_slow_precomp ctx output a =
  let open LowStar.BufferOps in
  let k = !*ctx in
  bn_mod_slow_precomp k.MA.n k.MA.mu k.MA.r2 a output


inline_for_extraction noextract
let bn_mod_exp_ctx_st (t:limb_t) (len:BN.meta_len t) =
    ctx:MA.pbn_mont_ctx t
  -> output:lbignum t len
  -> a:lbignum t len
  -> #l:Ghost.erased size_t
  -> b:lbignum t (blocks0 l (size (bits t)))
  -> b_bits:size_t{b_bits = Ghost.reveal l} ->
  Stack unit
  (requires fun h ->
    (B.deref h ctx).MA.len == len /\
    MA.pbn_mont_ctx_inv h ctx /\
    bn_v h a < MA.bn_v_n h ctx /\
    bn_v h b < pow2 (v b_bits) /\

    live h a /\ live h b /\ live h output /\
    disjoint output a /\ disjoint output b /\
    B.(loc_disjoint (MA.footprint h ctx) (loc_buffer (a <: buffer (limb t)))) /\
    B.(loc_disjoint (MA.footprint h ctx) (loc_buffer (output <: buffer (limb t)))))
  (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
    SE.bn_mod_exp_post (as_seq #MUT #(limb t) h0 (B.deref h0 ctx).MA.n)
      (as_seq h0 a) (v b_bits) (as_seq h0 b) (as_seq h1 output))


inline_for_extraction noextract
val mk_bn_mod_exp_ctx:
    #t:limb_t
  -> len:Ghost.erased _
  -> bn_mod_exp_precomp:BE.bn_mod_exp_precomp_st t len ->
  bn_mod_exp_ctx_st t len

let mk_bn_mod_exp_ctx #t len bn_mod_exp_precomp ctx output a b b_bits =
  let open LowStar.BufferOps in
  let k = !*ctx in
  bn_mod_exp_precomp k.MA.n k.MA.mu k.MA.r2 a b_bits b output


inline_for_extraction noextract
let bn_mod_inv_prime_ctx_st (t:limb_t) (len:BN.meta_len t) =
    ctx:MA.pbn_mont_ctx t
  -> output:lbignum t len
  -> a:lbignum t len ->
  Stack unit
  (requires fun h ->
    (B.deref h ctx).MA.len == len /\
    MA.pbn_mont_ctx_inv h ctx /\
    0 < bn_v h a /\ bn_v h a < MA.bn_v_n h ctx /\
    FStar.Math.Euclid.is_prime (MA.bn_v_n h ctx) /\

    live h a /\ live h output /\ disjoint output a /\
    B.(loc_disjoint (MA.footprint h ctx) (loc_buffer (a <: buffer (limb t)))) /\
    B.(loc_disjoint (MA.footprint h ctx) (loc_buffer (output <: buffer (limb t)))))
  (ensures  fun h0 r h1 -> modifies (loc output) h0 h1 /\
    bn_v h1 output * bn_v h0 a % MA.bn_v_n h0 ctx = 1)


inline_for_extraction noextract
val mk_bn_mod_inv_prime_ctx:
    #t:limb_t
  -> len:Ghost.erased _
  -> bn_mod_inv_precomp:BI.bn_mod_inv_prime_precomp_st t len ->
  bn_mod_inv_prime_ctx_st t len

let mk_bn_mod_inv_prime_ctx #t len bn_mod_inv_precomp ctx output a =
  let open LowStar.BufferOps in
  let k = !*ctx in
  bn_mod_inv_precomp k.MA.n k.MA.mu k.MA.r2 a output
