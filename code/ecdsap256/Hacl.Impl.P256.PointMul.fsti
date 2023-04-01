module Hacl.Impl.P256.PointMul

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Point

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module BSeq = Lib.ByteSequence


#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val point_mul: res:point -> p:point -> scalar:felem -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ live h scalar /\
    disjoint p res /\ disjoint scalar res /\ disjoint p scalar /\
    point_inv h p /\ as_nat h scalar < pow2 256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) ==
    S.point_mul (as_nat h0 scalar) (from_mont_point (as_point_nat h0 p)))


val point_mul_g: res:point -> scalar:felem -> Stack unit
  (requires fun h ->
    live h res /\ live h scalar /\ disjoint res scalar /\
    as_nat h scalar < pow2 256)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) == S.point_mul_g (as_nat h0 scalar))


val point_mul_bytes: res:aff_point -> p:point -> scalar:lbuffer uint8 32ul -> Stack uint64
  (requires fun h ->
    live h p /\ live h res /\ live h scalar /\
    disjoint p res /\ disjoint scalar res /\ disjoint p scalar /\
    point_inv h p)
  (ensures fun h0 r h1 -> modifies (loc res) h0 h1 /\
    aff_point_inv h1 res /\
   (let res_proj = S.point_mul (BSeq.nat_from_bytes_be (as_seq h0 scalar))
     (from_mont_point (as_point_nat h0 p)) in
    as_aff_point_nat h1 res == S.to_aff_point res_proj /\
   (if S.is_point_at_inf res_proj then v r = ones_v U64 else v r = 0)))


val point_mul_g_bytes: res:aff_point -> scalar:lbuffer uint8 32ul -> Stack uint64
  (requires fun h ->
    live h res /\ live h scalar /\ disjoint res scalar)
  (ensures fun h0 r h1 -> modifies (loc res) h0 h1 /\
    aff_point_inv h1 res /\
   (let res_proj = S.point_mul_g (BSeq.nat_from_bytes_be (as_seq h0 scalar)) in
    as_aff_point_nat h1 res == S.to_aff_point res_proj /\
   (if S.is_point_at_inf res_proj then v r = ones_v U64 else v r = 0)))


val point_mul_double_g: res:point -> scalar1:felem -> scalar2:felem -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h scalar1 /\ live h scalar2 /\ live h p /\
    disjoint res scalar1 /\ disjoint res scalar2 /\ disjoint res p /\
    disjoint p scalar1 /\ disjoint p scalar2 /\
    point_inv h p /\ as_nat h scalar1 < pow2 256 /\ as_nat h scalar2 < pow2 256)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) ==
      S.point_mul_double_g (as_nat h0 scalar1) (as_nat h0 scalar2)
      (from_mont_point (as_point_nat h0 p)))
