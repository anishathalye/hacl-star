module Hacl.Impl.EC.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECC
open Spec.ECDSA
open Hacl.Spec.EC.Definition
open Spec.DH
open Hacl.EC.Lemmas

open Hacl.Impl.EC.LowLevel 
open Hacl.Impl.EC.Core
open Hacl.Impl.P256.Signature.Common

open Hacl.Impl.EC.Intro


#set-options " --z3rlimit 300 --max_fuel 0 --max_ifuel 0"

open FStar.Mul 
inline_for_extraction noextract
val ecp256_dh_i_: #c: curve -> #l: ladder -> resultBuffer: point c 
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) 
  -> scalar: scalar_t #MUT #c -> result: pointAffine8 c -> 
  Stack bool
  (requires fun h -> live h resultBuffer /\ live h tempBuffer /\ live h scalar /\ live h result /\
    disjoint resultBuffer result /\
    scalar_as_nat (as_seq h scalar) < getOrder #c /\
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc scalar; loc resultBuffer])
  (ensures fun h0 success h1 -> modifies (loc result |+| loc tempBuffer |+| loc resultBuffer) h0 h1 /\ (
    let rX = nat_from_bytes_be (as_seq h1 (getXAff8 #c result)) in 
    let rY = nat_from_bytes_be (as_seq h1 (getYAff8 #c result)) in
    let p, flag = ecp256_dh_i #c (as_seq h0 scalar) in 
    rX < getPrime c /\ rX < getPrime c /\ flag == success /\ (
    success ==> 
      (rX, rY) == p /\ 
      ~ (isPointAtInfinity (secret_to_public (as_seq h0 scalar))) /\ 
      (rX, rY) == fromJacobianCoordinatesTest #c (_norm (secret_to_public (as_seq h0 scalar)))) /\
    (not success ==> isPointAtInfinity (secret_to_public (as_seq h0 scalar)))))


let ecp256_dh_i_ #c #l resultBuffer tempBuffer scalar result = 
    let h0 = ST.get() in 
  secretToPublic #c #l resultBuffer scalar tempBuffer;
    let h1 = ST.get() in 
  let r = isPointAtInfinityPrivate #c resultBuffer in 
    let h2 = ST.get() in 
  fromFormPoint #c resultBuffer result;
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h1 h2 resultBuffer;
  let open Hacl.Impl.EC.LowLevel.RawCmp in 
  unsafe_bool_of_u64 r


let ecp256dh_i c l result scalar =
  push_frame();
  let len = getCoordinateLenU64 c in 
  let tempBuffer = create (size 20 *! len) (u64 0) in
  let resultBuffer = create (size 3 *! len) (u64 0) in
  let flag = ecp256_dh_i_ #c #l resultBuffer tempBuffer scalar result in 
  pop_frame();
  flag


[@ (Comment "  This code is not side channel resistant on pubKey")]
inline_for_extraction noextract
val _ecp256dh_r_public: #c: curve 
  -> #l: ladder 
  -> result: point c
  -> pubKey: point c
  -> scalar: scalar_t #MUT #c -> 
  Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ 
     LowStar.Monotonic.Buffer.all_disjoint [loc pubKey;  loc scalar; loc result] /\ (
    let pk = as_nat c h (getX pubKey), as_nat c h (getY pubKey), as_nat c h (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian pk) /\ as_nat c h (getZ pubKey) == 1 /\
    scalar_as_nat (as_seq h scalar) < getOrder #c /\
    as_nat c h (getX result) == 0 /\ as_nat c h (getY result) == 0 /\ as_nat c h (getZ result) == 0))
  (ensures fun h0 r h1 -> modifies (loc result |+| loc pubKey) h0 h1 /\ point_eval c h1 result /\ (
    let pk = as_nat c h0 (getX pubKey), as_nat c h0 (getY pubKey), as_nat c h0 (getZ pubKey) in 
    let x3, y3, z3 = point_as_nat c h1 result in
    if not (verifyQValidCurvePointSpec #c pk) then
      r = false /\ x3 == 0 /\ y3 == 0
    else begin
      let pk_scalar = scalar_multiplication #c (as_seq h0 scalar) pk in
      if isPointAtInfinity #Jacobian pk_scalar then
	r == false
      else
	r == true /\ (x3, y3, z3) == fromJacobianCoordinates #c pk_scalar
      end))


let _ecp256dh_r_public #c #l result pubKey scalar =
    let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create (size 20 *! len) (u64 0) in
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_getZ_noChangeInState c h0 h1 pubKey;
  let publicKeyCorrect = verifyQValidCurvePoint_public #c #l pubKey tempBuffer in 
  if publicKeyCorrect then
    begin
      let h2 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 pubKey;
      scalarMultiplication #c #MUT #l pubKey result scalar tempBuffer; 

      let h3 = ST.get() in 
	let flag = isPointAtInfinityPrivate #c result in 
	pop_frame();
	  let h4 = ST.get() in 
	  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h3 h4 result;
	let open Hacl.Impl.EC.LowLevel.RawCmp in 
	unsafe_bool_of_u64 flag
    end
  else
    begin
      pop_frame();
	let h2 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 result;
      false
    end


inline_for_extraction noextract
val _ecp256dh_r_private: #c: curve 
  -> #l: ladder 
  -> result: point c
  -> pubKey: point c
  -> scalar: scalar_t #MUT #c -> 
  Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ 
     LowStar.Monotonic.Buffer.all_disjoint [loc pubKey;  loc scalar; loc result] /\ (
    let pk = as_nat c h (getX pubKey), as_nat c h (getY pubKey), as_nat c h (getZ pubKey) in 
    ~ (isPointAtInfinity #Jacobian pk) /\ as_nat c h (getZ pubKey) == 1 /\
    scalar_as_nat (as_seq h scalar) < getOrder #c /\
    as_nat c h (getX result) == 0 /\ as_nat c h (getY result) == 0 /\ as_nat c h (getZ result) == 0))
  (ensures fun h0 r h1 -> modifies (loc result |+| loc pubKey) h0 h1 /\ point_eval c h1 result /\ (
    let pk = as_nat c h0 (getX pubKey), as_nat c h0 (getY pubKey), as_nat c h0 (getZ pubKey) in 
    let x3, y3, z3 = point_as_nat c h1 result in
    if not (verifyQValidCurvePointSpec #c pk) then
      r = false /\ x3 == 0 /\ y3 == 0
    else begin
      let pk_scalar = scalar_multiplication #c (as_seq h0 scalar) pk in
      if isPointAtInfinity #Jacobian pk_scalar then
	r == false
      else
	r == true /\ (x3, y3, z3) == fromJacobianCoordinates #c pk_scalar
      end))


let _ecp256dh_r_private #c #l result pubKey scalar =
    let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let tempBuffer = create (size 20 *! len) (u64 0) in
    let h1 = ST.get() in 
    Hacl.Impl.P.PointAdd.Aux.lemma_getZ_noChangeInState c h0 h1 pubKey;
  let publicKeyCorrect = verifyQValidCurvePoint_private #c #l pubKey tempBuffer in 
  if publicKeyCorrect then
    begin
        let h2 = ST.get() in 
	Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 pubKey;
	scalarMultiplication #c #MUT #l pubKey result scalar tempBuffer; 
	  let h3 = ST.get() in 
	let flag = isPointAtInfinityPrivate #c result in 
	pop_frame();
	  let h4 = ST.get() in 
	  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h3 h4 result;
	let open Hacl.Impl.EC.LowLevel.RawCmp in 
	unsafe_bool_of_u64 flag
    end
  else
    begin
      pop_frame();
	let h2 = ST.get() in 
      Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h2 result;
      false
    end


let lemma_zero_point_zero_coordinates c h p = 
  let yz = gsub p (getCoordinateLenU64 c) (size 2 *! getCoordinateLenU64 c) in 
  lemma_test (as_seq h p) (v (getCoordinateLenU64 c));
  lemma_test (as_seq h yz) (v (getCoordinateLenU64 c));
  Hacl.Impl.P.PointAdd.Aux.lemma_point_eval_if_zero c p h


inline_for_extraction noextract
val ecp256_dh_r_public_: #c: curve -> #l: ladder -> result: pointAffine8 c 
  -> pubKey: pointAffine8 c 
  -> scalar: scalar_t #MUT #c
  -> pkF: point c
  -> rF: point c ->
  Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ live h pkF /\ live h rF /\
    disjoint pubKey pkF /\ point_eval c h rF /\ disjoint rF result /\
    LowStar.Monotonic.Buffer.all_disjoint [loc rF; loc pkF; loc scalar] /\
    scalar_as_nat (as_seq h scalar) < getOrder #c /\ (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h (getXAff8 pubKey)) in
    let pointScalarYSeq = nat_from_bytes_be (as_seq h (getYAff8 pubKey)) in 
      pointScalarXSeq <> 0 /\  pointScalarYSeq <> 0) /\
    as_nat c h (getX rF) == 0 /\ as_nat c h (getY rF) == 0 /\ as_nat c h (getZ rF) == 0)
  (ensures fun h0 success h1 -> modifies (loc result |+| loc pkF |+| loc rF) h0 h1 /\ (
    let pk = nat_from_bytes_be (as_seq h0 (getXAff8 pubKey)), nat_from_bytes_be (as_seq h0 (getYAff8 pubKey)) in 
    let coordinateX = nat_from_bytes_be (as_seq h1 (getXAff8 #c result)) in 
    let coordinateY = nat_from_bytes_be (as_seq h1 (getYAff8 #c result)) in
    coordinateX < getPrime c /\ coordinateY < getPrime c /\ (
    let p, flag = ecp256_dh_r pk (as_seq h0 scalar) in 
    flag == success /\ 
    success ==> (coordinateX, coordinateY) == p)))


let ecp256_dh_r_public_ #c #l result pubKey scalar pkF rF = 
    let h0 = ST.get() in 
  toFormPoint pubKey pkF; 
    let h1 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 rF; 
  let flag = _ecp256dh_r_public #c #l rF pkF scalar in 
  fromFormPoint rF result; 
  flag


inline_for_extraction noextract
val ecp256_dh_r_private_: #c: curve -> #l: ladder -> result: pointAffine8 c 
  -> pubKey: pointAffine8 c 
  -> scalar: scalar_t #MUT #c
  -> pkF: point c
  -> rF: point c ->
  Stack bool
  (requires fun h -> live h result /\ live h pubKey /\ live h scalar /\ live h pkF /\ live h rF /\
    disjoint pubKey pkF /\ point_eval c h rF /\ disjoint rF result /\
     (
    let pointScalarXSeq = nat_from_bytes_be (as_seq h (getXAff8 pubKey)) in
    let pointScalarYSeq = nat_from_bytes_be (as_seq h (getYAff8 pubKey)) in 
      pointScalarXSeq <> 0 /\  pointScalarYSeq <> 0)  /\
    LowStar.Monotonic.Buffer.all_disjoint [loc rF; loc pkF; loc scalar] /\
        scalar_as_nat (as_seq h scalar) < getOrder #c /\
    as_nat c h (getX rF) == 0 /\ as_nat c h (getY rF) == 0 /\ as_nat c h (getZ rF) == 0)
  (ensures fun h0 success h1 -> modifies (loc result |+| loc pkF |+| loc rF) h0 h1 /\ (
    let pk = nat_from_bytes_be (as_seq h0 (getXAff8 pubKey)), nat_from_bytes_be (as_seq h0 (getYAff8 pubKey)) in 
    let coordinateX = nat_from_bytes_be (as_seq h1 (getXAff8 #c result)) in 
    let coordinateY = nat_from_bytes_be (as_seq h1 (getYAff8 #c result)) in
    coordinateX < getPrime c /\ coordinateY < getPrime c /\ (
    let p, flag = ecp256_dh_r pk (as_seq h0 scalar) in 
    flag == success /\ 
    success ==> (coordinateX, coordinateY) == p)))

let ecp256_dh_r_private_ #c #l result pubKey scalar pkF rF = 
    let h0 = ST.get() in 
  toFormPoint pubKey pkF; 
    let h1 = ST.get() in 
  Hacl.Impl.P.PointAdd.Aux.lemma_coord_eval c h0 h1 rF; 
  let flag = _ecp256dh_r_public #c #l rF pkF scalar in 
  fromFormPoint rF result; 
  flag


let ecp256dh_r_public #c #l result pubKey scalar =
  let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 

    let rF = create (size 3 *! len) (u64 0) in
    let pkF = create (size 3 *! len) (u64 0) in
    let h1 = ST.get() in 

    lemma_create_zero_buffer #U64 (3 * v len) c;
    lemma_zero_point_zero_coordinates c h1 rF;
  let flag = ecp256_dh_r_public_ #c #l result pubKey scalar pkF rF in 

  pop_frame();
  flag


let ecp256dh_r_private #c #l result pubKey scalar =
  let h0 = ST.get() in 
  push_frame();
    let len = getCoordinateLenU64 c in 

    let rF = create (size 3 *! len) (u64 0) in
    let pkF = create (size 3 *! len) (u64 0) in
    let h1 = ST.get() in 

    lemma_create_zero_buffer #U64 (3 * v len) c;
    lemma_zero_point_zero_coordinates c h1 rF;
  let flag = ecp256_dh_r_private_ #c #l result pubKey scalar pkF rF in 

  pop_frame();
  flag