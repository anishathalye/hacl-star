module Hacl.Impl.Sparkle1

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.ByteBuffer
open Lib.Buffer

open Spec.SPARKLE2


#set-options " --z3rlimit 200 --ifuel 0 --fuel 0"


inline_for_extraction
let vsize_rcon: size_t = 8ul


let rcon: x: glbuffer uint32 vsize_rcon 
  {witnessed #uint32 #vsize_rcon x (Lib.Sequence.of_list rcon_list) /\ recallable x} =
  createL_global rcon_list


type branch_len =  n: size_t {v n = 4 \/ v n = 6 \/ v n = 8}

inline_for_extraction noextract
type branch branch_len = lbuffer uint32 (2ul *! branch_len)


inline_for_extraction noextract
val getBranch: #n: branch_len -> b: branch n -> i: size_t{v i < v n} -> 
  Stack (tuple2 uint32 uint32)
  (requires fun h -> live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec.SPARKLE2.getBranch #(v n) (v i) (as_seq h0 b))

let getBranch #l b i =  
  Lib.Buffer.index b (2ul *! i), Lib.Buffer.index b (2ul *! i +! 1ul)


inline_for_extraction noextract 
val setBranch: #n: branch_len -> i: size_t {v i < v n} -> b0: branch1 -> b: branch n -> 
  Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ 
    as_seq h1 b == Spec.SPARKLE2.setBranch #(v n) (v i) b0 (as_seq h0 b))

let setBranch #n i (x, y) b =
  upd #uint32 b (2ul *! i) x; upd #uint32 b (2ul *! i +! 1ul) y


inline_for_extraction noextract
val xor_step: #l: branch_len -> b: branch l
  -> tx: lbuffer uint32 (size 1) 
  -> ty: lbuffer uint32 (size 1) 
  -> i: size_t {v i <= v l / 2} ->
  Stack unit
  (requires fun h -> live h b /\ live h tx /\ live h ty /\ disjoint tx ty)
  (ensures fun h0 _ h1 -> modifies (loc tx |+| loc ty) h0 h1 /\ (
    let tx_0 = Lib.Sequence.index (as_seq h0 tx) 0 in 
    let ty_0 = Lib.Sequence.index (as_seq h0 ty) 0 in 
    let tx_1: uint32 = Lib.Sequence.index (as_seq h1 tx) 0 in 
    let ty_1: uint32 = Lib.Sequence.index (as_seq h1 ty) 0 in  
    (tx_1, ty_1) == Spec.SPARKLE2.xor_step #(v l) (as_seq h0 b) (v i) (tx_0, ty_0)))

let xor_step #l b tx ty i = 
  let xi, yi = getBranch b i in 
  let tx_0 = index tx (size 0) in 
  let ty_0 = index ty (size 0) in 
  upd tx (size 0) (xi ^. tx_0);
  upd ty (size 0) (yi ^. ty_0)


inline_for_extraction
val xor: #l: branch_len -> b: branch l -> Stack (tuple2 uint32 uint32)
    (requires fun h -> live h b)
    (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r == Spec.SPARKLE2.xor #(v l) (as_seq h0 b))

let xor #l b = 
  push_frame();
    let tx = create (size 1) (u32 0) in 
    let ty = create (size 1) (u32 0) in 
  let h0 = ST.get() in 
  let inv h (i: nat {i <= v l / 2})  = live h b /\ live h ty /\ live h tx /\ 
    disjoint tx ty /\ disjoint tx b /\ disjoint ty b /\
    modifies (loc tx |+| loc ty) h0 h /\ (
      let tx_0 = Lib.Sequence.index (as_seq h0 tx) 0 in 
      let ty_0 = Lib.Sequence.index (as_seq h0 ty) 0 in 
      let tx_1: uint32 = Lib.Sequence.index (as_seq h tx) 0 in 
      let ty_1: uint32 = Lib.Sequence.index (as_seq h ty) 0 in  
      (tx_1, ty_1) == 
	Lib.LoopCombinators.repeati #(tuple2 uint32 uint32) i (Spec.SPARKLE2.xor_step #(v l) (as_seq h0 b)) (tx_0, ty_0)) in 
  Lib.LoopCombinators.eq_repeati0 (v l / 2 + 1) (Spec.SPARKLE2.xor_step #(v l) (as_seq h0 b)) (
    Lib.Sequence.index (as_seq h0 tx) 0, Lib.Sequence.index (as_seq h0 ty) 0);
    
  Lib.Loops.for 0ul (l >>. 1ul) inv
    (fun (i: size_t {v i < v l / 2}) -> 
      xor_step b tx ty i;
      let f = Spec.SPARKLE2.xor_step #(v l) (as_seq h0 b) in 
      
      let tx_0 = Lib.Sequence.index (as_seq h0 tx) 0 in 
      let ty_0 = Lib.Sequence.index (as_seq h0 ty) 0 in 
      Lib.LoopCombinators.unfold_repeati (v l / 2 + 1) f (tx_0, ty_0) (v i));
  let r0, r1 = index tx (size 0), index ty (size 0) in 
  pop_frame();
  r0, r1

open FStar.Mul


inline_for_extraction noextract
val xor_x_step: #n: branch_len -> b: branch n -> lty: uint32 -> ltx: uint32 -> i: size_t {v i < v n}
  -> temp: branch n ->
  Stack unit 
  (requires fun h -> live h b /\ live h temp)
  (ensures fun h0 _ h1 -> modifies (loc temp) h0 h1 /\ (
    as_seq h1 temp == xor_x_step #(v n) (lty, ltx) (as_seq h0 b) (v i) (as_seq h0 temp)))

let xor_x_step #n b lty ltx i temp = 
  let xi, yi = getBranch b i in 
  let xi_n = xi ^. lty in
  let yi_n = yi ^. ltx in
  setBranch i (xi_n, yi_n) temp


val xor_x: #n: branch_len -> b: branch n -> lty: uint32 -> ltx: uint32 -> temp: branch n -> Stack unit 
  (requires fun h -> live h b /\ live h temp /\ disjoint temp b)
  (ensures fun h0 _ h1 -> modifies (loc temp) h0 h1 /\ (
    as_seq h1 temp == xor_x #(v n) (as_seq h0 b) (lty, ltx) (as_seq h0 temp)))

let xor_x #n b lty ltx temp = 
  let h0 = ST.get() in 

  Lib.LoopCombinators.eq_repeati0 (v n / 2) (
    (Spec.SPARKLE2.xor_x_step #(v n) (lty, ltx) (as_seq h0 b))) (as_seq h0 temp);
 
  let inv h (i: nat {i >= 0 /\ i <= v n / 2})  = live h b /\ modifies (loc temp) h0 h /\ (
    let f = Spec.SPARKLE2.xor_x_step #(v n) (lty, ltx) (as_seq h0 b) in 
    let temp0 = as_seq h0 temp in
    as_seq h temp == Lib.LoopCombinators.repeati i f temp0) in   

  Lib.Loops.for 0ul (n >>. 1ul) inv (fun (i: size_t {v i < v n / 2}) -> 
    xor_x_step b lty ltx i temp;
    
    let f = Spec.SPARKLE2.xor_x_step #(v n) (lty, ltx) (as_seq h0 b) in
    let temp0 = as_seq h0 temp in
    Lib.LoopCombinators.unfold_repeati (v n) f temp0 (v i)
  )


inline_for_extraction noextract
val m: #n: branch_len -> b: branch n -> temp: branch n -> Stack unit 
  (requires fun h -> live h b /\ live h temp /\ disjoint temp b)
  (ensures fun h0 _ h1 -> modifies (loc temp) h0 h1 /\ as_seq h1 temp == Spec.SPARKLE2.m #(v n) (as_seq h0 b) (as_seq h0 temp))

let m #n b temp  = 
  let ltx, lty = xor #n b  in 
  xor_x #n b (l1 lty) (l1 ltx) temp


inline_for_extraction
val l_step: #n: branch_len -> m: branch n -> i: size_t {v i < v n} -> right: branch n -> Stack unit 
  (requires fun h -> live h m /\ live h right)
  (ensures fun h0 _ h1 -> modifies (loc m) h0 h1 /\ 
    as_seq h1 m == Spec.SPARKLE2.l_step #(v n) (as_seq h0 m) (as_seq h0 right) (v i))

let l_step #n m i right = 
  let xi, yi = getBranch right i in 
  let p0i, p1i = getBranch m i in 
  let branchIUpd = xi ^. p0i, yi ^. p1i in
  setBranch #n i branchIUpd m


val l: #n: branch_len -> b: branch n -> Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

let l #n b = 
  admit(); 
  let h0 = ST.get() in 
  push_frame(); 
    let result = create (size 2 *. n) (u32 0) in 
    let leftBranch = sub b (size 0) n in 
    let rightBranch = sub b n n in
 
  m #n b result;
  
  Lib.Loops.for 0ul (n >>. 1ul) 
    (fun h i -> live h b /\ modifies (loc b) h0 h)
    (fun (i: size_t {v i < v n}) -> l_step #n result i rightBranch); 

  Lib.Loops.for 0ul (n >>. 1ul)
    (fun h i -> live h b /\ modifies (loc b) h0 h)
    (fun (i: size_t {v i <= v n}) -> setBranch #n i (getBranch #n leftBranch i) rightBranch);

  Lib.Loops.for 0ul (n >>. 1ul)
    (fun h i -> live h b /\ modifies (loc b) h0 h)
    (fun (i: size_t {v i <= v n}) -> 
        let index = Lib.RawIntTypes.size_to_UInt32 (i -. 1ul) in 
        let k =  Lib.RawIntTypes.size_to_UInt32 (n >>. 1ul) in 
        let j = FStar.UInt32.rem index k in 
        setBranch #n j (getBranch #n result i) leftBranch);
  pop_frame()
  

val add2: #n: branch_len -> i: size_t -> b:branch n -> Stack unit 
  (requires fun h -> live h b) 
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_seq h1 b == Spec.SPARKLE2.add2 #(v n) (v i) (as_seq h0 b))

let add2 #n i b = 
  recall_contents rcon (Lib.Sequence.of_list rcon_list); 

  let (x0, y0) = getBranch #n b (size 0) in 
  let (x1, y1) = getBranch #n b (size 1) in 

  let i0 = logand i (size 7) in 
    logand_mask i (size 7) 3; 
  let y0 = y0 ^. index rcon i0 in
  let y1 = y1 ^. (to_u32 i) in
 
  setBranch (size 0) (x0, y0) b;
  setBranch #n (size 1) (x1, y1) b


val toBranch: #n: branch_len -> i: lbuffer uint8 (size 8 *! n) -> o: branch n -> 
  Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_seq h1 o == Spec.SPARKLE2.toBranch #(v n) (as_seq h0 i))

let toBranch #n i o = 
  uints_from_bytes_le o i 


val fromBranch: #n: branch_len -> i: branch n -> o: lbuffer uint8 (size 8 *! n) -> 
  Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ as_seq h1 o == Spec.SPARKLE2.fromBranch #(v n) (as_seq h0 i))

let fromBranch #n i o = 
  uints_to_bytes_le (2ul *! n) o i


val arx_n_step: #n: branch_len -> i: size_t {v i < v n} -> b: branch n -> 
  Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_seq h1 b == Spec.SPARKLE2.arx_n_step #(v n) (v i) (as_seq h0 b))

let arx_n_step #n i b = 
  let branchI = getBranch b i in  
    recall_contents rcon (Lib.Sequence.of_list rcon_list); 
  let rcon_i = index rcon i in 
  let x, y = arx rcon_i branchI in 
  setBranch i (x, y) b
  

inline_for_extraction noextract
val arx_n: #n: branch_len -> b: branch n -> 
  Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_seq h1 b == Spec.SPARKLE2.arx_n #(v n) (as_seq h0 b)) 

let arx_n #n b =
  let h0 = ST.get() in 
  Lib.LoopCombinators.eq_repeati0 (v n) (Spec.SPARKLE2.arx_n_step #(v n)) (as_seq h0 b);

  Lib.Loops.for 0ul n 
    (fun h i -> live h b /\ modifies (loc b) h0 h /\ as_seq h b == Lib.LoopCombinators.repeati i (Spec.SPARKLE2.arx_n_step #(v n)) (as_seq h0 b))
    (fun (i: size_t {v i < v n}) -> arx_n_step i b;
      Lib.LoopCombinators.unfold_repeati (v n) (Spec.SPARKLE2.arx_n_step #(v n)) (as_seq h0 b) (v i))


inline_for_extraction noextract
val mainLoop_step: #n: branch_len -> i: size_t -> b: branch n ->
  Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_seq h1 b == Spec.SPARKLE2.mainLoop_step #(v n) (v i) (as_seq h0 b))

let mainLoop_step #n i b = 
  add2 i b;
  arx_n #n b;
  l #n b


inline_for_extraction noextract
val mainLoop: #n: branch_len -> b: branch n -> steps: size_t -> 
  Stack unit 
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

let mainLoop #n b steps = 
  let h0 = ST.get() in 
  Lib.Loops.for 0ul steps
    (fun h i -> live h b /\ modifies (loc b) h0 h)
    (fun (i: size_t) -> mainLoop_step i b)


val sparkle256: steps: size_t -> i: lbuffer (uint8) (size 32) -> o: lbuffer (uint8) (size 32) ->
  Stack unit 
  (requires fun h -> live h i /\ live h o)
  (ensures fun h0 _ h1 -> True)

let sparkle256 steps i o =
  push_frame();
    let temp = create (size 12) (u32 0) in 
    toBranch #(size 4) i temp;
    mainLoop #(size 4) temp steps;
    fromBranch #(size 4) temp o; 
  pop_frame()
