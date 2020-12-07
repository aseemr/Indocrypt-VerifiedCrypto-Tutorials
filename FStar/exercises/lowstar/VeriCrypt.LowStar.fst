module VeriCrypt.LowStar

open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST

module Seq = Lib.Sequence
module B = Lib.Buffer

open Lib.IntTypes

module C = C.Loops

#set-options "--fuel 0 --ifuel 0"

type u32 = pub_uint32

(*
 * Exercise: Implement the functions below.
 *
 * The min function computes the index i that contains the
 *   minimum element in the input buffer b
 *
 * The copy function copies contents of b2 to b1
 *
 * You can use loop combinators in C.Loops to implement these
 *
 * Once you have the implementation, make sure that your code
 *   is valid Low* and compiles to C
 *
 * To do so, you can run `make -j N` (where N is the degree of
 *   parallelism you want)
 *
 * in the current directory (lowstar/) and it should build
 *   a libvericrypt.a in the lowstar/dist directory
 *
 * To see the extracted C code, see lowstar/VeriCrypt_LowStar.c
 *)

let min (len:u32) (b:B.lbuffer u32 len)
  : Stack u32
      (requires fun h -> B.live h b /\ v len > 0)
      (ensures fun h0 i h1 ->
        B.modifies0 h0 h1 /\
        v i < v len /\
        (forall (k:u32). v k < v len ==>
                    v (B.bget h1 b (v i)) <= v (B.bget h1 b (v k))))
  = admit ()

let copy (len:u32) (b1 b2:B.lbuffer u32 len)
  : Stack unit
      (requires fun h ->
        B.live h b1 /\
        B.live h b2 /\
        B.disjoint b1 b2)
      (ensures fun h0 _ h1 ->
        Seq.equal (B.as_seq h1 b1) (B.as_seq h1 b2) /\
        B.modifies1 b1 h0 h1)
  = admit ()
