module VeriCrypt.LowStar.Basic

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
 * A simple function that allocates a buffer on stack and operates on it
 *)
 
let test1 (_:unit)
  : Stack unit
      (requires fun _ -> True)
      (ensures fun h0 _ h1 -> B.(modifies0 h0 h1))
  = push_frame ();
    let b = B.create 2ul 0ul in
    let x = B.index b 0ul in
    assert (x == 0ul);
    B.upd b 0ul 1ul;
    let x = B.index b 0ul in
    assert (x == 1ul);
    pop_frame ()

let eq_buffer (len:u32) (b1 b2:B.lbuffer u32 len)
  : Stack bool
      (requires fun h ->
        B.live h b1 /\
        B.live h b2)
      (ensures fun h0 b h1 ->
        h0 == h1 /\
        (b ==> Seq.equal (B.as_seq h1 b1) (B.as_seq h1 b2)))
  = let h0 = ST.get () in
    let _, b =
      C.interruptible_for 0ul len
        (fun h i b ->
         h == h0     /\
         B.live h b1 /\
         B.live h b2 /\
         i <= v len /\
         (not b ==> (forall (j:nat). j < i ==> Seq.index (B.as_seq h b1) j == Seq.index (B.as_seq h b2) j)))
        (fun i ->
         let x1 = B.index b1 i in
         let x2 = B.index b2 i in
         x1 <> x2) in
     not b
