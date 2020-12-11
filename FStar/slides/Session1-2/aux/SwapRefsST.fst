module SwapRefsST

open FStar.Ref

// BEGIN: swap
val swap : r1:ref int -> r2:ref int -> ST unit
    (requires (fun h0 -> True))
    (ensures (fun h0 _ h3 -> modifies !{r1,r2} h0 h3 /\
                             sel h3 r2 == sel h0 r1 /\ sel h3 r1 == sel h0 r2))
let swap r1 r2 =
  let t = !r1 in
    (* Know (P1): exists h1 t. modifies !{} h0 h1 /\ t == sel h0 r1 *)
  r1 := !r2;
    (* Know (P2): exists h2. modifies !{r1} h1 h2 /\ sel h2 r1 == sel h1 r2 *)
  r2 := t
    (* Know (P3): modifies !{r2} h2 h3 /\ sel h3 r2 == t *)
// END: swap

// BEGIN: swap_proof
(* `modifies !{r1,r2} h0 h3` follows directly from transitivity of modifies *)

(* `sel h3 r2 == sel h0 r1` follows immediately from (P1) and (P3) *)

(* Still to show: `sel h3 r1 == sel h0 r2`
   From (P2) we know that  `sel h2 r1 == sel h1 r2` (A)
   From (P1) we know that  modifies !{} h0 h1
     which by definition gives us  sel h1 r2 == sel h0 r2 (B)
   From (P3) we know that  modifies !{r2} h2 h3
     which by definition gives us  sel h2 r1 == sel h3 r1 (C)
   We conclude by transitivity from (A)+(B)+(C) *)
// END: swap_proof
