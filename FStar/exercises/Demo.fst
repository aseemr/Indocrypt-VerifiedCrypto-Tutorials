module Demo

open FStar.Mul

(*
 * Try writing other types for incr
 *)

val incr : nat -> nat
let incr x = x + 1


let rec factorial (n:nat) : nat =
  if n = 0
  then 1
  else n * factorial (n - 1)

[@@ expect_failure]
let rec factorial_int (n:int) : int =
  if n = 0
  then 1
  else n * factorial_int (n - 1)

let rec length (#a:Type) (l:list a) : nat =
  match l with
  | []   -> 0
  | _::tl -> 1 + length tl

(*
 * Could write a decreases clause `length l1` here, though unnecessary
 *)
 
let rec append_intrinsic (#a:Type) (l1 l2:list a)
  : Tot (m:list a{length m == length l1 + length l2})
  = match l1 with
    | [] -> l2
    | hd::tl -> hd::(append_intrinsic tl l2)

let rec ackermann (m n:nat) : Tot nat (decreases %[m; n]) =
  if m=0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))
