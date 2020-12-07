module Sum

open FStar.Mul

let rec sum_rec (n:nat) : nat =
  if n = 0 then 0
  else n + sum_rec (n - 1)

let sum (n:nat) : nat = (n * (n + 1)) / 2

(*
 * Exercise: remove the admit and complete the proof
 *)

let sum_rec_correct_lemma (n:nat)
  : Lemma (sum_rec n == sum n)
  = admit ()
