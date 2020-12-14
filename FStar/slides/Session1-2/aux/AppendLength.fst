module AppendLength

open FStar.List.Tot.Base

// BEGIN: append
let rec append (#a:Type) (xs ys : list a) : Tot (list a) =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys
// END: append

// BEGIN: append_length
let rec append_length (#a:Type) (xs ys : list a) :
    Pure unit
      (requires True)
      (ensures (fun _ -> length (append xs ys) = length xs + length ys))
= match xs with
  | [] -> ()  (* length (append [] ys) = length [] + length ys *)
  | x :: xs' ->
    append_length xs' ys
    (* Know recursive call's postcondition: length (append xs' ys) = length xs' + length ys *)
    (* To show: length (append (x::xs') ys) = length (x::xs') + length ys *)
    (* i.e. length (x::(append xs' ys)) = 1 + length xs' + length ys *)
    (* i.e. 1 + length (append xs' ys) = 1 + length xs' + length ys *)
// END: append_length

// BEGIN: append_length_lemma
let rec append_length_lemma (#a:Type) (xs ys : list a) :
    Lemma (ensures (length (append xs ys) = length xs + length ys))
= match xs with
  | [] -> ()
  | x :: xs' -> append_length_lemma xs' ys
// END: append_length_lemma

(*
Base case:
length (append [] ys) = length [] + length ys
length ys = 0 + length ys  -- trivial

Inductive case:
  IH: length (append xs' ys) = length xs' + length ys

  TS: length (append (x::xs') ys) = length (x::xs') + length ys
      length (x :: (append xs' ys)) = 1 + length xs' + length ys
      1 + length (append xs' ys) = 1 + length xs' + length ys
*)
