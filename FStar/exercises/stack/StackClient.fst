module StackClient

open Stack

(*
 * Exercise: enhance the specs in Stack.fsti,
 *           and if required the implementation in Stack.fst,
 *           so that test function below verifies
 *)

let test () =
  let s0 = empty in
  assert (is_empty s0);

  let s1 = push s0 3 in
  assert (~(is_empty s1));

  let s2 = push s1 4 in
  assert (~(is_empty s2));

  let i = top s2 in
  assert (i == 4);

  let s3 = pop s2 in
  assert (s3 == s1);

  let s4 = pop s3 in
  assert (s4 == s0)
