module StackClientBad

open Stack

let some_function_bad (s:stack) = if s = [] then ...  (* ERROR *)
