module Stack

val stack : Type0

val empty : stack

val is_empty (s:stack) : bool

val push (s:stack) (x:int) : stack

val pop (s:stack{~ (is_empty s)}) : stack

val top (s:stack{~ (is_empty s)}) : int
