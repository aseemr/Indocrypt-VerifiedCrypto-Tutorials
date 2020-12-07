require import Int.

module QCounter = {
   var q : int

   proc init() = { q <- 0; }

   proc count() =  { q <- q + 1; }

}.


