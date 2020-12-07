require import AllCore List.
from Jasmin require import JModel.
require import Array11 AES_jazz  NbAESEnc_mem_jazz AES_spec AES_proof NbPRFEnc.

(* We refine our nonce-based encryption scheme by creating our own
   local copy of the theory and instantiating the PRF types and
   algorithm with those of an AES operator that defines the semantics
   of aes in Jasmin. 

   In general there could be an abstraction gap between the types used 
   by the refined scheme that we proved secure (e.g., ZModP) and the
   Jasmin representation of values in those types (e.g., W128.t). 
   In this case, preconditions/post-conditions assume/require
   that the inputs/outputs to/of the Jasmin implementation are 
   correct representations of the refined scheme inputs/outputs.
   Here representation is just equality. *)

clone import NbPRFEnc as RefinedScheme with
  type key <- W128.t,
  op   f   <- aes,
  type nonce <- W128.t,  
  type plaintext <- W128.t,
  op (^) <- W128.(+^)
  proof xor_idempotent1 by smt(@W128)
  proof xor_idempotent2 by smt(@W128).
  (* proof * will reveal we inherit as unproven
     axioms the assumptions on distributions on
     W128.t keys and plaintexts *)

import RefinedScheme.
import PRFth.

(* TODO : move this in JMemory *)
lemma load_storeE_eq (mem : global_mem_t) (ptr : W64.t) (val : W128.t) :
  loadW128 (storeW128 mem (to_uint ptr) val) (to_uint ptr) = val.
proof.
  apply W16u8.wordP => i hi.
  rewrite loadW128_bits8 1:// storeW128E /loadW8 get_storesE W16u8.nth_to_list /#.
qed.

(* Our library for AES includes a proof that extracted Jasmin code
   for the AES function (AES_jass.M, which calls the AES-NI instructions) is
   computing the aes operator that defines our reference AES 
   semantics. We first prove that our NbAESEncryption scheme is
   actually using the exact same Jasmin implementation, and
   derive as a corollary that M.aes computes the aes operator.  *)  
  
equiv aes_correct_E : 
  M.aes ~ AES_jazz.M.aes :
    ={arg} ==> ={res} by sim.

phoare aes_correct k n : [M.aes : arg = (k,n) ==> res  = aes k n] = 1%r.
proof. conseq aes_correct_E (aes_jazz k n) => /#. qed.

(* With the above results as helpers, we can prove that our
   Jasmin code stores in the output memory the correct encryption
   of the message and key stored in the input memory.
   We first prove an equivalence modulo memory representation. *)
equiv enc_correct_equiv _k _n _p _cptr : 
  M.enc ~ Scheme.enc :
     arg{2} = (_k,_n,_p) /\
     _cptr  = to_uint cptr{1} /\
     _k = loadW128 Glob.mem{1} (to_uint kptr{1}) /\
     _n = loadW128 Glob.mem{1} (to_uint nptr{1}) /\
     _p = loadW128 Glob.mem{1} (to_uint pptr{1}) 
  ==>
     loadW128 Glob.mem{1} _cptr = res{2}.
proof.
proc.
inline M.xor; wp.
ecall {1} (aes_correct k{1} n{1}).
by auto => /> *; rewrite load_storeE_eq.
qed.

(* Then we derive correctness as a corollary. *)
phoare enc_correct _k _n _p _cptr : 
 [ M.enc :
     _cptr  = to_uint cptr /\
     _k = loadW128 Glob.mem (to_uint kptr) /\
     _n = loadW128 Glob.mem (to_uint nptr) /\
     _p = loadW128 Glob.mem (to_uint pptr) 
  ==>
     enc _k _n _p = loadW128 Glob.mem _cptr ] = 1%r.
proof. 
  conseq (enc_correct_equiv _k _n _p _cptr) (correct_enc _k _n _p) => /#. 
qed.

(* We do the same for decryption *)
equiv dec_correct_equiv _k _n _c _pptr:
  M.dec ~ Scheme.dec :
     arg{2} = (_k,_n,_c) /\
     _pptr  = to_uint pptr{1} /\
     _k = loadW128 Glob.mem{1} (to_uint kptr{1}) /\
     _n = loadW128 Glob.mem{1} (to_uint nptr{1}) /\
     _c = loadW128 Glob.mem{1} (to_uint cptr{1}) 
  ==>
     loadW128 Glob.mem{1} _pptr = res{2}.
proof.
proc.
inline M.xor;wp.
ecall {1} (aes_correct k{1} n{1}).
by auto => />;move => *; rewrite load_storeE_eq. 
qed.

phoare dec_correct _k _n _c _pptr : 
  [ M.dec :
     _pptr  = to_uint pptr /\
     _k = loadW128 Glob.mem (to_uint kptr) /\
     _n = loadW128 Glob.mem (to_uint nptr) /\
     _c = loadW128 Glob.mem (to_uint cptr) 
  ==>
     enc _k _n _c = loadW128 Glob.mem _pptr ] = 1%r.
proof.
  conseq (dec_correct_equiv _k _n _c _pptr) (correct_dec _k _n _c) => /#.
qed.

(* Here the data types used as inputs by encryption
   and decryption do not match those of Scheme.
   This means that we need to modify the IND$-CPA game
   in order to capture security of this implementation.
   Several technicalities arise because the scheme
   receives and returns values in memory: if the 
   attacker is allowed to choose the memory regions,
   then it must be restricted to avoid safety problems.
   However, the same principle applies: modulo memory
   safety, functional correctnes of implementation
   combined with IND$-CPA security of specification
   implies that implementation is also IND$-CPA secure. *)
