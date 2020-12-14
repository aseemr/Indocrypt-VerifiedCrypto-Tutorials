require import AllCore Distr.
from Jasmin require import JModel.
require import Array11 AES_jazz  NbAESEnc_jazz AES_spec AES_proof NbPRFEnc QCounter.

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

type key = W128.t.
type plaintext = W128.t.
type nonce = W128.t.

(* W128.dword is the uniform distribution over word of size 128 bits *)
op dkey = W128.dword. 
op dplaintext = W128.dword.

clone import NbPRFEnc as RefinedScheme with
  type key <- W128.t,
  type nonce <- W128.t,  
  type plaintext <- W128.t,
  op   f   <- aes,
  op dkey <- dkey,
  op dplaintext <- dplaintext,
  op (^) <- W128.(+^)
  proof *.

realize dkey_ll by apply W128.dword_ll.
realize dplaintext_ll by apply W128.dword_ll.
realize dplaintext_uni by apply W128.dword_uni.
realize dplaintext_full by apply W128.dword_fu.
realize xor_idempotent1 by smt(@W128).
realize xor_idempotent2 by smt(@W128).

import RefinedScheme.
import PRFth.

(*
print Scheme.
print indcpa_security.
*)

(* Our library for AES includes a proof that extracted Jasmin code
   for the AES function (AES_jass.M, which calls the AES-NI instructions) is
   computing the aes operator that defines our reference AES 
   semantics. We first prove that our NbAESEncryption scheme is
   actually using the exact same Jasmin implementation, and
   derive as a corollary that M.aes computes the aes operator.  *)  
  
equiv aes_correct_E : 
  NbAESEnc_jazz.M.aes ~ AES_jazz.M.aes :
    ={arg} ==> ={res} by sim.

phoare aes_correct k n : [NbAESEnc_jazz.M.aes : arg = (k,n) ==> res  = aes k n] = 1%r.
proof. conseq aes_correct_E (aes_jazz k n) => /#. qed.

(* With the above results as helpers, we can prove that our
   Jasmin code is correct with respect to the specification.
   We do this in two steps: first we prove equivalence to
   the scheme and then we derive correctness with respect
   to the encryption operator. *)
equiv enc_correct_equiv : 
  NbAESEnc_jazz.M.enc ~ RefinedScheme.Scheme.enc :  ={arg} ==> ={res}.
proof.
proc.
inline M.xor; wp.
by ecall {1} (aes_correct k{1} n{1}).
qed.

(* Then we derive correctness as a corollary. *)
phoare enc_correct _k _n _p : 
 [ NbAESEnc_jazz.M.enc :
    arg = (_k,_n,_p) ==> res = enc _k _n _p ] = 1%r.
proof. 
  conseq (enc_correct_equiv) (correct_enc _k _n _p) => /#. 
qed.

(* We do the same for decryption *)
equiv dec_correct_equiv : 
  NbAESEnc_jazz.M.dec ~ RefinedScheme.Scheme.dec :  ={arg} ==> ={res}.
proof.
proc.
inline M.xor; wp.
by ecall {1} (aes_correct k{1} n{1}).
qed.

phoare dec_correct _k _n _c : 
 [ NbAESEnc_jazz.M.dec :
    arg = (_k,_n,_c) ==> res = dec _k _n _c ] = 1%r.
proof. 
  conseq (dec_correct_equiv) (correct_dec _k _n _c)  => /#. 
qed.

(* These results show each of our Jasmin procedures 
   are implemementing the encryption and decryption 
   operators correctly. But can we conclude that they
   constitute a correct and secure encryption scheme? *)

(* For that we need to put them together into the 
   Scheme syntax, assuming keys are generated as
   per the specification. *)

module ConcreteScheme = {
  include Scheme [ kg ]
  include M [enc, dec]
}.

(* Now  we can use the correctness of the implementation
   propagate specification correctness to implementation
   correctness. *)

lemma concrete_correctness &m (_k _n _p : W128.t):
    Pr[Correctness(ConcreteScheme).main(_k, _n, _p) @ &m : res] = 1%r.
proof.
rewrite (_: 1%r = Pr[Correctness(Scheme).main(_k, _n, _p) @ &m : res]); 
   first by rewrite -(correctness &m _k _n _p).
byequiv; last 2 by done.
proc.
by call (dec_correct_equiv); call (enc_correct_equiv).
qed.

section.

declare module A : AdvCPA{RF, Real_PRF, RealScheme, CPA, Real_Ideal}.

lemma concrete_indcpa_security &m q:
   (* Advantages match *)
  `| Pr[CPA(A,RealScheme(ConcreteScheme)).main() @ &m : res] - 
       Pr[CPA(A,IdealScheme).main() @ &m : res]| =
  `| Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : res] - 
       Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : res] | /\

   (* Same number of queries in real games *)
     Pr[CPA(A,RealScheme(ConcreteScheme)).main() @ &m : QCounter.q = q ] =
     Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : QCounter.q = q ] /\ 

   (* Same number of queries in ideal games *)
     Pr[CPA(A,IdealScheme).main() @ &m : QCounter.q = q ] =
     Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : QCounter.q = q ]
.
proof.

(* We will show that security for the specification implies
   security for the implementation. *)
move : (indcpa_security A &m q) => [#] adv countr counti.

do split.

(* We will use functional correctness to show that the adversary's
   output is the same when attacking the real scheme and the concrete
   scheme. Then we can simply apply the results above. *)

+ have -> : (Pr[CPA(A, RealScheme(ConcreteScheme)).main() @ &m : res] = 
            Pr[CPA(A, RealScheme(Scheme)).main() @ &m : res]); 
       last by apply adv.
  byequiv; last 2 by done.
  proc.
  call(_: ={RealScheme.k,WO.nonces}); last by inline *; auto => />.
  proc. 
  sp; if; 1,3: by auto.
  wp;call(_: ={RealScheme.k}); last by auto.
  call (enc_correct_equiv).
  by inline *; auto.

+ have -> : (Pr[CPA(A, RealScheme(ConcreteScheme)).main() @ &m : QCounter.q = q ] = 
            Pr[CPA(A, RealScheme(Scheme)).main() @ &m : QCounter.q = q ]); 
       last by apply countr.
  byequiv; last 2 by done.
  proc.
  call(_: ={RealScheme.k,WO.nonces,QCounter.q}); last by inline *; auto => />.
  proc. 
  sp; if; 1,3: by auto.
  wp;call(_: ={RealScheme.k,QCounter.q}); last by auto.
  call (enc_correct_equiv).
  by inline *; auto.

+ by apply counti.

qed.

end section.

