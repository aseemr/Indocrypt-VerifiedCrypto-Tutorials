require import AllCore SmtMap List Distr.
require import QCounter.
require (****) PRFth NbEnc.

theory NbPRFEnc.

(* Will work for arbitrary types *)
type nonce.
type plaintext.
type key.

(* These operators will replace the ones in the PRF theory,
   so our assumption will be based on this function and
   these distributions. *)
op f : key -> nonce -> plaintext.
op dkey : key distr.
op dplaintext : plaintext distr.

(* We bring to the top level the assumptions on the 
   distributions required by the theories we will clone. *)
axiom dkey_ll: is_lossless dkey.
axiom dplaintext_ll: is_lossless dplaintext.
axiom dplaintext_uni: is_uniform dplaintext.
axiom dplaintext_full: is_full dplaintext.

(* Cloning creates a sub-theory with definitions, 
   axioms and lemmas defined in the cloned theory.
   The <- notation forgets the original type names via
   substitution.
   Using = keeps original names and creates an alias. *)
clone import PRFth with
  type input <- nonce,
  type output <- plaintext,
  type key <- key,
  op f <- f,
  op doutput <- dplaintext,
  op dkey <- dkey
  (* renaming is purely syntactic on all occurrences! *)
  rename "doutput" as "dplaintext"
  (* if we do not prove axioms in original theory, they
     remain axioms, here we prove all of them under the
     top level axioms above for clarity. *)
  proof *.

realize dplaintext_ll by apply dplaintext_ll.
realize dplaintext_uni by apply dplaintext_uni.
realize dplaintext_full by apply dplaintext_full.
realize dkey_ll by apply dkey_ll.

(* We get the syntax and security definitions for nonce-based
   encryption by copying all the definitions in NbEnc with
   some renamings.
   The alternative = notation adds a type definition
   with an alias.
*)
clone include NbEnc with
  type key <- key,
  type nonce <- nonce,
  type plaintext <- plaintext,
  type ciphertext = plaintext,
  op dciphertext = dplaintext
  proof *.

(* Again we prove all axioms in the underlying theory
   using the top-level ones for clarity *)

realize dciphertext_ll by apply dplaintext_ll.
realize dciphertext_uni by apply dplaintext_uni.
realize dciphertext_full by apply dplaintext_full.

(* XOR operator over plaintexts with minimal properties *)
op (^) : plaintext -> plaintext -> plaintext.

axiom xor_idempotent1 x y : (x ^ y) ^ y = x.
axiom xor_idempotent2 x y : x ^ (x ^ y) = y.

(* Encryption and decryption operators *)
op enc k n p = f k n ^ p.
op dec k n c = f k n ^ c.

(* We prove that decryption recovers an encrypted 
   message using the core logic. This lemma can
   then be used to prove that the scheme is correct. *)
lemma enc_dec_correct k n p :
  dec k n (enc k n p) = p
 by  rewrite /enc /dec xor_idempotent2.

(* The encryption scheme  in the correct syntax. *)
module Scheme : Scheme_T = {

  proc kg () = {
    var k;
    k <$ dkey;
    return k;
  }
  
  proc enc(k:key, n:nonce, p:plaintext) = {
    var mask, c;
    mask <- f k n;
    c <- mask ^ p;
    return c;
  }

  proc dec(k:key, n:nonce, c:ciphertext) = {
    var mask, p;
    mask <- f k n;
    p <- mask ^ c;
    return p;
  }
}.

(*************************************************************)
(*                      CORRECTNESS                          *)
(*************************************************************)


(* We prove partial correctness with respect to the functional
   operators. I.e., correct if terminates.  *)
lemma correct_enc_h k n p :
  hoare [ Scheme.enc : arg = (k,n,p) ==> res = enc k n p]
   by proc; wp; skip; move => /> *; rewrite /enc. 

(* Encryption always terminates *)
lemma correct_enc_ll : islossless Scheme.enc by islossless.

(* Total correctness as a corollary. 
   This means we can always lift any call to
   the enc procedure to a logical operation over its
   inputs *)
lemma correct_enc k n p :
  phoare [ Scheme.enc : arg = (k,n,p) ==> res = enc k n p] = 1%r
  by conseq correct_enc_ll (correct_enc_h k n p). 

(* We do the same for decryption *)
lemma correct_dec_h k n c :
  hoare [ Scheme.dec : arg = (k,n,c) ==> res = dec k n c]
   by proc; wp; skip; move => /> *; rewrite /dec. 

lemma correct_dec_ll : islossless Scheme.dec by islossless.

lemma correct_dec k n c :
  phoare [ Scheme.dec : arg = (k,n,c) ==> res = dec k n c] = 1%r
  by conseq correct_dec_ll (correct_dec_h k n c). 

(* We can apply the above lemmas when we prove that the
   construction is correct as a nonce-based encryption scheme:
   lift encryption and decryption to logical operations and
   then use the fact that the logical operators cancel as
   proved in enc_dec_correct. *)
lemma correctness &m _k _n _p:
  Pr[ Correctness(Scheme).main(_k,_n,_p) @ &m : res ] = 1%r.
byphoare (_: arg = (_k,_n,_p) ==> _) => //.
have lossless: islossless Correctness(Scheme).main; first by islossless.
have correct : hoare [ Correctness(Scheme).main : arg = (_k, _n, _p) ==> res ].
+ proc.
  seq 1 : (#pre /\ c = enc _k _n _p).
  call (correct_enc_h _k _n _p); first by auto => />.
  ecall (correct_dec_h _k _n c). 
  by auto => />; rewrite enc_dec_correct.
by conseq lossless correct. 
qed.

(*************************************************************)
(*                          SECURITY                         *)
(*************************************************************)

(* B is a reduction that breaks PRF if A breaks encryption scheme  *)

module (B(A:AdvCPA):Adv) (O:Orcl) = {
  
  module OCPA = {
    proc init() = { }

    proc enc (n:nonce, p:plaintext) = {
      var r;
      r <@ O.f(n);
      return (r ^ p);
    }
  }

  proc guess = CPA(A, OCPA).main

}.

section PROOF.

(*  Declaring an adversary in a section quantifies  universally
    over A for all results in the section. The names in brackets
    indicate that A cannot touch the internal states of these
    modules. Otherwise the proof fails (e.g., A could just get
    the PRF key! *)
declare module A:AdvCPA {Real_Ideal, Real_PRF, RealScheme, RF, WO}.

(* We prove equivalences between games using pRHL, which then
   allow us to derive probability results as a consequence.
   These equivalences talk about how events occurring in
   one game relate to events occurring in the other game. *)

(* If PRF game is uses PRF then we are using the real scheme.
   There is a syntactic identity between the games modulo
   renamings. 
   If A starts from the same state, then both games output 
   the same result res and the global counter has the same
   value, so B makes same queries as A. *)
lemma Real_CPA_PRF : 
  equiv [ CPA(A, RealScheme(Scheme)).main ~ Real_Ideal(B(A), Real_PRF).main :
            ={glob A} ==> ={res, QCounter.q} ].
proof.
proc.
 inline *; wp. 
call (: ={WO.nonces,QCounter.q} /\ RealScheme.k{1} = Real_PRF.k{2}).
+ by proc; inline *; auto => /> /#.
by auto => />.
qed.

(* We introduce a game hop where we modify the scheme to use
   a true random function instead of the PRF *)
module ModifiedScheme = {
   include Scheme [-enc,kg]
  
   proc kg() : key = { 
     RF.init();
     return witness;
   }

   proc enc(k : key, n : nonce, p : plaintext) : ciphertext = {
    var mask : plaintext;
    var c : ciphertext;
    
    mask <@ RF.f(n);
    c <- mask ^ p;
    
    return c;
  }
}.

(* If PRF game uses RF then we are using the modified scheme.
   Again the proof is simply a syntactic match. *)
lemma Modified_CPA_PRF: 
  equiv [ CPA(A, RealScheme(ModifiedScheme)).main ~ Real_Ideal(B(A), Ideal_PRF).main :
            ={glob A} ==> ={res, QCounter.q} ].
proof.
proc; inline *; wp.
call (: ={WO.nonces,RF.m,QCounter.q}).
+ by proc; inline *;sim.
by auto.
qed.

(* Now we do a final step to show we have reached the ideal
   game; we need to argue that the RF acts as a one-time pad
   so ciphertexts do look totally random. *)
lemma Modified_CPA_Ideal:
  equiv [ CPA(A, RealScheme(ModifiedScheme)).main ~ CPA(A, IdealScheme).main :
            ={glob A} ==> ={res, QCounter.q} ].
proof.
proc; inline *; wp.
call (: ={WO.nonces,QCounter.q} /\
          (forall n, n \in WO.nonces = n \in RF.m){1}).
+ proc; inline *.
  sp; if; 1, 3: by auto.
  rcondt{1} ^if; 1: by auto => /#.  
  wp. rnd (fun r => r ^ p{1}). 
  auto => />; smt (get_setE xor_idempotent1 dciphertext_uni  dciphertext_full).
by auto => /> *; rewrite mem_empty.
qed.

(* Our main theorem relates advantages of A and B, and it also relates
   the number of queries both make. *)
lemma incpa_security_hop &m q:
   (* Advantages match *)
  `| Pr[CPA(A,RealScheme(Scheme)).main() @ &m : res] - 
       Pr[CPA(A,IdealScheme).main() @ &m : res]| =
  `| Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : res] - 
       Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : res] | /\

   (* Same number of queries in real games *)
     Pr[CPA(A,RealScheme(Scheme)).main() @ &m : QCounter.q = q ] =
     Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : QCounter.q = q ] /\ 

   (* Same number of queries in ideal games *)
     Pr[CPA(A,IdealScheme).main() @ &m : QCounter.q = q ] =
     Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : QCounter.q = q ]
.
proof.
do split.

(* have -> introduces a new proof goal and immediately rewrites it once
   proved. Here we use the equiv lemmas proved above to rewrite probability
   equalities and wrap up the proof. *)

+ have -> : (Pr[CPA(A,RealScheme(Scheme)).main() @ &m : res] =
            Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : res]); 
     first by byequiv (Real_CPA_PRF) => //.

  have <- : (Pr[CPA(A,RealScheme(ModifiedScheme)).main() @ &m : res] =
            Pr[CPA(A,IdealScheme).main() @ &m : res]); 
     first by byequiv (Modified_CPA_Ideal) => //.

  have -> : (Pr[CPA(A,RealScheme(ModifiedScheme)).main() @ &m : res] =
            Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : res]); 
     [ by byequiv (Modified_CPA_PRF) => // | by done ].

+ have -> : (Pr[CPA(A,RealScheme(Scheme)).main() @ &m : QCounter.q = q] =
            Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : QCounter.q = q]); 
     [ by byequiv (Real_CPA_PRF) => // | by done ].

+ have <- : (Pr[CPA(A,RealScheme(ModifiedScheme)).main() @ &m : QCounter.q = q] =
            Pr[CPA(A,IdealScheme).main() @ &m : QCounter.q = q]); 
     first by byequiv (Modified_CPA_Ideal) => //.

  have <- : (Pr[CPA(A,RealScheme(ModifiedScheme)).main() @ &m : QCounter.q = q] =
            Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : QCounter.q = q]); 
     [ by byequiv (Modified_CPA_PRF) => // | by done].

qed.

end section PROOF.

(*************************************************************)
(*                   Alternative Proof                       *)
(*************************************************************)

(* The same B above can be used to perform a direct reduction
   proof, where we bridge directly the ideal scheme to 
   the ideal PRF game. *)

section PROOF.

declare module A:AdvCPA {WO, Real_PRF, Ideal, RealScheme, ModifiedScheme}.

(* If PRF game uses RF then we are using the ideal scheme.
   We need to argue that xor acts as a one time pad to get the
   equivalence.  *)
lemma Ideal_CPA_PRF : 
  equiv [ CPA(A, IdealScheme).main ~ Real_Ideal(B(A), Ideal_PRF).main : 
            ={glob A} ==> ={res, QCounter.q} ].
proof.
proc; inline *; wp.
call (: ={WO.nonces,QCounter.q} /\
            (forall n, n \in WO.nonces = n \in RF.m){2}).
+ proc; inline *.
  sp; if; 1, 3: by auto.
  rcondt{2} ^if; 1: by auto => /#.  
  wp. rnd (fun r => r ^ p{2}). 
  auto => />; smt (get_setE xor_idempotent1 dciphertext_uni  dciphertext_full).
by auto => /> *; rewrite mem_empty.
qed.

(* The same result follows. *)
lemma indcpa_security &m q :

   (* Advantages match *)
  `| Pr[CPA(A,RealScheme(Scheme)).main() @ &m : res] - 
       Pr[CPA(A,IdealScheme).main() @ &m : res]| =
  `| Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : res] - 
       Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : res] | /\

   (* Same number of queries in real games *)
     Pr[CPA(A,RealScheme(Scheme)).main() @ &m : QCounter.q = q ] =
     Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : QCounter.q = q ] /\ 

   (* Same number of queries in ideal games *)
     Pr[CPA(A,IdealScheme).main() @ &m : QCounter.q = q ] =
     Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : QCounter.q = q ]
.
proof.
do split.

+ have -> : (Pr[CPA(A,RealScheme(Scheme)).main() @ &m : res] =
            Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : res]); 
     first by byequiv (Real_CPA_PRF A) => //.

  have <- : (Pr[CPA(A,IdealScheme).main() @ &m : res] =
            Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : res]); 
     [ by byequiv (Ideal_CPA_PRF) => // | by done].

+ have -> : (Pr[CPA(A,RealScheme(Scheme)).main() @ &m : QCounter.q = q] =
            Pr[Real_Ideal(B(A), Real_PRF).main() @ &m : QCounter.q = q]); 
     [ by byequiv (Real_CPA_PRF A) => // | by done].

+ have <- : (Pr[CPA(A,IdealScheme).main() @ &m : QCounter.q = q] =
            Pr[Real_Ideal(B(A), Ideal_PRF).main() @ &m : QCounter.q = q]); 
     [ by byequiv (Ideal_CPA_PRF) => // | by done].

qed.


end section PROOF.

(* The hopping technique above can be extended to make explicit
   the PRF-PRP bound if f is a permutation. 

   First modify the scheme to use a RP (rather than directly 
   an RF) and prove that any difference in the CPA game can be
   used to win the PRP game against f. This will be the new
   computational assumption in the final bound. 

   Then use generic RP-RF switching lemma to hop to the 
   modified scheme that uses the RF and proceed as above. 
   The EC library already includes the switching lemma. *)


end NbPRFEnc.
