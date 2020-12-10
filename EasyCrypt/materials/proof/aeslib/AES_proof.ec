require import AllCore List.
from Jasmin require import JModel.
require import AES_jazz AES_spec Array11.


(* ------------------------------------------------------------------------------*)
(* Functional correctness of key_expand                                          *)

phoare rCONP round : 
  [M.rCON : 1 <= i <= 10 /\ i = round 
        ==> W8.of_int res = rcon round] = 1%r.
proof. by proc; wp; skip; smt (rcon_nth). qed.

phoare key_expandP rcon_ k : 
  [M.key_expand : W8.of_int rcon = rcon_ /\ rkey = k /\ temp2 \bits32 0 = W32.of_int 0
            ==> res.`1 = key_expand k rcon_ /\ res.`2 \bits32 0 = W32.of_int 0] = 1%r.
proof.
  proc; inline *; wp; skip => /= &m [#] -> -> h.
  rewrite AESKEYGENASSISTE; cbv delta; rewrite h /=.
  apply W4u32.allP => /=; smt (W32.WRing.addrA W32.WRing.addrC).
qed.

equiv keyExpansion_E : M.keys_expand ~ Aes.keyExpansion : ={arg} ==> ={res}.
proof.
  proc.
  while (1 <= round{1} /\ ={round, rkeys} /\ 
         (key = rkeys.[round - 1]){1} /\ temp2{1} \bits32 0 = W32.of_int 0).
  + wp.
    ecall{1} (key_expandP (W8.of_int rcon{1}) key{1}).
    by ecall{1} (rCONP round{1}); skip; smt(get_setE).
  by auto.
qed.

(* ------------------------------------------------------------------------------*)
(* Functional correctness of aes_rounds and aes                                  *)

equiv aes_rounds_E : M.aes_rounds ~ Aes.aes_rounds : ={arg} ==> ={res}.
proof.
  proc; wp.
  while (={round, state, rkeys} /\ round{1} <= 10).  
  + by wp; skip; rewrite AESENC_AESENC_ /#.
  wp; skip; smt(AESENCLAST_AESENCLAST_).
qed.

equiv aes_E : M.aes ~ Aes.aes : ={arg} ==> ={res}.
proof. by proc; call aes_rounds_E; call keyExpansion_E; wp; skip. qed.

phoare aes_jazz k n : [M.aes : arg = (k,n) ==> res  = aes k n] = 1%r.
proof. conseq aes_E (aes k n) => /#. qed.

(* ------------------------------------------------------------------------------*)
(* Functional correctness of invaes_rounds and invaes                            *)

equiv keyExpansion_inv_E : M.keys_expand_inv ~ Aes.keyExpansion : ={arg} ==> 
  res{1}.[0] = res{2}.[0] /\ res{1}.[10] = res{2}.[10] /\
  (forall i, 1 <= i < 10 => res{1}.[i] = InvMixColumns res{2}.[i]).
proof.
  proc.
  while (1 <= round{1} <= 11 /\ ={round} /\ 
         key{1} = (rkeys.[round - 1]){2} /\
         rkeys{1}.[0] = rkeys{2}.[0] /\ temp2{1} \bits32 0 = W32.of_int 0 /\
        (forall i, 1 <= i < round{1} => 
           rkeys{1}.[i] = if i < 10 then InvMixColumns rkeys{2}.[i]
                        else rkeys{2}.[i])).
  + wp.
    ecall{1} (key_expandP (W8.of_int rcon{1}) key{1}).
    by ecall{1} (rCONP round{1}); skip; smt(get_setE).
  by auto => /> /#.
qed.

equiv invaes_rounds_E : M.invaes_rounds ~ Aes.invaes_rounds : 
  rkeys{1}.[0] = rkeys{2}.[0] /\ rkeys{1}.[10] = rkeys{2}.[10] /\
  (forall i, 1 <= i < 10 => rkeys{1}.[i] = InvMixColumns rkeys{2}.[i]) /\
  in_0{1} = cipher{2}
  ==> 
  ={res}.
proof.
  proc; wp.
  while (={round, state} /\ 0 <= round{1} <= 9 /\
    (forall i, 1 <= i < 10 => rkeys{1}.[i] = InvMixColumns rkeys{2}.[i])).
  + by wp; skip; rewrite -AESDEC_AESDEC_ /#.
  by inline *; wp; skip => /#.
qed.

equiv invaes_E : M.invaes ~ Aes.invaes : ={arg} ==> ={res}.
proof. by proc; call invaes_rounds_E; call keyExpansion_inv_E; wp; skip. qed.

phoare invaes_jazz k n : [M.invaes : arg = (k,n) ==> res = invaes k n] = 1%r.
proof. conseq invaes_E (invaes k n) => /#. qed.



