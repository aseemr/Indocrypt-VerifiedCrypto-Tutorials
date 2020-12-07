require import AllCore List.
from Jasmin require import JWord AES JModel.
require import Array11.

(* ------------------------------------------------------------------------ *)
(* AES specification in a functional style                                  *)

op key_expand (wn1 : W128.t) (rcon : W8.t)  =
   let rcon = W4u8.pack4 [rcon; W8.zero; W8.zero; W8.zero] in 
   let w0 = wn1 \bits32 0 in
   let w1 = wn1 \bits32 1 in
   let w2 = wn1 \bits32 2 in
   let w3 = wn1 \bits32 3 in
    
   let tmp = w3 in
   let tmp = SubWord(RotWord(tmp)) `^` rcon in
   let w4 = w0 `^` tmp in
   let w5 = w1 `^` w4 in
   let w6 = w2 `^` w5 in
   let w7 = w3 `^` w6 in
   W4u32.pack4 [w4; w5; w6; w7].
  
op rcon : int -> W8.t.
axiom rcon_nth i : 
  0 <= i < 10 => 
  rcon (i + 1) = W8.of_int (nth 0 [1; 2; 4; 8; 16; 32; 64; 128; 27; 54] i).

op key_i (k : W128.t) i = 
  iteri i (fun i ki => key_expand ki (rcon (i+1))) k
axiomatized by key_iE.

op aes (key msg : W128.t) = 
  let state = AddRoundKey msg (key_i key 0) in
  let state = iteri 9 (fun i state => AESENC_ state (key_i key (i + 1))) state in
  AESENCLAST_ state (key_i key 10) 
axiomatized by aesE.

op invaes (key cipher : W128.t) = 
  let state = AddRoundKey cipher (key_i key 10) in
  let state = iteri 9 (fun i state => AESDEC_ state (key_i key (10 -(i + 1)))) state in
  AESDECLAST state (key_i key 0) 
axiomatized by invaesE.

(* Correctness of the AES rounds : invaes_rounds k (aes_rounds k m) = m *)
lemma aux1 c k1 k2: 
      AESDEC_ (AddRoundKey (AESENCLAST_ c k1) k1) k2 = InvMixColumns (c `^` k2).
proof.
  by rewrite AESDEC_E AESENCLAST_E /= 
        /AddRoundKey W128.WRing.subrK InvShiftRowsK InvSubBytesK.
qed.

lemma aux2 c k1 k2 : 
      AESDEC_ (InvMixColumns (AESENC_ c k1 `^` k1)) k2 = InvMixColumns (c `^` k2).
proof. 
  by rewrite AESDEC_E AESENC_E 
       /AddRoundKey /= W128.WRing.subrK InvMixColumnsK InvShiftRowsK InvSubBytesK.
qed.

lemma invaes_roundsK k m : invaes k (aes k m) = m.
proof.
  rewrite invaesE aesE /=.
  do 9! rewrite iteri_red 1:// /=; rewrite iteri0 1:// /=.
  do 9! rewrite iteri_red 1:// /=; rewrite iteri0 1:// /=.
  rewrite aux1 !aux2.
  rewrite AESDECLASTE /= AESENC_E /AddRoundKey /= W128.WRing.subrK.
  by rewrite InvMixColumnsK InvShiftRowsK InvSubBytesK W128.WRing.subrK.
qed.

(* ------------------------------------------------------------------------ *)
(* AES specification in a pseudo code style                                 *)

module Aes = {
  proc keyExpansion (key : W128.t) = {
    var rkeys : W128.t Array11.t;
    var round : int;

    rkeys <- witness;
    rkeys.[0] <- key;
    round    <- 1;
    while (round < 11) {
      rkeys.[round] <- key_expand rkeys.[round-1] (rcon round);
      round <- round + 1;
    }
    return rkeys;
  }

  proc aes_rounds (rkeys : W128.t Array11.t,  msg : W128.t) = {
    var state, round;
    state <- AddRoundKey msg rkeys.[0];
    round <- 1;
    while (round < 10) {
      state <- AESENC_ state rkeys.[round];
      round <- round + 1;
    }
    state <- AESENCLAST_ state rkeys.[round];
    return state;
  }

  proc aes (key msg: W128.t) = {
    var rkeys, cipher;
    rkeys  <@ keyExpansion(key);
    cipher <@ aes_rounds(rkeys, msg);
    return cipher;
  }

  proc invaes_rounds (rkeys : W128.t Array11.t, cipher : W128.t) = {
    var state, round;
    state <- AddRoundKey cipher rkeys.[10];
    round <- 9;
    while (0 < round) {
      state <- AESDEC_ state rkeys.[round];
      round <- round - 1;
    }
    state <- AESDECLAST state rkeys.[0];
    return state;
  }

  proc invaes (key cipher: W128.t) = {
    var rkeys, msg;
    rkeys  <@ keyExpansion(key);
    msg <@ invaes_rounds(rkeys, cipher);
    return msg;
  }

}.

(* ------------------------------------------------------------------------ *)
(* Showing imperative spec is equivalent to func spec                       *)

(* keyExpansion *)
hoare aes_keyExpansion k : 
  Aes.keyExpansion : key = k 
  ==> 
  forall i, 0 <= i < 11 => res.[i] = key_i k i.
proof.
  proc.
  while (1 <= round <= 11 /\ forall i, 0 <= i < round => rkeys.[i] = key_i k i).
  + by auto => />; smt (key_iE iteriS get_setE).
  by auto => />; smt(key_iE iteri0 get_setE).
qed.

(* aes_rounds and aes *) 

hoare aes_rounds k m : 
  Aes.aes_rounds : (forall i, 0 <= i < 11 => rkeys.[i] = key_i k i) /\ msg = m 
  ==>
  res = aes k m.
proof.
  proc; wp. 
  pose st0 := AddRoundKey m (key_i k 0). 
  while (1 <= round <= 10 /\ (forall i, 0 <= i < 11 => rkeys.[i] = key_i k i) /\
         state = iteri (round - 1) (fun i state => AESENC_ state (key_i k (i + 1))) st0).
  + by wp; skip; smt (iteriS).
  by wp; skip; smt(aesE iteri0).
qed.

hoare aes_h k m : 
  Aes.aes : key = k /\ msg = m 
  ==>
  res = aes k m.
proof.
  proc; call (aes_rounds k m); call (aes_keyExpansion k); skip => />.
qed.

phoare aes_ll : [Aes.aes : true ==> true] = 1%r.
proof. 
  islossless.
  + by while (true) (10 - round); auto => /#.
  by while (true) (11 - round); auto => /#.
qed.

phoare aes k m : [Aes.aes : key = k /\ msg = m  ==> res = aes k m] = 1%r.
proof. conseq aes_ll (aes_h k m) => />. qed.

(* invaes_rounds and invaes *) 

hoare invaes_rounds k c : 
  Aes.invaes_rounds : (forall i, 0 <= i < 11 => rkeys.[i] = key_i k i) /\ cipher = c
  ==>
  res = invaes k c.
proof.
  proc; wp. 
  pose st0 := AddRoundKey c (key_i k 10). 
  while (0 <= round <= 9 /\ (forall i, 0 <= i < 11 => rkeys.[i] = key_i k i) /\
         state = iteri (9 - round) (fun i state => AESDEC_ state (key_i k (10 - (i + 1)))) st0).
  + by wp; skip; smt (iteriS). 
  by wp; skip; smt(invaesE iteri0).
qed.

hoare invaes_h k c : 
  Aes.invaes : key = k /\ cipher = c
  ==>
  res = invaes k c.
proof.
  proc; call (invaes_rounds k c); call (aes_keyExpansion k); skip => />.
qed.

phoare invaes_ll : [Aes.invaes : true ==> true] = 1%r.
proof. 
  islossless.
  + by while (true) (round); auto => /#.
  by while (true) (11 - round); auto => /#.
qed.

phoare invaes k c : [Aes.invaes : key = k /\ cipher = c  ==> res = invaes k c] = 1%r.
proof. conseq invaes_ll (invaes_h k c) => />. qed.
