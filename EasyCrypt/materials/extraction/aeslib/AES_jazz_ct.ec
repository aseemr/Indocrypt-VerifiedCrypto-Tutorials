require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array11.
require import WArray176.



module M = {
  var leakages : leakages_t
  
  proc rCON (i:int) : int = {
    var aux: int;
    
    var c:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- ((i = 1) ? 1 : ((i = 2) ? 2 : ((i = 3) ? 4 : ((i = 4) ? 8 : ((i = 5) ? 16 : ((i = 6) ? 32 : ((i = 7) ? 64 : ((i = 8) ? 128 : ((i = 9) ? 27 : 54)))))))));
    c <- aux;
    return (c);
  }
  
  proc key_combine (rkey:W128.t, temp1:W128.t, temp2:W128.t) : W128.t *
                                                               W128.t = {
    var aux: W128.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- VPSHUFD_128 temp1
    (W8.of_int (3 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 3))));
    temp1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VSHUFPS_128 temp2 rkey
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    temp2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (rkey `^` temp2);
    rkey <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- VSHUFPS_128 temp2 rkey
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    temp2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (rkey `^` temp2);
    rkey <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- (rkey `^` temp1);
    rkey <- aux;
    return (rkey, temp2);
  }
  
  proc key_expand (rcon:int, rkey:W128.t, temp2:W128.t) : W128.t * W128.t = {
    var aux_0: W128.t;
    var aux: W128.t;
    
    var temp1:W128.t;
    
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- VAESKEYGENASSIST rkey (W8.of_int rcon);
    temp1 <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <@ key_combine (rkey, temp1, temp2);
    rkey <- aux_0;
    temp2 <- aux;
    return (rkey, temp2);
  }
  
  proc keys_expand (key:W128.t) : W128.t Array11.t = {
    var aux_0: int;
    var aux_1: W128.t;
    var aux: W128.t;
    
    var rkeys:W128.t Array11.t;
    var temp2:W128.t;
    var round:int;
    var rcon:int;
    rkeys <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- key;
    leakages <- LeakAddr([0]) :: leakages;
    rkeys.[0] <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- setw0_128 ;
    temp2 <- aux_1;
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    round <- 1;
    while (round < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ rCON (round);
      rcon <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux) <@ key_expand (rcon, key, temp2);
      key <- aux_1;
      temp2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_1 <- key;
      leakages <- LeakAddr([round]) :: leakages;
      rkeys.[round] <- aux_1;
      round <- round + 1;
    }
    return (rkeys);
  }
  
  proc keys_expand_inv (key:W128.t) : W128.t Array11.t = {
    var aux_0: int;
    var aux_1: W128.t;
    var aux: W128.t;
    
    var rkeys:W128.t Array11.t;
    var temp2:W128.t;
    var round:int;
    var rcon:int;
    rkeys <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- key;
    leakages <- LeakAddr([0]) :: leakages;
    rkeys.[0] <- aux_1;
    leakages <- LeakAddr([]) :: leakages;
    aux_1 <- setw0_128 ;
    temp2 <- aux_1;
    leakages <- LeakFor(1,11) :: LeakAddr([]) :: leakages;
    round <- 1;
    while (round < 11) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ rCON (round);
      rcon <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      (aux_1, aux) <@ key_expand (rcon, key, temp2);
      key <- aux_1;
      temp2 <- aux;
      leakages <- LeakCond((round <> 10)) :: LeakAddr([]) :: leakages;
      if ((round <> 10)) {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- AESIMC key;
        leakages <- LeakAddr([round]) :: leakages;
        rkeys.[round] <- aux_1;
      } else {
        leakages <- LeakAddr([]) :: leakages;
        aux_1 <- key;
        leakages <- LeakAddr([round]) :: leakages;
        rkeys.[round] <- aux_1;
      }
      round <- round + 1;
    }
    return (rkeys);
  }
  
  proc aes_rounds (rkeys:W128.t Array11.t, in_0:W128.t) : W128.t = {
    var aux_0: int;
    var aux: W128.t;
    
    var state:W128.t;
    var round:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- in_0;
    state <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (state `^` rkeys.[0]);
    state <- aux;
    leakages <- LeakFor(1,10) :: LeakAddr([]) :: leakages;
    round <- 1;
    while (round < 10) {
      leakages <- LeakAddr([round]) :: leakages;
      aux <- AESENC state rkeys.[round];
      state <- aux;
      round <- round + 1;
    }
    leakages <- LeakAddr([10]) :: leakages;
    aux <- AESENCLAST state rkeys.[10];
    state <- aux;
    return (state);
  }
  
  proc addRoundKey (state:W128.t, rk:W128.t) : W128.t = {
    var aux: W128.t;
    
    
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- (state `^` rk);
    state <- aux;
    return (state);
  }
  
  proc invaes_rounds (rkeys:W128.t Array11.t, in_0:W128.t) : W128.t = {
    var aux_0: int;
    var aux: W128.t;
    
    var state:W128.t;
    var rk:W128.t;
    var round:int;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <- in_0;
    state <- aux;
    leakages <- LeakAddr([10]) :: leakages;
    aux <- rkeys.[10];
    rk <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ addRoundKey (state, rk);
    state <- aux;
    leakages <- LeakFor(0,9) :: LeakAddr([]) :: leakages;
    round <- 0;
    while (9 < round) {
      leakages <- LeakAddr([round]) :: leakages;
      aux <- AESDEC state rkeys.[round];
      state <- aux;
      round <- round - 1;
    }
    leakages <- LeakAddr([0]) :: leakages;
    aux <- AESDECLAST state rkeys.[0];
    state <- aux;
    return (state);
  }
  
  proc aes (key:W128.t, in_0:W128.t) : W128.t = {
    var aux_0: W128.t;
    var aux: W128.t Array11.t;
    
    var out:W128.t;
    var rkeys:W128.t Array11.t;
    rkeys <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ keys_expand (key);
    rkeys <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ aes_rounds (rkeys, in_0);
    out <- aux_0;
    return (out);
  }
  
  proc invaes (key:W128.t, in_0:W128.t) : W128.t = {
    var aux_0: W128.t;
    var aux: W128.t Array11.t;
    
    var out:W128.t;
    var rkeys:W128.t Array11.t;
    rkeys <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ keys_expand_inv (key);
    rkeys <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ invaes_rounds (rkeys, in_0);
    out <- aux_0;
    return (out);
  }
}.

