require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array11.
require import WArray176.



module M = {
  proc rCON (i:int) : int = {
    
    var c:int;
    
    c <-
    ((i = 1) ? 1 : ((i = 2) ? 2 : ((i = 3) ? 4 : ((i = 4) ? 8 : ((i = 5) ? 16 : ((i = 6) ? 32 : ((i = 7) ? 64 : ((i = 8) ? 128 : ((i = 9) ? 27 : 54)))))))));
    return (c);
  }
  
  proc key_combine (rkey:W128.t, temp1:W128.t, temp2:W128.t) : W128.t *
                                                               W128.t = {
    
    
    
    temp1 <- VPSHUFD_128 temp1
    (W8.of_int (3 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * 3))));
    temp2 <- VSHUFPS_128 temp2 rkey
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (1 %% 2^2 + 2^2 * 0))));
    rkey <- (rkey `^` temp2);
    temp2 <- VSHUFPS_128 temp2 rkey
    (W8.of_int (0 %% 2^2 + 2^2 * (3 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    rkey <- (rkey `^` temp2);
    rkey <- (rkey `^` temp1);
    return (rkey, temp2);
  }
  
  proc key_expand (rcon:int, rkey:W128.t, temp2:W128.t) : W128.t * W128.t = {
    
    var temp1:W128.t;
    
    temp1 <- VAESKEYGENASSIST rkey (W8.of_int rcon);
    (rkey, temp2) <@ key_combine (rkey, temp1, temp2);
    return (rkey, temp2);
  }
  
  proc keys_expand (key:W128.t) : W128.t Array11.t = {
    var aux: int;
    
    var rkeys:W128.t Array11.t;
    var temp2:W128.t;
    var round:int;
    var rcon:int;
    rkeys <- witness;
    rkeys.[0] <- key;
    temp2 <- setw0_128 ;
    round <- 1;
    while (round < 11) {
      rcon <@ rCON (round);
      (key, temp2) <@ key_expand (rcon, key, temp2);
      rkeys.[round] <- key;
      round <- round + 1;
    }
    return (rkeys);
  }
  
  proc keys_expand_inv (key:W128.t) : W128.t Array11.t = {
    var aux: int;
    
    var rkeys:W128.t Array11.t;
    var temp2:W128.t;
    var round:int;
    var rcon:int;
    rkeys <- witness;
    rkeys.[0] <- key;
    temp2 <- setw0_128 ;
    round <- 1;
    while (round < 11) {
      rcon <@ rCON (round);
      (key, temp2) <@ key_expand (rcon, key, temp2);
      if ((round <> 10)) {
        rkeys.[round] <- AESIMC key;
      } else {
        rkeys.[round] <- key;
      }
      round <- round + 1;
    }
    return (rkeys);
  }
  
  proc aes_rounds (rkeys:W128.t Array11.t, in_0:W128.t) : W128.t = {
    var aux: int;
    
    var state:W128.t;
    var round:int;
    
    state <- in_0;
    state <- (state `^` rkeys.[0]);
    round <- 1;
    while (round < 10) {
      state <- AESENC state rkeys.[round];
      round <- round + 1;
    }
    state <- AESENCLAST state rkeys.[10];
    return (state);
  }
  
  proc addRoundKey (state:W128.t, rk:W128.t) : W128.t = {
    
    
    
    state <- (state `^` rk);
    return (state);
  }
  
  proc invaes_rounds (rkeys:W128.t Array11.t, in_0:W128.t) : W128.t = {
    var aux: int;
    
    var state:W128.t;
    var rk:W128.t;
    var round:int;
    
    state <- in_0;
    rk <- rkeys.[10];
    state <@ addRoundKey (state, rk);
    round <- 9;
    while (0 < round) {
      state <- AESDEC state rkeys.[round];
      round <- round - 1;
    }
    state <- AESDECLAST state rkeys.[0];
    return (state);
  }
  
  proc aes (key:W128.t, in_0:W128.t) : W128.t = {
    
    var out:W128.t;
    var rkeys:W128.t Array11.t;
    rkeys <- witness;
    rkeys <@ keys_expand (key);
    out <@ aes_rounds (rkeys, in_0);
    return (out);
  }
  
  proc invaes (key:W128.t, in_0:W128.t) : W128.t = {
    
    var out:W128.t;
    var rkeys:W128.t Array11.t;
    rkeys <- witness;
    rkeys <@ keys_expand_inv (key);
    out <@ invaes_rounds (rkeys, in_0);
    return (out);
  }
}.

