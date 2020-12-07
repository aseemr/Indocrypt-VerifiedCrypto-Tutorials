require import AllCore List.
from Jasmin require import JModel.
require import NbAESEnc_jazz_ct.

(* Make the name of variables shorter *)
import var NbAESEnc_jazz_ct.M.

equiv enc_ct : 
    NbAESEnc_jazz_ct.M.enc ~ NbAESEnc_jazz_ct.M.enc : 
        ={leakages}  ==> ={leakages}.
proof. proc; inline *; sim. qed.

equiv dec_ct : 
    NbAESEnc_jazz_ct.M.dec ~ NbAESEnc_jazz_ct.M.dec : 
        ={leakages}  ==> ={leakages}.
proof. proc; inline *; sim. qed.

