require import AllCore List.
from Jasmin require import JModel.
require import AES_jazz_ct Array11.

(* Make the name of variables shorter *)
import var AES_jazz_ct.M.

equiv aes_ct : 
    AES_jazz_ct.M.aes ~ AES_jazz_ct.M.aes : 
         ={leakages}  ==> ={leakages}.
proof. proc; inline *; sim. qed.

equiv invaes_ct : 
    AES_jazz_ct.M.invaes ~ AES_jazz_ct.M.invaes : 
         ={leakages}  ==> ={leakages}.
proof. proc; inline *; sim. qed.



