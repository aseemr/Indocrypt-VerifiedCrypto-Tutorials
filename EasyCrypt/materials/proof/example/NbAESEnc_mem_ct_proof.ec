require import AllCore List.
from Jasmin require import JModel.
require import NbAESEnc_mem_jazz_ct.

(* Make the name of variables shorter *)
import var NbAESEnc_mem_jazz_ct.M.

(* This does not work but it  helps to find 
   what should be public *)
(*
equiv enc_ct : 
    NbAESEnc_mem_jazz_ct.M.enc ~ NbAESEnc_mem_jazz_ct.M.enc : 
       ={leakages}  ==> ={leakages}.
proof. proc; inline *; sim. qed.
*)

(* Remark: we require that pointers "cptr, pptr, nptr, kptr" 
   are equal, not the contents of the memory they point to.
   I.e we do not require that the memory content is equal. *)

equiv enc_ct : 
    NbAESEnc_mem_jazz_ct.M.enc ~ NbAESEnc_mem_jazz_ct.M.enc : 
        ={cptr, pptr, nptr, kptr, leakages}  ==> ={leakages}.
proof. proc; inline *; sim. qed.

equiv dec_ct : 
    NbAESEnc_mem_jazz_ct.M.dec ~ NbAESEnc_mem_jazz_ct.M.dec : 
        ={pptr, cptr, nptr, kptr,leakages}  ==> ={leakages}.
proof. proc; inline *; sim. qed.
