From BookTheory Require Import Basics.
Require Import Small.

Example sample_ok : sample = 3.                         (* 验证被导入的sample等于3 *)
Proof. reflexivity. Qed.                                (* 展开定义后两边相同 *)

Check marker.
