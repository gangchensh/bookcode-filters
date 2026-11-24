From Theories Require Import ProjectBase.

Example above_three : above 3 3.                        (* 验证3不小于3 *)
Proof.
  exact (above_self 3).
Qed.
