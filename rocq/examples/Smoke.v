From Theories Require Import Eventually.

Check EventuallyNat_and.

Example eventually_ge_100 : EventuallyNat (fun n => 100 <= n).  (* 自然数最终不小于100 *)
Proof.
  exists 100.                                           (* 选取100作为见证 *)
  intros n Hn.
  exact Hn.
Qed.
