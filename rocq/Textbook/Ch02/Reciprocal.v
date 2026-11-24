From Stdlib Require Import Reals Psatz.
From Textbook.Ch02 Require Import Eventually.

Open Scope R_scope.

Theorem eventually_reciprocal (eps : R) (Heps : 0 < eps) :  (* 为倒数估计选择阈值 *)
  EventuallyNat (fun n => 1 / (INR n + 1) < eps).       (* 需要证明倒数最终小于距离上界 *)
Proof.
  destruct (INR_archimed eps 1 Heps) as [N HN].
  exists N.                                             (* 选取N作为见证 *)
  intros n Hn.
  pose proof (le_INR N n Hn) as Hle.                    (* 把已有定理加入当前假设 *)
  pose proof (pos_INR n) as Hpos.                       (* 把已有定理加入当前假设 *)
  apply (Rmult_lt_reg_r (INR n + 1)).
  - lra.                                                (* 核对线性实数不等式 *)
  - unfold Rdiv.
    rewrite Rmult_assoc, Rinv_l.  (* 按Rmult_assoc, Rinv_l给出的等式或等价式改写 *)
    + nra.                                              (* 核对非线性实数运算 *)
    + lra.                                              (* 核对线性实数不等式 *)
Qed.
