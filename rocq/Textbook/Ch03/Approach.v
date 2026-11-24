From Stdlib Require Import Reals Lra Psatz.
From Textbook.Ch02 Require Import Reciprocal.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters.

Module Ch03Approach.
Import Ch02 Ch03.
Open Scope R_scope.

Definition preimage {X Y : Type} (f : X -> Y) (V : Y -> Prop) : X -> Prop :=  (* 定义目标集合的原像 *)
  fun x => V (f x).

Definition Approaches {X Y : Type} (f : X -> Y)         (* 用原像定义趋近关系 *)
    (F : BookFilter X) (G : BookFilter Y) : Prop :=     (* F、G指定输入与输出的趋近方式 *)
  forall V : Y -> Prop, members G V -> members F (preimage f V).

Theorem real_iff {X : Type} (f : X -> R) (F : BookFilter X) (b : R) :  (* 趋于实数b的绝对值判定 *)
  Approaches f F (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> Eventually F (fun x => Rabs (f x-b) < eps).
Proof.
  split.
  - intros H eps Heps. apply (H (fun y => Rabs (y-b) < eps)).
    exists eps. split; [exact Heps |]. intros y Hy. exact Hy.  (* 选取eps作为见证，再分别证明各项要求 *)
  - intros H V [eps [Heps HV]].
    change (members F (fun x => V (f x))).
    eapply upward; [exact (H eps Heps) |].
    intros x Hx. apply HV. exact Hx.
Qed.

Theorem sequence_iff (u : nat -> R) (b : R) :           (* 数列极限的阈值判定 *)
  Approaches u tail_filter (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat -> Rabs (u n-b) < eps.
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

Theorem double_limit (a : R) :                          (* 证明二倍函数的有限极限 *)
  Approaches (fun x => 2*x) (neighborhood_filter a)
    (neighborhood_filter (2*a)).
Proof.
  apply (proj2 (real_iff _ _ _)). intros eps Heps.      (* 将极限目标转为绝对值判定 *)
  exists (eps/2). split; [lra |]. intros x Hx.          (* 选取(eps/2)作为见证，再分别证明各项要求 *)
  change (Rabs (x-a) < eps/2) in Hx.
  replace (2*x-2*a) with (2*(x-a)) by ring.             (* 用等式改写相应表达式 *)
  rewrite Rabs_mult, (Rabs_right 2); lra.  (* 用绝对值相关等式重写 *)
Qed.

Theorem reciprocal_sequence :                           (* 证明倒数数列趋于零 *)
  Approaches (fun n => 1/(INR n+1)) tail_filter (neighborhood_filter 0).
Proof.
  apply (proj2 (sequence_iff _ _)). intros eps Heps.    (* 将极限目标转为绝对值判定 *)
  destruct (eventually_reciprocal eps Heps) as [N HN].
  exists N. intros n Hn.                                (* 选取N作为见证 *)
  assert (Hpos : 0 <= 1/(INR n+1)).
  { apply Rlt_le. apply Rdiv_lt_0_compat; [lra |].      (* 以成员谓词描述集合 *)
    pose proof (pos_INR n). lra. }                      (* 把已有定理加入当前假设 *)
  pose proof (HN n Hn) as Hlt.                          (* 把已有定理加入当前假设 *)
  rewrite Rminus_0_r, Rabs_right; lra.  (* 按Rminus_0_r, Rabs_right; lra给出的等式或等价式改写 *)
Qed.

Theorem double_atTop :                                  (* 二倍函数趋于正无穷 *)
  Approaches (fun x => 2*x) upper_filter upper_filter.
Proof.
  intros V [b Hb]. exists (b/2). intros x Hx.
  apply Hb. lra.
Qed.

Theorem neg_atBot :                                     (* 负号交换两种无穷方向 *)
  Approaches (fun x => -x) lower_filter upper_filter.
Proof.
  intros V [b Hb]. exists (-b). intros x Hx.
  apply Hb. lra.
Qed.

End Ch03Approach.
