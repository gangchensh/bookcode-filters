From Stdlib Require Import Arith Lia.

Definition EventuallyNat (P : nat -> Prop) : Prop :=    (* 定义自然数上的最终成立 *)
  exists N : nat,                                       (* 断言存在一个合适的见证 *)
    forall n : nat,
      N <= n -> P n.

Example eventually_ge_100 :                             (* 自然数最终不小于100 *)
  EventuallyNat (fun n => 100 <= n).                    (* 陈述 100 不大于 n 最终成立 *)
Proof.
  exists 100.                                           (* 选取100作为见证 *)
  intros n Hn.
  exact Hn.
Qed.

Theorem EventuallyNat_and                               (* 最终成立对有限合取封闭 *)
    (P Q : nat -> Prop) :
    EventuallyNat P ->
    EventuallyNat Q ->
    EventuallyNat (fun n => P n /\ Q n).                (* 陈述两个谓词的合取最终成立 *)
Proof.
  intros [NP HP] [NQ HQ].
  exists (Nat.max NP NQ).                               (* 选取(Nat.max NP NQ)作为见证 *)
  intros n Hn.
  split.
  - apply HP.
    lia.                                                (* 核对自然数或整数算术 *)
  - apply HQ.
    lia.                                                (* 核对自然数或整数算术 *)
Qed.

Definition Tail (N : nat) : nat -> Prop :=              (* 用谓词表示尾集 *)
  fun n => N <= n.


Theorem EventuallyNat_mono                              (* 将较强断言传到较弱断言 *)
    (P Q : nat -> Prop) :
    EventuallyNat P ->
    (forall n, P n -> Q n) ->
    EventuallyNat Q.                                    (* 需要证明 Q 最终成立 *)
Proof.
  intros [N HN] HPQ.
  exists N.                                             (* 选取N作为见证 *)
  intros n Hn.
  exact (HPQ n (HN n Hn)).
Qed.

Example eventually_weaker_bound (u : nat -> nat)        (* 由最终大于1000推出最终大于100 *)
    (H : EventuallyNat (fun n => 1000 < u n)) :
    EventuallyNat (fun n => 100 < u n).                 (* 需要证明 u 的值最终大于 100 *)
Proof.
  apply (EventuallyNat_mono
    (fun n => 1000 < u n) (fun n => 100 < u n) H).
  intros n Hn.
  lia.                                                  (* 核对自然数或整数算术 *)
Qed.
