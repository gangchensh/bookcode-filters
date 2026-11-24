From Stdlib Require Import Arith Lia.

Definition EventuallyNat (P : nat -> Prop) : Prop :=    (* 定义自然数上的最终成立 *)
  exists N : nat, forall n : nat, N <= n -> P n.  (* 选取N : nat, forall n : nat, N <= n -> P n作为见证 *)

Theorem EventuallyNat_and (P Q : nat -> Prop) :         (* 最终成立对有限合取封闭 *)
  EventuallyNat P -> EventuallyNat Q ->
  EventuallyNat (fun n => P n /\ Q n).                  (* 陈述两个谓词的合取最终成立 *)
Proof.
  intros [NP HP] [NQ HQ].
  exists (Nat.max NP NQ).                               (* 选取(Nat.max NP NQ)作为见证 *)
  intros n Hn.
  split.
  - apply HP. lia.
  - apply HQ. lia.
Qed.
