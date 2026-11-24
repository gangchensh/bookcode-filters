From Stdlib Require Import Arith Reals.
Open Scope R_scope.

(* BEGIN division *)
Example nat_half : (1 / 2 = 0)%nat.              (* 自然数除法取整数商 *)
Proof. reflexivity. Qed.

Example real_div_zero : 1 / 0 = 0.               (* 实数标准库约定除以0为0 *)
Proof.
  unfold Rdiv. rewrite Rinv_0, Rmult_0_r.
  reflexivity.
Qed.

Theorem real_div_self (x : R) (Hx : x <> 0) :    (* 非零实数除以自身等于1 *)
  x / x = 1.
Proof. apply Rdiv_diag. exact Hx. Qed.
(* END division *)

(* BEGIN function *)
Definition next_nat (n : nat) : nat := S n.      (* 自然数的后继函数 *)
Definition is_positive_nat (n : nat) : Prop := (0 < n)%nat.

Example next_two : next_nat 2 = 3%nat.
Proof. reflexivity. Qed.

Example three_positive : is_positive_nat 3.
Proof. unfold is_positive_nat. apply Nat.lt_0_succ. Qed.
(* END function *)

(* BEGIN conjunction *)
Theorem swap_and (P Q : Prop) :                 (* 交换合取中的两个命题 *)
  P /\ Q -> Q /\ P.
Proof.
  intros [HP HQ].                               (* 取出P与Q的证明 *)
  split.                                        (* 分别证明Q和P *)
  - exact HQ.
  - exact HP.
Qed.
(* END conjunction *)

(* BEGIN quantifiers *)
Theorem threshold_example :                    (* 选择阈值100后保持下界 *)
  exists N : nat, forall n : nat,
    (N <= n)%nat -> (100 <= n)%nat.
Proof.
  exists 100%nat.                               (* 取N = 100 *)
  intros n Hn.                                  (* Hn : 100 <= n *)
  exact Hn.
Qed.
(* END quantifiers *)

(* BEGIN sets *)
Definition Upper100 : nat -> Prop :=            (* 自然数中不小于100的点集 *)
  fun n => (100 <= n)%nat.

Theorem upper100_mem (n : nat) :
  Upper100 n <-> (100 <= n)%nat.
Proof. unfold Upper100. reflexivity. Qed.

Theorem inter_left (A B : nat -> Prop) :        (* 交集包含在左边的集合内 *)
  forall n, A n /\ B n -> A n.
Proof. intros n [HA HB]. exact HA. Qed.
(* END sets *)

(* BEGIN proof_term *)
Definition swap_and_term (P Q : Prop) : P /\ Q -> Q /\ P :=
  fun h => conj (proj2 h) (proj1 h).
(* END proof_term *)

(* BEGIN record *)
Record ClosedBounds : Type := {                 (* 两个实数端点及其顺序证明 *)
  lower : R;
  upper : R;
  ordered : lower <= upper
}.

Definition unit_bounds : ClosedBounds :=         (* 构造端点为0和1的记录 *)
  {| lower := 0; upper := 1; ordered := Rle_0_1 |}.
(* END record *)
