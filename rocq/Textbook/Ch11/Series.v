From Stdlib Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.
Module Ch11.

(* BEGIN definition *)
Fixpoint PartialSum (a : nat -> R) (N : nat) : R :=
  match N with
  | O => 0
  | S n => PartialSum a n + a n                    (* 新增第n项，前n项保持不变 *)
  end.
Definition SeriesHasSum (a : nat -> R) (s : R) : Prop :=
  filterlim (PartialSum a) eventually (locally s).
(* END definition *)

(* BEGIN index *)
Theorem partialSum_sum_n (a : nat -> R) (n : nat) :
  PartialSum a (S n) = sum_n a n.
Proof.
  induction n as [|n IH].
  - simpl. rewrite sum_O. ring.
  - change (PartialSum a (S n) + a (S n) = sum_n a (S n)).
    rewrite IH, sum_Sn. reflexivity.               (* sum_n包括最后的第n项 *)
Qed.
(* END index *)

(* BEGIN geometric *)
Theorem partialSum_geometric (q : R) (Hq : q <> 1) (N : nat) :
  PartialSum (fun n => q^n) N = (1-q^N)/(1-q).
Proof.
  induction N as [|N IH].
  - simpl. field; lra.
  - simpl. rewrite IH. field; lra.                (* 有限几何和由归纳与代数恒等式得到 *)
Qed.
Theorem geometric_native (q : R) (Hq : Rabs q < 1) :
  is_series (fun n : nat => q^n) (1/(1-q)).
Proof.
  replace (1/(1-q)) with (/(1-q)) by (unfold Rdiv; ring).
  exact (is_series_geom q Hq).                     (* 库中的自然顺序级数收敛证书 *)
Qed.
(* END geometric *)

(* BEGIN tail *)
Theorem geometric_remainder (q : R) (Hq : q <> 1) (N : nat) :
  1/(1-q)-PartialSum (fun n => q^n) N = q^N/(1-q).
Proof. rewrite partialSum_geometric by exact Hq. field; lra. Qed.
(* END tail *)

(* BEGIN power *)
Definition NativePowerSum (c : nat -> R) (x s : R) : Prop :=
  is_pseries c x s.
(* END power *)

(* BEGIN series_bridge *)
Theorem ordered_coquelicot_iff (a : nat -> R) (s : R) :
  SeriesHasSum a s <-> is_series a s.
Proof.
  unfold SeriesHasSum, is_series. split.
  - intros H P HP. destruct (H P HP) as [N HN].
    exists N. intros n Hn.
    rewrite <- partialSum_sum_n. apply HN. lia.   (* S n越过原阈值，级数项序不变 *)
  - intros H P HP. destruct (H P HP) as [N HN].
    exists (S N). intros n Hn.
    destruct n as [|k]; [lia |].
    rewrite partialSum_sum_n. apply HN. lia.      (* 跳过零项和，恢复sum_n下标 *)
Qed.
(* END series_bridge *)
End Ch11.
