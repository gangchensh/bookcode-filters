From Stdlib Require Import Reals Lra Lia Psatz Classical.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.
From Textbook.Ch03 Require Import LimitRules.

Module Ch05.
Import Ch02 Ch03 Ch03Approach.
Open Scope R_scope.

Definition Converges (u : nat -> R) (l : R) : Prop :=  (* 复用第3章的滤子数列极限 *)
  Approaches u tail_filter (neighborhood_filter l).

Definition BoundedSeq (u : nat -> R) : Prop :=         (* 一个共同常数控制全部项 *)
  exists M : R, forall n : nat, Rabs (u n) <= M.

Definition CauchySequence (u : nat -> R) : Prop :=     (* 两个充分大下标共用同一阈值 *)
  forall eps : R, 0 < eps -> exists N : nat,
    forall m n : nat, (N <= m)%nat -> (N <= n)%nat -> Rabs (u m-u n) < eps.

Theorem converges_iff (u : nat -> R) (l : R) :         (* 调用已有的数列判定 *)
  Converges u l <-> forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat -> Rabs (u n-l) < eps.
Proof. exact (sequence_iff u l). Qed.

Theorem eventually_positive (u : nat -> R) (l : R) :   (* 正极限使数列最终为正 *)
  Converges u l -> 0 < l -> Eventually tail_filter (fun n => 0 < u n).
Proof.
  intros Hu Hl.
  destruct ((proj1 (converges_iff u l)) Hu (l/2)) as [N HN]; [lra |].
  exists N. intros n Hn.
  specialize (HN n Hn).
  pose proof (Rle_abs (l-u n)) as Hlower.
  rewrite Rabs_minus_sym in Hlower. lra.             (* l-u_n≤|u_n-l|<l/2 *)
Qed.

Definition StrictIndex (phi : nat -> nat) : Prop :=   (* 子列索引严格递增 *)
  forall m n : nat, (m < n)%nat -> (phi m < phi n)%nat.

Theorem index_ge (phi : nat -> nat) :                 (* 严格递增索引满足n≤phi(n) *)
  StrictIndex phi -> forall n : nat, (n <= phi n)%nat.
Proof.
  intros Hphi n. induction n as [| n IH]; [lia |].
  pose proof (Hphi n (S n) (Nat.lt_succ_diag_r n)). lia.
Qed.

Theorem subsequence_index (phi : nat -> nat) :        (* 子列索引保持充分大 *)
  StrictIndex phi -> Approaches phi tail_filter tail_filter.
Proof.
  intros Hphi V [N HN]. exists N. intros n Hn.
  apply HN. pose proof (index_ge phi Hphi n). lia.    (* N≤n≤phi(n) *)
Qed.

Theorem converges_subsequence (u : nat -> R) (l : R) (phi : nat -> nat) :
  Converges u l -> StrictIndex phi ->                 (* 子列继承同一个极限 *)
  Converges (fun n => u (phi n)) l.
Proof.
  intros Hu Hphi.
  exact (Ch03Rules.approaches_comp phi u _ _ _
    (subsequence_index phi Hphi) Hu).                (* 复用第3章的复合定理 *)
Qed.

Definition IsLeastUpperBound (u : nat -> R) (l : R) : Prop :=
  (forall n : nat, u n <= l) /\                     (* l是所有项的上界 *)
  (forall b : R, (forall n : nat, u n <= b) -> l <= b). (* l不超过任何上界 *)

Theorem monotone_limit_of_lub (u : nat -> R) (l : R) :
  (forall m n : nat, (m <= n)%nat -> u m <= u n) ->  (* 数列非递减 *)
  IsLeastUpperBound u l -> Converges u l.
Proof.
  intros Hmono [Hupper Hleast].
  apply (proj2 (converges_iff u l)). intros eps Heps.
  assert (Hnot : ~ forall n : nat, u n <= l-eps).
  { intro H. specialize (Hleast (l-eps) H). lra. }   (* l-eps不能是上界 *)
  apply not_all_ex_not in Hnot. destruct Hnot as [N HN].
  exists N. intros n Hn.
  pose proof (Hmono N n Hn). pose proof (Hupper n).
  rewrite Rabs_left1; lra.                           (* |u_n-l|=l-u_n<eps *)
Qed.

Theorem monotone_bounded_converges (u : nat -> R) :
  (forall m n : nat, (m <= n)%nat -> u m <= u n) ->
  (exists b : R, forall n : nat, u n <= b) ->
  exists l : R, Converges u l.                       (* 实数上确界保证极限存在 *)
Proof.
  intros Hmono [b Hb].
  set (E := fun x : R => exists n : nat, x = u n).
  assert (HE : bound E).
  { exists b. intros x [n Hx]. subst x. exact (Hb n). }
  assert (Hnonempty : exists x : R, E x).
  { exists (u 0%nat). exists 0%nat. reflexivity. }
  destruct (completeness E HE Hnonempty) as [l [Hup Hleast]].
  exists l. apply (monotone_limit_of_lub u l Hmono). split.
  - intros n. apply Hup. exists n. reflexivity.
  - intros c Hc. apply Hleast. intros x [n Hx]. subst x. exact (Hc n).
Qed.

Theorem convergent_cauchy (u : nat -> R) (l : R) :    (* 收敛使两个尾项彼此接近 *)
  Converges u l -> CauchySequence u.
Proof.
  intros Hu eps Heps.
  destruct ((proj1 (converges_iff u l)) Hu (eps/2)) as [N HN]; [lra |].
  exists N. intros m n Hm Hn.
  pose proof (HN m Hm) as Hml. pose proof (HN n Hn) as Hnl.
  replace (u m-u n) with ((u m-l)+(l-u n)) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang |].
  rewrite (Rabs_minus_sym l (u n)). lra.             (* 两个eps/2界相加小于eps *)
Qed.

End Ch05.
