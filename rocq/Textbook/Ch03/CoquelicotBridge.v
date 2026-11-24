From Stdlib Require Import Reals.
From Coquelicot Require Import Coquelicot.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.
Import Ch02 Ch03 Ch03Approach.
Open Scope R_scope.

Lemma sequence_coquelicot_iff (u : nat -> R) (b : R) :  (* Coquelicot数列收敛等价于ε-N判定 *)
  is_lim_seq u (Finite b) <->
  forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat -> Rabs (u n-b) < eps.
Proof.
  rewrite <- is_lim_seq_spec.                           (* 按<- is_lim_seq_spec给出的等式或等价式改写 *)
  unfold is_lim_seq'. cbn.
  split.
  - intros H eps Heps. exact (H (mkposreal eps Heps)).
  - intros H eps. exact (H (pos eps) (cond_pos eps)).
Qed.

Lemma sequence_filterlim_iff (u : nat -> R) (b : R) :   (* filterlim数列收敛等价于ε-N判定 *)
  filterlim u eventually (locally b) <->
  forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat -> Rabs (u n-b) < eps.
Proof.
  change (is_lim_seq u (Finite b) <->
    forall eps : R, 0 < eps -> exists N : nat,
      forall n : nat, (N <= n)%nat -> Rabs (u n-b) < eps).
  apply sequence_coquelicot_iff.                        (* 使用已证明的is_lim_seq ε-N判定 *)
Qed.

Lemma sequence_limit_coquelicot (u : nat -> R) (b : R) :  (* 本书数列收敛等价于Coquelicot数列收敛 *)
  Approaches u tail_filter (neighborhood_filter b) <-> is_lim_seq u (Finite b).
Proof.
  rewrite sequence_iff, sequence_coquelicot_iff. reflexivity.  (* 把两边都改写成相同ε-N公式 *)
Qed.

Lemma filtermap_members_iff {X Y : Type} (f : X -> Y)                           (* Coquelicot像滤子的成员由原像判定 *)
    (F : BookFilter X) (V : Y -> Prop) :                                        (* F是源滤子，V是目标集合的成员谓词 *)
  filtermap f (members F) V <->
    members F (preimage f V).                                                   (* V属于像滤子↔V的原像属于F *)
Proof. reflexivity. Qed.                                                        (* 展开定义后两边相同 *)

Lemma approaches_coquelicot_iff                         (* 本书趋近关系等价于Coquelicot的filterlim *)
    {X Y : Type} (f : X -> Y)
    (F : BookFilter X) (G : BookFilter Y) :             (* F、G指定输入与输出的趋近方式 *)
  Approaches f F G <-> filterlim f (members F) (members G).
Proof. reflexivity. Qed.                                (* 展开定义后两边相同 *)
