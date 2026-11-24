From Stdlib Require Import Reals.
From Textbook.Ch02 Require Import Filters.
From Textbook.Ch03 Require Import StandardFilters.
From Textbook.Ch03 Require Import Approach.
Import Ch02 Ch03 Ch03Approach.
Open Scope R_scope.

Module Ch03DefinitionExamples.
Definition SequenceLimit (u : nat -> R) (b : R) : Prop :=  (* 定义实数数列收敛 *)
  Approaches u tail_filter (neighborhood_filter b).

Theorem sequence_limit_iff (u : nat -> R) (b : R) :     (* 本书数列收敛等价于ε-N判定 *)
  SequenceLimit u b <->
  forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat -> Rabs (u n-b) < eps.
Proof.
  unfold SequenceLimit. rewrite real_iff. reflexivity.
Qed.

Theorem finite_atTop_iff (f : R -> R) (b : R) :         (* 正无穷处实数极限的ε-B判定 *)
  Approaches f upper_filter (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists B : R,
    forall x : R, B <= x ->
      Rabs (f x-b) < eps.                               (* 要求函数值与目标的距离小于上限 *)
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

Theorem finite_atBot_iff (f : R -> R) (b : R) :         (* 负无穷处实数极限的ε-B判定 *)
  Approaches f lower_filter (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists B : R,
    forall x : R, x <= B ->
      Rabs (f x-b) < eps.                               (* 要求函数值与目标的距离小于上限 *)
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

Theorem finite_neighborhood_iff (f : R -> R) (a b : R) :  (* 完整邻域趋近的ε-δ判定 *)
  Approaches f (neighborhood_filter a) (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists delta : R, 0 < delta /\
    forall x : R, Rabs (x-a) < delta ->
      Rabs (f x-b) < eps.                               (* 要求函数值与目标的距离小于上限 *)
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

Definition ContinuousAtPoint (f : R -> R) (a : R) : Prop :=  (* 用邻域滤子定义函数在一点连续 *)
  Approaches f (neighborhood_filter a) (neighborhood_filter (f a)).

Theorem continuousAtPoint_iff (f : R -> R) (a : R) :    (* 连续性等价于传统ε-δ判定 *)
  ContinuousAtPoint f a <->
  forall eps : R, 0 < eps -> exists delta : R, 0 < delta /\
    forall x : R, Rabs (x-a) < delta -> Rabs (f x-f a) < eps.
Proof. exact (finite_neighborhood_iff f a (f a)). Qed.  (* 在邻域极限判定中代入b=f(a) *)

Theorem finite_within_iff (f : R -> R) (S : R -> Prop) (a b : R) :  (* 集合内极限的ε-δ判定 *)
  Approaches f (near_within a S) (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists delta : R, 0 < delta /\
    forall x : R, Rabs (x-a) < delta -> S x ->
      Rabs (f x-b) < eps.                               (* 要求函数值与目标的距离小于上限 *)
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

Theorem finite_punctured_iff (f : R -> R) (a b : R) :   (* 去心函数极限的ε-δ判定 *)
  Approaches f (punctured a) (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists delta : R, 0 < delta /\
    forall x : R, Rabs (x-a) < delta -> x <> a ->
      Rabs (f x-b) < eps.                               (* 要求函数值与目标的距离小于上限 *)
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

Theorem finite_right_iff (f : R -> R) (a b : R) :       (* 右极限的ε-δ判定 *)
  Approaches f (right_near a) (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists delta : R, 0 < delta /\
    forall x : R, Rabs (x-a) < delta -> a < x ->
      Rabs (f x-b) < eps.                               (* 要求函数值与目标的距离小于上限 *)
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

Theorem finite_left_iff (f : R -> R) (a b : R) :        (* 左极限的ε-δ判定 *)
  Approaches f (left_near a) (neighborhood_filter b) <->
  forall eps : R, 0 < eps -> exists delta : R, 0 < delta /\
    forall x : R, Rabs (x-a) < delta -> x < a ->
      Rabs (f x-b) < eps.                               (* 要求函数值与目标的距离小于上限 *)
Proof. rewrite real_iff. reflexivity. Qed.              (* 用real_iff展开目标邻域，再展开源滤子 *)

End Ch03DefinitionExamples.
