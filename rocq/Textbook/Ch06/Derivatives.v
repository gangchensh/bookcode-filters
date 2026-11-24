From Stdlib Require Import Reals Psatz.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.
Import Ch02 Ch03 Ch03Approach.
Open Scope R_scope.

(* BEGIN definition *)
Definition HasDerivative (f : R -> R) (a d : R) : Prop :=
  Approaches (fun x => (f x-f a)/(x-a))
    (punctured a) (neighborhood_filter d).
(* END definition *)

(* BEGIN standard_bridge *)
Theorem derivative_standard (f : R -> R) (a d : R) :
  HasDerivative f a d <-> derivable_pt_lim f a d.
Proof.
  unfold HasDerivative. rewrite (real_iff _ _ _).
  split.
  - intros H eps Heps. destruct (H eps Heps) as [r [Hr Hloc]].
    exists (mkposreal r Hr).                       (* 将正半径打包为posreal *)
    intros h Hh Hsmall.
    specialize (Hloc (a+h)).
    unfold Neighborhoods.eps_neighborhood in Hloc.
    replace (a+h-a) with h in Hloc by ring.
    apply Hloc; [exact Hsmall | lra].              (* 输入非零增量对应去心点 *)
  - intros H eps Heps. destruct (H eps Heps) as [r Hloc].
    exists (pos r). split; [exact (cond_pos r) |].
    intros x Hsmall Hne.
    change (Rabs (x-a) < r) in Hsmall.
    specialize (Hloc (x-a)).
    replace (a+(x-a)) with x in Hloc by ring.
    apply Hloc; [lra | exact Hsmall].
Qed.
(* END standard_bridge *)

(* BEGIN constants *)
Theorem derivative_const (c a : R) :               (* 常值差商为0 *)
  HasDerivative (fun _ => c) a 0.
Proof.
  unfold HasDerivative. apply (proj2 (real_iff _ _ _)).
  intros eps Heps. exists 1. split; [lra |].
  intros x Hx Hne.
  replace (c-c) with 0 by ring.
  unfold Rdiv. rewrite Rmult_0_l, Rminus_0_r, Rabs_R0.
  exact Heps.
Qed.
(* END constants *)

(* BEGIN square *)
Theorem derivative_square (a : R) :                (* 平方差商化为x+a *)
  HasDerivative (fun x => x*x) a (2*a).
Proof.
  unfold HasDerivative. apply (proj2 (real_iff _ _ _)).
  intros eps Heps. exists eps. split; [exact Heps |].
  intros x Hx Hne. change (Rabs (x-a) < eps) in Hx.
  change (x <> a) in Hne.
  assert (Hden : x-a <> 0) by lra.
  replace ((x*x-a*a)/(x-a)-2*a) with (x-a).
  - exact Hx.
  - field; assumption.
Qed.
(* END square *)

(* BEGIN affine *)
Theorem derivative_affine (m b a : R) :            (* 仿射差商在去心范围恒为m *)
  HasDerivative (fun x => m*x+b) a m.
Proof.
  unfold HasDerivative. apply (proj2 (real_iff _ _ _)).
  intros eps Heps. exists 1. split; [lra |].
  intros x Hx Hne. change (x <> a) in Hne.
  assert (Hden : x-a <> 0) by lra.                 (* 去心条件保证差商可约分 *)
  replace ((m*x+b-(m*a+b))/(x-a)-m) with 0.
  - rewrite Rabs_R0. exact Heps.
  - field; assumption.
Qed.
(* END affine *)

(* BEGIN remainder *)
Theorem square_remainder (a h : R) :               (* 平方函数的精确线性余项 *)
  (a+h)*(a+h) - (a*a+(2*a)*h) = h*h.
Proof. ring. Qed.

Theorem square_error_bound (a h eta : R)
  (Heta : 0 <= eta) (Hh : Rabs h <= eta) :         (* 将输入变化界传递到余项 *)
  Rabs ((a+h)*(a+h)-(a*a+(2*a)*h)) <= eta*eta.
Proof.
  rewrite square_remainder, Rabs_mult.
  pose proof (Rabs_pos h). nra.
Qed.
(* END remainder *)

(* BEGIN reciprocal_error *)
Theorem reciprocal_remainder (a h : R)
  (Ha : a <> 0) (Hah : a+h <> 0) :                (* 线性模型与倒数值的精确差 *)
  1/(a+h) - (1/a-h/(a*a)) = h*h/((a*a)*(a+h)).
Proof. field; split; assumption. Qed.
(* END reciprocal_error *)
