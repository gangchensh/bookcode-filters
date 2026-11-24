From Stdlib Require Import Reals Psatz.
Open Scope R_scope.

(* BEGIN exact *)
Theorem reciprocal_identity (h : R) (Hh : 1+h <> 0) :
  1/(1+h) - (1-h+h*h) = -(h*h*h)/(1+h).
Proof. field; assumption. Qed.
(* END exact *)

(* BEGIN cubic *)
Theorem cubic_expansion (a h : R) :
  (a+h)^3 = a^3 + 3*a^2*h + 3*a*h^2 + h^3.
Proof. ring. Qed.

Theorem cubic_remainder (a h eta : R)
  (Hh : Rabs h <= eta) :
  Rabs ((a+h)^3-(a^3+3*a^2*h+3*a*h^2)) <= eta^3.
Proof.
  assert (Heta : 0 <= eta) by (pose proof (Rabs_pos h); lra).
  replace ((a+h)^3-(a^3+3*a^2*h+3*a*h^2)) with (h*h*h) by ring.
  rewrite !Rabs_mult. pose proof (Rabs_pos h).
  replace (eta^3) with (eta*eta*eta) by ring.
  assert (Hs : Rabs h * Rabs h <= eta*eta).
  { apply Rmult_le_compat; assumption. }
  apply Rmult_le_compat; try assumption.
  apply Rmult_le_pos; assumption.
Qed.
(* END cubic *)

(* BEGIN littleo *)
Definition BookLittleO (r g : R -> R)
  (F : (R -> Prop) -> Prop) : Prop :=
  forall eps, 0 < eps ->
    F (fun x => Rabs (r x) <= eps * Rabs (g x)).
(* END littleo *)

(* BEGIN cubic_scale *)
Theorem cubic_scale_bound (r h K eps : R)
  (Hsmall : K * Rabs h <= eps)
  (Hr : Rabs r <= K * (Rabs h)^3) :
  Rabs r <= eps * (Rabs h)^2.
Proof.
  eapply Rle_trans; [exact Hr |].                 (* 先使用已有的三次余项界 *)
  replace (K*(Rabs h)^3) with
    ((K*Rabs h)*(Rabs h)^2) by ring.             (* 分出K乘|h|作为系数 *)
  apply Rmult_le_compat_r.
  - pose proof (Rle_0_sqr (Rabs h)). unfold Rsqr in *. nra.
  - exact Hsmall.                               (* 系数已经不超过eps *)
Qed.
(* END cubic_scale *)

(* BEGIN bigo *)
Definition BookBigO (r g : R -> R)
  (F : (R -> Prop) -> Prop) : Prop :=
  exists C, 0 <= C /\
    F (fun x => Rabs (r x) <= C * Rabs (g x)).
(* END bigo *)
