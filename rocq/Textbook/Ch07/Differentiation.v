From Stdlib Require Import Reals Psatz.
From Textbook.Ch06 Require Import Derivatives.
Open Scope R_scope.

(* BEGIN product *)
Theorem product_rule (f g : R -> R) (a df dg : R)
  (Hf : HasDerivative f a df) (Hg : HasDerivative g a dg) :
  HasDerivative (fun x => f x * g x) a (df*g a+f a*dg).
Proof.
  apply (proj2 (derivative_standard _ _ _)).
  apply derivable_pt_lim_mult.
  - apply (proj1 (derivative_standard _ _ _)). exact Hf.
  - apply (proj1 (derivative_standard _ _ _)). exact Hg.
Qed.
(* END product *)

(* BEGIN chain *)
Theorem chain_rule (f g : R -> R) (a df dg : R)
  (Hf : HasDerivative f a df) (Hg : HasDerivative g (f a) dg) :
  HasDerivative (fun x => g (f x)) a (dg*df).
Proof.
  apply (proj2 (derivative_standard _ _ _)).
  eapply derivable_pt_lim_comp.
  - apply (proj1 (derivative_standard _ _ _)). exact Hf.
  - apply (proj1 (derivative_standard _ _ _)). exact Hg.
Qed.
(* END chain *)

(* BEGIN mean_value *)
Theorem mean_value (f df : R -> R) (a b : R)
  (Hab : a < b)
  (Hd : forall x, a <= x <= b -> derivable_pt_lim f x (df x)) :
  exists c, f b-f a = df c*(b-a) /\ a < c < b.
Proof. exact (MVT_cor2 f df a b Hab Hd). Qed.
(* END mean_value *)

(* BEGIN design *)
Definition cost (x : R) := (x-3)*(x-3)+2.

Theorem cost_minimum (x : R) : 2 <= cost x.
Proof.
  unfold cost. replace 2 with (0+2) at 1 by ring.
  apply Rplus_le_compat_r. exact (Rle_0_sqr (x-3)).
Qed.

Theorem cost_eq_minimum (x : R) : cost x = 2 <-> x = 3.
Proof.
  unfold cost. split.
  - intro H. assert (Hs : (x-3)*(x-3)=0) by lra.
    apply Rmult_integral in Hs. destruct Hs; lra.
  - intro H. subst x. ring.
Qed.
(* END design *)

(* BEGIN worked_chain *)
Theorem fourth_power_derivative (a : R) :
  HasDerivative (fun x => (x*x)*(x*x)) a (4*a^3).
Proof.
  replace (4*a^3) with ((2*(a*a))*(2*a)) by ring.
  apply (chain_rule (fun x : R => x*x)
    (fun x : R => x*x) a (2*a) (2*(a*a))).         (* 中间值为a乘a *)
  - exact (derivative_square a).                  (* 内层平方在a处求导 *)
  - exact (derivative_square (a*a)).              (* 外层平方在a²处求导 *)
Qed.
(* END worked_chain *)
