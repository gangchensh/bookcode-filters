From Stdlib Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* BEGIN constant *)
Theorem integral_constant (c a b : R) :
  is_RInt (fun _ => c) a b ((b-a)*c).
Proof. exact (is_RInt_const a b c). Qed.
(* END constant *)

(* BEGIN primitive *)
Theorem primitive_integral (F f : R -> R) (a b : R)
  (Hd : forall x, Rmin a b <= x <= Rmax a b -> is_derive F x (f x))
  (Hc : forall x, Rmin a b <= x <= Rmax a b -> continuous f x) :
  is_RInt f a b (F b-F a).
Proof. exact (is_RInt_derive F f a b Hd Hc). Qed.
(* END primitive *)

(* BEGIN square *)
Theorem integral_square : is_RInt (fun x : R => x*x) 0 1 (1/3).
Proof.
  replace (1/3) with ((1*1*1/3)-(0*0*0/3)) by field.
  apply (is_RInt_derive (fun x : R => x*x*x/3) (fun x : R => x*x)).
  - intros x Hx.
    auto_derive; nra.
  - intros x Hx.
    apply (ex_derive_continuous (fun y : R => y*y) x).
    exists (x+x). auto_derive; try exact I; ring.
Qed.
(* END square *)

(* BEGIN filter_definition *)
Theorem riemann_filter_iff (f : R -> R) (a b I : R) :
  is_RInt f a b I <->
  filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd))
    (Riemann_fine a b) (locally I).
Proof. reflexivity. Qed.                        (* 展开库中积分的细分极限定义 *)
(* END filter_definition *)

(* BEGIN adjacent *)
Theorem integral_adjacent (f : R -> R) (a c b I J : R)
  (Hleft : is_RInt f a c I) (Hright : is_RInt f c b J) :
  is_RInt f a b (I+J).
Proof.
  exact (is_RInt_Chasles f a c b I J Hleft Hright).
Qed.
(* END adjacent *)
