From Stdlib Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.
Module Ch13.

(* BEGIN iterated *)
Definition IsIterated (f : R -> R -> R) (a b c d I : R) : Prop :=
  (forall x, Rmin a b <= x <= Rmax a b -> ex_RInt (f x) c d) /\
  is_RInt (fun x => RInt (f x) c d) a b I.         (* 内层存在，外层积分等于I *)
(* END iterated *)

(* BEGIN affine_helper *)
Lemma integral_affine (c a b : R) :
  is_RInt (fun t : R => c*t) a b (c*b*b/2-c*a*a/2).
Proof.
  apply (is_RInt_derive (fun t : R => c*t*t/2) (fun t : R => c*t)).
  - intros x Hx. auto_derive; nra.
  - intros x Hx. apply (ex_derive_continuous (fun t : R => c*t) x).
    exists c. auto_derive; nra.
Qed.
(* END affine_helper *)

(* BEGIN rectangle *)
Theorem rectangle_product :
  IsIterated (fun x y : R => x*y) 0 1 0 1 (1/4).
Proof.
  split.
  - intros x Hx. exists (x/2).
    replace (x/2) with (x*1*1/2-x*0*0/2) by field.
    apply integral_affine.                       (* 每条竖直切片的积分存在 *)
  - assert (Hslice : forall x, RInt (fun y : R => x*y) 0 1 = x/2).
    { intro x. apply is_RInt_unique.
      replace (x/2) with (x*1*1/2-x*0*0/2) by field.
      apply integral_affine. }
    eapply is_RInt_ext with (f := fun x : R => (1/2)*x).
    + intros x Hx. rewrite Hslice.
      unfold Rdiv. rewrite Rmult_1_l. apply Rmult_comm.
    + replace (1/4) with ((1/2)*1*1/2-(1/2)*0*0/2) by field.
      apply integral_affine.                     (* 外层积分为1/4 *)
Qed.
(* END rectangle *)

(* BEGIN mass *)
Theorem triangle_mass :
  is_RInt (fun x : R => RInt (fun _y : R => 2*x) 0 (1-x)) 0 1 (1/3).
Proof.
  eapply is_RInt_ext with (f := fun x : R => (1-x)*(2*x)).
  - intros x Hx. rewrite RInt_const. cbn. ring.    (* 内层是密度乘切片长度 *)
  - replace (1/3) with ((1*1-2*1*1*1/3)-(0*0-2*0*0*0/3)) by field.
    apply (is_RInt_derive (fun t : R => t*t-2*t*t*t/3)
      (fun t : R => (1-t)*(2*t))).
    + intros x Hx. auto_derive; nra.
    + intros x Hx. apply (ex_derive_continuous (fun t : R => (1-t)*(2*t)) x).
      exists (2-4*x). auto_derive; nra.
Qed.
(* END mass *)

(* BEGIN jacobian *)
Theorem polar_determinant (r theta : R) :
  cos theta*(r*cos theta)-(-r*sin theta)*sin theta = r.
Proof.
  replace (cos theta*(r*cos theta)-(-r*sin theta)*sin theta)
    with (r*(Rsqr (sin theta)+Rsqr (cos theta))) by (unfold Rsqr; ring).
  rewrite sin2_cos2. ring.
Qed.                                            (* 面积因子再取绝对值 *)
(* END jacobian *)

(* BEGIN disk *)
Theorem polar_disk_area (r : R) :
  is_RInt (fun _theta : R => RInt (fun t : R => t) 0 r)
    0 (2*PI) (PI*r*r).
Proof.
  assert (Hradial : RInt (fun t : R => t) 0 r = r*r/2).
  { apply is_RInt_unique.
    replace (r*r/2) with (1*r*r/2-1*0*0/2) by field.
    eapply is_RInt_ext with (f := fun t : R => 1*t).
    - intros t Ht. exact (Rmult_1_l t).
    - apply integral_affine. }
  rewrite Hradial.
  replace (PI*r*r) with ((2*PI-0)*(r*r/2)) by field.
  exact (is_RInt_const 0 (2*PI) (r*r/2)).          (* 对全部角度累加相同的径向积分 *)
Qed.
(* END disk *)

(* BEGIN work *)
Theorem circle_work :
  is_RInt (fun t : R => (-sin t)*(-sin t)+cos t*cos t)
    0 (2*PI) (2*PI).
Proof.
  eapply is_RInt_ext with (f := fun _ : R => 1).
  - intros t Ht. pose proof (sin2_cos2 t). unfold Rsqr in H. nra.
  - replace (2*PI) with ((2*PI-0)*1) at 2 by ring.
    exact (is_RInt_const 0 (2*PI) 1).             (* 逆时针一周的功为2π *)
Qed.
(* END work *)

(* BEGIN flux *)
Theorem plane_flux :
  is_RInt (fun _u : R => RInt (fun _v : R => 3) 0 1) 0 1 3.
Proof.
  assert (Hinner : RInt (fun _v : R => 3) 0 1 = 3).
  { rewrite RInt_const. change ((1-0)*(3:R)=3). ring. }
  rewrite Hinner.
  pose proof (is_RInt_const 0 1 (3:R)) as Hconst.
  change (is_RInt (fun _ : R => 3) 0 1 ((1-0)*3)) in Hconst.
  replace ((1-0)*3) with (3:R) in Hconst by ring.
  exact Hconst.                                  (* 向上法向量与向量场的内积为3 *)
Qed.
(* END flux *)
End Ch13.
