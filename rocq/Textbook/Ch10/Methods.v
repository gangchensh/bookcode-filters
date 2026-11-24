From Stdlib Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

Module Ch10.
(* BEGIN polynomial *)
Theorem polynomial_substitution :
  is_RInt (fun x : R => 2*x*(x*x+1)) 0 1 (3/2).
Proof.
  replace (3/2) with (((1*1+1)*(1*1+1)/2)-((0*0+1)*(0*0+1)/2)) by field.
  apply (is_RInt_derive
    (fun x : R => (x*x+1)*(x*x+1)/2) (fun x : R => 2*x*(x*x+1))).
  - intros x Hx. auto_derive; nra.                   (* 原函数导数为2x(x²+1) *)
  - intros x Hx. apply (ex_derive_continuous (fun y : R => 2*y*(y*y+1)) x).
    exists (6*x*x+2). auto_derive; nra.             (* 多项式可导，因而连续 *)
Qed.
(* END polynomial *)

(* BEGIN xexp *)
Theorem integral_x_exp : is_RInt (fun x : R => x*exp x) 0 1 1.
Proof.
  assert (Hprim : is_RInt (fun x : R => x*exp x) 0 1
    ((1-1)*exp 1-(0-1)*exp 0)).
  { apply (is_RInt_derive (fun x : R => (x-1)*exp x) (fun x : R => x*exp x)).
    - intros x Hx. auto_derive; nra.                (* 乘积求导后合并为x exp(x) *)
    - intros x Hx. apply (ex_derive_continuous (fun y : R => y*exp y) x).
      exists (exp x+x*exp x). auto_derive; nra. }
  replace ((1-1)*exp 1-(0-1)*exp 0) with 1 in Hprim by (rewrite exp_0; ring).
  exact Hprim.
Qed.
(* END xexp *)

(* BEGIN improper *)
Definition ImproperRight (f : R -> R) (a L : R) : Prop :=
  (forall T, a <= T -> ex_RInt f a T) /\
  filterlim (fun T => RInt f a T) (Rbar_locally p_infty) (locally L).
(* END improper *)

(* BEGIN decay *)
Theorem decay_truncation (T : R) :
  is_RInt (fun x : R => exp (-x)) 0 T (1-exp (-T)).
Proof.
  replace (1-exp (-T)) with (-exp (-T)-(-exp (-0)))
    by (replace (-0) with 0 by ring; rewrite exp_0; ring).
  apply (is_RInt_derive (fun x : R => -exp (-x)) (fun x : R => exp (-x))).
  - intros x Hx. auto_derive; nra.                  (* 链式法则与两个负号相消 *)
  - intros x Hx. apply (ex_derive_continuous (fun y : R => exp (-y)) x).
    exists (-exp (-x)). auto_derive; nra.
Qed.
(* END decay *)

(* BEGIN certificate *)
Theorem total_error_budget (I A Q disc tail : R)
  (Ht : Rabs (I-A) <= tail) (Hd : Rabs (A-Q) <= disc) :
  Rabs (I-Q) <= tail+disc.
Proof.
  replace (I-Q) with ((I-A)+(A-Q)) by ring.
  eapply Rle_trans; [apply Rabs_triang | lra].      (* 合并截断余量与求积误差 *)
Qed.
(* END certificate *)
(* BEGIN generalized *)
Definition LibraryImproperRight (f : R -> R) (a L : R) : Prop :=
  is_RInt_gen f (at_point a) (Rbar_locally p_infty) L.
(* END generalized *)

(* BEGIN library_bridge *)
Theorem improper_library_iff (f : R -> R) (a L : R)
  (Hlocal : forall T, a <= T -> ex_RInt f a T) :
  ImproperRight f a L <-> LibraryImproperRight f a L.
(* END library_bridge *)
Proof.
  unfold ImproperRight, LibraryImproperRight, is_RInt_gen,
    filterlimi, filter_le, filtermapi, filterlim, filtermap.
  split.
  - intros [_ Hlim] P HP.
    specialize (Hlim P HP).
    destruct Hlim as [M HM].
    apply (Filter_prod _ _ _ (fun x => x = a)
      (fun T => a <= T /\ P (RInt f a T))).
    + reflexivity.
    + exists (Rmax M a). intros T HT. split.
      * exact (Rle_trans a (Rmax M a) T (Rmax_r M a) (Rlt_le _ _ HT)).
      * apply HM. exact (Rle_lt_trans M (Rmax M a) T (Rmax_l M a) HT).
    + intros x T Hx [HT HPval]. subst x.
      exists (RInt f a T). split; [exact (RInt_correct f a T (Hlocal T HT)) | exact HPval].
  - intro H. split; [exact Hlocal |].
    intros P HP. specialize (H P HP).
    destruct H as [Q R HQ HR Hpair].
    destruct HR as [M HM]. exists M. intros T HT.
    destruct (Hpair a T HQ (HM T HT)) as [I [HI HPval]].
    rewrite (is_RInt_unique f a T I HI). exact HPval.
Qed.


(* BEGIN exponential_limit *)
Theorem exponential_improper :
  ImproperRight (fun x : R => exp (-x)) 0 1.
Proof.
  split.
  - intros T HT. exists (1-exp (-T)). apply decay_truncation.
  - assert (Hneg : is_lim (fun x : R => -x) p_infty m_infty).
    { exact (is_lim_opp (fun x : R => x) p_infty p_infty (is_lim_id p_infty)). }
    assert (He : is_lim (fun x : R => exp (-x)) p_infty 0).
    { eapply is_lim_comp; [exact is_lim_exp_m | exact Hneg |].
      exists 0. intros x Hx. discriminate. }
    assert (Hdiff : is_lim (fun x : R => 1-exp (-x)) p_infty 1).
    { eapply is_lim_minus; [apply is_lim_const | exact He |].
      unfold is_Rbar_minus, is_Rbar_plus, Rbar_opp. simpl. repeat f_equal; lra. }
    eapply filterlim_ext.
    + intro T. symmetry. apply (is_RInt_unique _ _ _ _ (decay_truncation T)).
    + exact Hdiff.
Qed.
(* END exponential_limit *)
End Ch10.



