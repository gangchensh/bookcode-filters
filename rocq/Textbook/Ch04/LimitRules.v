From Stdlib Require Import Reals Lra Psatz.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.
From Textbook.Ch03 Require Import LimitRules.
From Textbook.Ch04 Require Import OneSidedInfinity.

Module Ch04.
Import Ch02 Ch02Logic Ch03 Ch03Approach Ch03Rules.
Open Scope R_scope.

Section Rules.
Context {X : Type} (F : BookFilter X).

Theorem limit_add (f g : X -> R) (a b : R) :           (* 共同源上的和极限 *)
  Approaches f F (neighborhood_filter a) ->
  Approaches g F (neighborhood_filter b) ->
  Approaches (fun x => f x+g x) F (neighborhood_filter (a+b)).
Proof.
  intros Hf Hg. apply (proj2 (real_iff _ _ _)).
  intros eps Heps. assert (Hhalf : 0 < eps/2) by lra.
  eapply upward.
  - exact (eventually_and
      (proj1 (real_iff _ _ _) Hf _ Hhalf)
      (proj1 (real_iff _ _ _) Hg _ Hhalf)).           (* 合并两个 eps/2 距离界 *)
  - intros x [Hxf Hxg].
    replace (f x+g x-(a+b)) with ((f x-a)+(g x-b)) by ring.
    pose proof (Rabs_triang (f x-a) (g x-b)).
    lra.                                            (* 距离之和严格小于 eps *)
Qed.

Theorem limit_neg (f : X -> R) (a : R) :
  Approaches f F (neighborhood_filter a) ->
  Approaches (fun x => -f x) F (neighborhood_filter (-a)).
Proof.
  intros Hf. apply (proj2 (real_iff _ _ _)). intros eps Heps.
  eapply upward; [exact (proj1 (real_iff _ _ _) Hf eps Heps) |].
  intros x Hx. replace (-f x- -a) with (-(f x-a)) by ring.
  rewrite Rabs_Ropp. exact Hx.                      (* 用 |-z|=|z| *)
Qed.

Theorem limit_sub (f g : X -> R) (a b : R) :
  Approaches f F (neighborhood_filter a) ->
  Approaches g F (neighborhood_filter b) ->
  Approaches (fun x => f x-g x) F (neighborhood_filter (a-b)).
Proof.
  intros Hf Hg. exact (limit_add f (fun x => -g x) a (-b)
    Hf (limit_neg g b Hg)).
Qed.

Theorem limit_squeeze (f g h : X -> R) (a : R) :      (* 两端同极限，最终夹住中间函数 *)
  Approaches f F (neighborhood_filter a) ->
  Approaches h F (neighborhood_filter a) ->
  Eventually F (fun x => f x <= g x) ->
  Eventually F (fun x => g x <= h x) ->
  Approaches g F (neighborhood_filter a).
Proof.
  intros Hf Hh Hfg Hgh.
  apply (proj2 (real_iff _ _ _)). intros eps Heps.
  eapply upward.
  - exact (eventually_and (eventually_and Hfg Hgh)
      (eventually_and
        (proj1 (real_iff _ _ _) Hf eps Heps)
        (proj1 (real_iff _ _ _) Hh eps Heps))).       (* 四项要求取共同成员 *)
  - intros x [[Hlow Hupp] [Hfd Hhd]].
    apply Rabs_def1.
    + apply Rabs_def2 in Hhd. lra.                  (* 用右端得到 g(x)-a<eps *)
    + apply Rabs_def2 in Hfd. lra.                  (* 用左端得到 -eps<g(x)-a *)
Qed.

Theorem bounded_mul_zero (f g : X -> R) (C : R) :    (* 有界因子不必存在极限 *)
  0 <= C -> Eventually F (fun x => Rabs (f x) <= C) ->
  Approaches g F (neighborhood_filter 0) ->
  Approaches (fun x => f x*g x) F (neighborhood_filter 0).
Proof.
  intros HC Hbound Hg.
  apply (proj2 (real_iff _ _ _)). intros eps Heps.
  assert (HC1 : 0 < C+1) by lra.
  assert (Heta : 0 < eps/(C+1)) by (apply Rdiv_lt_0_compat; assumption).
  eapply upward.
  - exact (eventually_and Hbound
      (proj1 (real_iff _ _ _) Hg _ Heta)).
  - intros x [Hf Hgsmall]. rewrite Rminus_0_r in *.
    rewrite Rabs_mult.
    assert (Hprod : Rabs (f x)*Rabs (g x) <= C*Rabs (g x)).
    { apply Rmult_le_compat_r; [apply Rabs_pos | exact Hf]. }
    assert (Hsmall : Rabs (g x)*(C+1) < eps).
    { apply (Rmult_lt_reg_r (/ (C+1))).
      - apply Rinv_0_lt_compat. exact HC1.
      - replace (Rabs (g x)*(C+1)*/(C+1)) with (Rabs (g x)).
        + exact Hgsmall.
        + field. lra. }
    pose proof (Rabs_pos (g x)). nra.               (* C|g|≤(C+1)|g|<eps *)
Qed.

Theorem limit_le (f g : X -> R) (a b : R) :           (* 保序需要源非平凡 *)
  IsProper F ->
  Approaches f F (neighborhood_filter a) ->
  Approaches g F (neighborhood_filter b) ->
  Eventually F (fun x => f x <= g x) -> a <= b.
Proof.
  intros HF Hf Hg Hfg. apply Rnot_lt_le. intro Hba.
  assert (Heta : 0 < (a-b)/3) by lra.
  destruct (eventually_exists HF
    (eventually_and Hfg (eventually_and
      (proj1 (real_iff _ _ _) Hf _ Heta)
      (proj1 (real_iff _ _ _) Hg _ Heta))))
    as [x [Hord [Hfd Hgd]]].                        (* 在共同成员中取一个实际点 *)
  apply Rabs_def2 in Hfd. apply Rabs_def2 in Hgd.
  lra.                                              (* 此点同时要求 f(x)>g(x) *)
Qed.

Theorem upper_add_finite (f g : X -> R) (b : R) :
  Approaches f F upper_filter ->
  Approaches g F (neighborhood_filter b) ->
  Approaches (fun x => f x+g x) F upper_filter.
Proof.
  intros Hf Hg. apply (proj2 (Ch04Infinity.upper_iff _ _)). intros M.
  eapply upward.
  - exact (eventually_and
      (proj1 (Ch04Infinity.upper_iff _ _) Hf (M-b+1))
      (proj1 (real_iff _ _ _) Hg 1 Rlt_0_1)).        (* 上阈值与有限目标距离同时满足 *)
  - intros x [Hfm Hgb]. apply Rabs_def2 in Hgb. lra.
Qed.

End Rules.
End Ch04.
