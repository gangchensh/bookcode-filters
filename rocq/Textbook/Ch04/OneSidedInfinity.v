From Stdlib Require Import Reals Lra Psatz.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.
From Textbook.Ch03 Require Import LimitRules.

Module Ch04Infinity.
Import Ch02 Ch02Logic Ch03 Ch03Approach Ch03Rules.
Open Scope R_scope.

Theorem upper_iff {X : Type} (f : X -> R) (F : BookFilter X) :                  (* 正无穷的阈值判定 *)
  Approaches f F upper_filter <->
    forall M : R, Eventually F (fun x => M <= f x).
Proof.
  split.                                                                        (* 分两向；先证明全部上阈值 *)
  - intros H M. apply (H (fun y => M <= y)).                                    (* 取目标上尾 [M,+∞) *)
    exists M. intros y Hy. exact Hy.
  - intros H V [M HM].                                                          (* 反向取 M，使 [M,+∞)⊆V *)
    eapply upward; [exact (H M) |].                                             (* 留下 M≤f(x) 蕴含 V(f(x)) *)
    intros x Hx. exact (HM (f x) Hx).                                           (* 把阈值要求扩大为目标成员V *)
Qed.

Theorem lower_iff {X : Type} (f : X -> R) (F : BookFilter X) :                  (* 负无穷的阈值判定 *)
  Approaches f F lower_filter <->
    forall M : R, Eventually F (fun x => f x <= M).
Proof.
  split.                                                                        (* 分两向；先证明全部下阈值 *)
  - intros H M. apply (H (fun y => y <= M)).                                    (* 取目标下尾 (-∞,M] *)
    exists M. intros y Hy. exact Hy.
  - intros H V [M HM].                                                          (* 反向取 M，使 (-∞,M]⊆V *)
    eapply upward; [exact (H M) |].                                             (* 留下 f(x)≤M 蕴含 V(f(x)) *)
    intros x Hx. exact (HM (f x) Hx).
Qed.

Theorem sides_iff {Y : Type} (f : R -> Y) (a : R) (G : BookFilter Y) :
  Approaches f (punctured a) G <->
    Approaches f (left_near a) G /\ Approaches f (right_near a) G.
Proof.
  split.
  - intros H. split; intros V HV.                                               (* 分别证明左右原像属于源 *)
    + exact (proj1 (proj1 (punctured_iff_sides a _) (H V HV))).                 (* proj1 提取左侧成员关系 *)
    + exact (proj2 (proj1 (punctured_iff_sides a _) (H V HV))).                 (* proj2 提取右侧成员关系 *)
  - intros [HL HR] V HV.                                                        (* 反向把同一个 V 交给两侧 *)
    apply (proj2 (punctured_iff_sides a _)).                                    (* 把去心成员拆为两侧成员 *)
    split; [exact (HL V HV) | exact (HR V HV)].                                 (* 对同一V合并两侧原像 *)
Qed.

Theorem upper_eventually_pos {X : Type}                                         (* 正无穷保证最终严格正 *)
    (f : X -> R) (F : BookFilter X) :
  Approaches f F upper_filter -> Eventually F (fun x => 0 < f x).
Proof.
  intros H. eapply upward.
  - exact (proj1 (upper_iff f F) H 1).                                          (* 用目标阈值 M=1 *)
  - intros x Hx. lra.                                                           (* lra 由 1≤f(x) 得 f(x)>0 *)
Qed.

Theorem neg_upper_iff {X : Type}                                                (* 负号交换目标的无穷方向 *)
    (f : X -> R) (F : BookFilter X) :
  Approaches (fun x => - f x) F upper_filter <-> Approaches f F lower_filter.
Proof.
  rewrite upper_iff, lower_iff. split; intros H M.
  - eapply upward; [exact (H (-M)) |]. intros x Hx. lra.
  - eapply upward; [exact (H (-M)) |]. intros x Hx. lra.
Qed.

Theorem square_upper :                                                          (* 正无穷处的平方趋于正无穷 *)
  Approaches (fun x : R => x*x) upper_filter upper_filter.
Proof.
  apply (proj2 (upper_iff _ _)). intros M.                                      (* 取任意目标阈值 M *)
  exists (Rmax 1 M). intros x Hx.                                               (* 选源阈值 max(1,M) *)
  pose proof (Rmax_l 1 M). pose proof (Rmax_r 1 M).                             (* 取最大值的两个下界 *)
  assert (1 <= x) by lra. assert (M <= x) by lra.                               (* lra 分别得 x≥1 与 x≥M *)
  assert (0 <= (x-1)*x) by (apply Rmult_le_pos; lra).                           (* 正因子乘积给出 x²-x≥0 *)
  nra.                                                                          (* nra 结合乘积非负得 x²≥M *)
Qed.

Theorem square_lower :                                                          (* 负无穷处的平方同样趋于正无穷 *)
  Approaches (fun x : R => x*x) lower_filter upper_filter.
Proof.
  apply (proj2 (upper_iff _ _)). intros M.
  exists (- Rmax 1 M). intros x Hx.                                             (* 选源阈值 -max(1,M) *)
  pose proof (Rmax_l 1 M). pose proof (Rmax_r 1 M).
  assert (1 <= -x) by lra. assert (M <= -x) by lra.                             (* 把下尾界改写为 -x 的下界 *)
  assert (0 <= (-x-1)*(-x)) by (apply Rmult_le_pos; lra).                       (* 正因子乘积给出 x²+x≥0 *)
  nra.                                                                          (* 由 x²≥-x≥M 得目标 *)
Qed.

Definition join_example (x : R) : R :=                                          (* 与Lean采用相同的分段函数 *)
  if Rlt_dec x 0 then x+1 else if Req_EM_T x 0 then 7 else 1-x.

Theorem join_left :                                                             (* 分段函数左侧趋于1 *)
  Approaches join_example (left_near 0) (neighborhood_filter 1).
Proof.
  apply (proj2 (real_iff _ _ _)). intros eps Heps.                              (* 改证到 1 的距离小于 eps *)
  exists eps. split; [exact Heps |]. intros x Hx Hneg.                          (* 选半径 eps，Hneg 给出 x<0 *)
  unfold join_example. destruct (Rlt_dec x 0); [|lra].                          (* 选左支；另一分支与 x<0 矛盾 *)
  replace (x+1-1) with (x-0) by ring. exact Hx.                                 (* ring 把目标距离改为 |x-0| *)
Qed.

Theorem join_right :                                                            (* 分段函数右侧趋于1 *)
  Approaches join_example (right_near 0) (neighborhood_filter 1).
Proof.
  apply (proj2 (real_iff _ _ _)). intros eps Heps.
  exists eps. split; [exact Heps |]. intros x Hx Hpos.                          (* 选半径 eps，Hpos 给出 x>0 *)
  unfold join_example. destruct (Rlt_dec x 0); [lra|].                          (* x>0 排除左支 x+1 *)
  destruct (Req_EM_T x 0); [lra|].                                              (* x>0 排除中心值 7 *)
  replace (1-x-1) with (- (x-0)) by ring.                                       (* ring 得 (1-x)-1=-(x-0) *)
  rewrite Rabs_Ropp. exact Hx.                                                  (* 用 |-z|=|z|，返回半径界 *)
Qed.

Theorem join_limit :                                                            (* 合并两个单侧极限得到去心极限 *)
  Approaches join_example (punctured 0) (neighborhood_filter 1).
Proof.
  apply (proj2 (sides_iff _ _ _)). split.                                       (* 双侧目标拆为左右同趋于 1 *)
  - exact join_left.                                                            (* 左侧极限为 1 *)
  - exact join_right.                                                           (* 右侧极限也为 1 *)
Qed.

End Ch04Infinity.
