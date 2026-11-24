From Stdlib Require Import Reals.
Open Scope R_scope.

Definition eps_neighborhood                             (* 基本邻域的成员谓词 *)
    (a eps : R) : R -> Prop :=
  fun x => Rabs (x - a) < eps.

Definition is_neighborhood                              (* 一般邻域包含基本邻域 *)
    (a : R) (U : R -> Prop) : Prop :=
  exists eps : R,                                       (* 断言存在一个合适的见证 *)
    0 < eps /\                                          (* 半径必须为正 *)
    forall x : R,
      eps_neighborhood a eps x -> U x.

Definition locally_holds                                (* 定义在一点附近成立 *)
    (a : R) (P : R -> Prop) : Prop :=
  is_neighborhood a P.                                  (* 满足 P 的点组成 a 的邻域 *)

Definition punctured_eps_neighborhood
    (a eps : R) : R -> Prop :=
  fun x =>
    x <> a /\                                           (* 排除中心点 *)
    Rabs (x - a) < eps.                                 (* 要求点与中心的距离小于半径 *)


Theorem is_neighborhood_inter (a : R) (U V : R -> Prop) :  (* 两个邻域的交仍是邻域 *)
  is_neighborhood a U -> is_neighborhood a V ->
  is_neighborhood a (fun x => U x /\ V x).              (* 需要证明两个邻域的交仍是邻域 *)
Proof.
  intros [eps1 [Hpos1 HU]] [eps2 [Hpos2 HV]].
  exists (Rmin eps1 eps2). split.  (* 选取(Rmin eps1 eps2)作为见证，再分别证明各项要求 *)
  - unfold Rmin. destruct (Rle_dec eps1 eps2); assumption.
  - intros x Hx. split.
    + apply HU. unfold eps_neighborhood in *.
      eapply Rlt_le_trans; [exact Hx | apply Rmin_l].
    + apply HV. unfold eps_neighborhood in *.
      eapply Rlt_le_trans; [exact Hx | apply Rmin_r].
Qed.
