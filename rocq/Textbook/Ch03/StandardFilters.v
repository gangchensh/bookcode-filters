From Stdlib Require Import Reals Lra.
From Textbook.Ch02 Require Import Filters Logic.

Module Ch03.
Import Ch02.
Open Scope R_scope.

Definition upper_filter : BookFilter R.                 (* 构造实数上尾滤子 *)
Proof.
  refine {| members := fun A => exists b : R,           (* 指定构造并留下子目标 *)
    forall x : R, b <= x -> A x |}.
  - exists 0. intros x Hx. exact I.                     (* 选取0作为见证 *)
  - intros A B [b Hb] [c Hc]. exists (Rmax b c).
    intros x Hx. split.
    + apply Hb. eapply Rle_trans; [apply Rmax_l | exact Hx].
    + apply Hc. eapply Rle_trans; [apply Rmax_r | exact Hx].
  - intros A B [b Hb] HAB. exists b.
    intros x Hx. apply HAB. apply Hb. exact Hx.
Defined.                                                (* 结束并保留可展开的定义 *)

Definition lower_filter : BookFilter R.                 (* 构造实数下尾滤子 *)
Proof.
  refine {| members := fun A => exists b : R,           (* 指定构造并留下子目标 *)
    forall x : R, x <= b -> A x |}.
  - exists 0. intros x Hx. exact I.                     (* 选取0作为见证 *)
  - intros A B [b Hb] [c Hc]. exists (Rmin b c).
    intros x Hx. split.
    + apply Hb. eapply Rle_trans; [exact Hx | apply Rmin_l].
    + apply Hc. eapply Rle_trans; [exact Hx | apply Rmin_r].
  - intros A B [b Hb] HAB. exists b.
    intros x Hx. apply HAB. apply Hb. exact Hx.
Defined.                                                (* 结束并保留可展开的定义 *)

Theorem upper_proper : IsProper upper_filter.           (* 非空线性序上的上尾滤子不含空集 *)
Proof.
  intros [b Hb]. apply (Hb b). apply Rle_refl.
Qed.

Theorem lower_proper : IsProper lower_filter.           (* 非空线性序上的下尾滤子不含空集 *)
Proof.
  intros [b Hb]. apply (Hb b). apply Rle_refl.
Qed.

Definition within {X : Type} (F : BookFilter X)         (* 将滤子限制到给定集合 *)
    (S : X -> Prop) : BookFilter X.
Proof.
  refine {| members := fun A => members F (fun x => S x -> A x) |}.  (* 指定members为fun A => members F (fun x => S x -> A x)，其余字段待证 *)
  - eapply upward; [apply whole |]. intros x Hx HS. exact I.
  - intros A B HA HB.
    eapply upward; [eapply meets; [exact HA | exact HB] |].
    intros x [HxA HxB] HS. split.
    + apply HxA. exact HS.
    + apply HxB. exact HS.
  - intros A B HA HAB.
    eapply upward; [exact HA |].
    intros x Hx HS. apply HAB. apply Hx. exact HS.
Defined.                                                (* 结束并保留可展开的定义 *)

Theorem eventually_within_iff {X : Type} (F : BookFilter X)  (* 限制后最终成立等价于原滤子上的蕴含 *)
    (S P : X -> Prop) :
  Eventually (within F S) P <-> Eventually F (fun x => S x -> P x).
Proof. reflexivity. Qed.                                (* 展开定义后两边相同 *)

Theorem within_mono_set {X : Type} (F : BookFilter X)   (* 缩小限制集合仍保持最终成立 *)
    (S T P : X -> Prop) :
  (forall x, T x -> S x) ->
  Eventually (within F S) P -> Eventually (within F T) P.
Proof.
  intros HTS HP. change (members F (fun x => T x -> P x)).
  change (members F (fun x => S x -> P x)) in HP.
  eapply upward; [exact HP |].
  intros x Hx HT. apply Hx. apply HTS. exact HT.
Qed.

Definition near_within (a : R) (S : R -> Prop) : BookFilter R :=  (* 构造集合内邻域滤子 *)
  within (neighborhood_filter a) S.                     (* 把邻域滤子限制在集合 S 上 *)
Definition punctured (a : R) : BookFilter R :=          (* 排除中心点的邻域滤子 *)
  near_within a (fun x => x <> a).                      (* 限制到不等于中心的点 *)
Definition right_near (a : R) : BookFilter R :=         (* 限制到中心点右侧 *)
  near_within a (fun x => a < x).                       (* 限制到中心右侧的点 *)
Definition left_near (a : R) : BookFilter R :=          (* 限制到中心点左侧 *)
  near_within a (fun x => x < a).                       (* 限制到中心左侧的点 *)

Theorem eventually_near_within_iff (a : R) (S P : R -> Prop) :  (* 集合内最终成立的半径判定 *)
  Eventually (near_within a S) P <->
  exists d : R, 0 < d /\ forall x : R,                  (* 断言存在一个合适的见证 *)
    Rabs (x-a) < d -> S x -> P x.
Proof. reflexivity. Qed.                                (* 展开定义后两边相同 *)

Theorem punctured_ne (a : R) :                          (* 去心邻域中x最终不等于a *)
  Eventually (punctured a) (fun x => x <> a).
Proof. exists 1. split; [lra |]. intros x Hx Hne. exact Hne. Qed.

Theorem right_proper (a : R) : IsProper (right_near a).  (* 右侧邻域滤子非平凡 *)
Proof.
  intros [d [Hd H]].
  assert (Hdist : Rabs (a+d/2-a) < d) by (rewrite Rabs_right; lra).
  apply (H (a+d/2) Hdist). lra.
Qed.

Theorem left_proper (a : R) : IsProper (left_near a).   (* 左侧邻域滤子非平凡 *)
Proof.
  intros [d [Hd H]].
  assert (Hdist : Rabs (a-d/2-a) < d) by (rewrite Rabs_left; lra).
  apply (H (a-d/2) Hdist). lra.
Qed.

Theorem punctured_iff_sides (a : R) (P : R -> Prop) :   (* 去心成立等价于两侧成立 *)
  Eventually (punctured a) P <->
  Eventually (left_near a) P /\ Eventually (right_near a) P.
Proof.
  split.
  - intros H. split.
    + eapply within_mono_set; [| exact H]. intros x Hx. lra.
    + eapply within_mono_set; [| exact H]. intros x Hx. lra.
  - intros [[d [Hd HL]] [e [He HR]]].
    exists (Rmin d e). split.                           (* 选取(Rmin d e)作为见证，再分别证明各项要求 *)
    + apply Rmin_pos; assumption.
    + intros x Hx Hne.
      destruct (Rlt_dec x a) as [Hleft | Hleft].
      * apply HL; [| exact Hleft].
        eapply Rlt_le_trans; [exact Hx | apply Rmin_l].
      * apply HR; [| lra].
        eapply Rlt_le_trans; [exact Hx | apply Rmin_r].
Qed.

End Ch03.
