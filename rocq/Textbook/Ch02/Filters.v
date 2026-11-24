From Stdlib Require Import Arith Reals Lra.
From Textbook.Ch02 Require Import Eventually.
From Textbook.Ch02 Require Import Neighborhoods.

Module Ch02.

Structure BookFilter (X : Type) : Type := {             (* 声明数据与证明字段 *)
  members : (X -> Prop) -> Prop;                        (* 指定集合族的成员谓词 *)
  whole : members (fun _ => True);                      (* 恒真谓词表示全空间 *)
  meets : forall A B, members A -> members B ->         (* 合并两个成员断言 *)
    members (fun x => A x /\ B x);                      (* 要求两个成员的交仍是成员 *)
  upward : forall A B, members A ->                     (* 验证向上封闭性 *)
    (forall x, A x -> B x) -> members B
}.

Arguments members {X} _ _.                              (* 设置可由系统推断的参数 *)
Arguments whole {X} _.                                  (* 设置可由系统推断的参数 *)
Arguments meets {X} _ _ _ _ _.                          (* 设置可由系统推断的参数 *)
Arguments upward {X} _ _ _ _ _.                         (* 设置可由系统推断的参数 *)

Definition IsProper {X : Type} (F : BookFilter X) : Prop :=  (* 空集不属于滤子的条件 *)
  ~ members F (fun _ => False).                         (* 要求空集不属于滤子 *)

Definition tail_filter : BookFilter nat.                (* 构造自然数尾集滤子 *)
Proof.
  refine {| members := EventuallyNat |}.                (* 指定members为EventuallyNat，其余字段待证 *)
  - exists 0%nat. intros n Hn. exact I.                 (* 选取0作为见证 *)
  - intros A B HA HB.
    exact (EventuallyNat_and A B HA HB).                (* 用第1章的合取规则合并HA、HB *)
  - intros A B HA HAB.
    exact (EventuallyNat_mono A B HA HAB).              (* 用HA及逐点蕴含HAB推出B最终成立 *)
Defined.                                                (* 结束并保留可展开的定义 *)

Theorem tail_filter_proper : IsProper tail_filter.      (* 自然数尾集滤子不含空集 *)
Proof.
  intros [N HN].
  exact (HN N (Nat.le_refl N)).
Qed.

Definition principal {X : Type} (S : X -> Prop) : BookFilter X.  (* 构造固定集合的主滤子 *)
Proof.
  refine {| members := fun A => forall x, S x -> A x |}.  (* 指定members为fun A => forall x, S x -> A x，其余字段待证 *)
  - intros x Hx. exact I.
  - intros A B HA HB x Hx.
    split.
    + exact (HA x Hx).
    + exact (HB x Hx).
  - intros A B HA HAB x Hx.
    exact (HAB x (HA x Hx)).
Defined.                                                (* 结束并保留可展开的定义 *)

Theorem principal_proper {X : Type} (S : X -> Prop) :   (* 非空集合生成的主滤子不含空集 *)
  (exists x, S x) -> IsProper (principal S).
Proof.
  intros [x Hx] H.
  exact (H x Hx).
Qed.

Open Scope R_scope.

Definition neighborhood_filter (a : R) : BookFilter R.  (* 构造实数邻域滤子 *)
Proof.
  refine {| members := is_neighborhood a |}.  (* 指定members为is_neighborhood a，其余字段待证 *)
  - exists 1. split.                                    (* 选取1作为见证，再分别证明各项要求 *)
    + lra.                                              (* 核对线性实数不等式 *)
    + intros x Hx. exact I.
  - intros A B [e [He HA]] [d [Hd HB]].
    exists (Rmin e d). split.                           (* 选取(Rmin e d)作为见证，再分别证明各项要求 *)
    + apply Rmin_pos; assumption.
    + intros x Hx. split.
      * apply HA. unfold eps_neighborhood in *.
        exact (Rlt_le_trans _ _ _ Hx (Rmin_l e d)).     (* 连接已有关系完成目标 *)
      * apply HB. unfold eps_neighborhood in *.
        exact (Rlt_le_trans _ _ _ Hx (Rmin_r e d)).     (* 连接已有关系完成目标 *)
  - intros A B [e [He HA]] HAB.
    exists e. split.                                    (* 选取e作为见证，再分别证明各项要求 *)
    + exact He.
    + intros x Hx. exact (HAB x (HA x Hx)).
Defined.                                                (* 结束并保留可展开的定义 *)

Theorem neighborhood_filter_proper (a : R) :            (* 实数邻域滤子不含空集 *)
  IsProper (neighborhood_filter a).
Proof.
  intros [e [He HU]].
  apply (HU a).
  unfold eps_neighborhood.
  replace (a - a) with 0 by lra.                        (* 用等式改写相应表达式 *)
  rewrite Rabs_R0.                                      (* 按Rabs_R0给出的等式或等价式改写 *)
  exact He.
Qed.

Definition Eventually {X : Type}                        (* 定义沿滤子的最终成立 *)
    (F : BookFilter X) (P : X -> Prop) : Prop :=
  members F P.                                          (* 满足 P 的点组成滤子的一个成员 *)

Theorem eventually_tail_iff (P : nat -> Prop) :         (* 尾集滤子最终成立等价于阈值判定 *)
  Eventually tail_filter P <-> EventuallyNat P.
Proof.
  reflexivity.                                          (* 两边展开定义后相同 *)
Qed.

End Ch02.
