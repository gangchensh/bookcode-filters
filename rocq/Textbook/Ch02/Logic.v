From Stdlib Require Import Arith Lia Reals Lra Classical_Prop.
From Textbook.Ch02 Require Import Filters.
Import Filters.Ch02.

Module Ch02Logic.

Definition EventuallyEq {X Y : Type}                    (* 定义两个函数最终相等 *)
    (F : BookFilter X) (f g : X -> Y) : Prop :=
  Eventually F (fun x => f x = g x).                    (* f与g沿F最终相等 *)

Definition EventuallyLE {X : Type}                      (* 定义最终不等式 *)
    (F : BookFilter X) (f g : X -> R) : Prop :=
  Eventually F (fun x => f x <= g x).                   (* f≤g沿F最终成立 *)

Section Rules.
Context {X : Type} {F : BookFilter X}.

Theorem eventually_of_forall {P : X -> Prop} :          (* 由处处成立推出最终成立 *)
  (forall x, P x) -> Eventually F P.
Proof.
  intro H.
  apply (upward F (fun _ => True) P).
  - exact (whole F).
  - intros x Hx. exact (H x).
Qed.

Theorem eventually_mono {P Q : X -> Prop} :             (* 沿逐点蕴含传递最终成立 *)
  Eventually F P -> (forall x, P x -> Q x) -> Eventually F Q.
Proof.
  intros HP HPQ.
  exact (upward F P Q HP HPQ).                          (* 使用滤子的向上封闭性 *)
Qed.

Theorem eventually_and {P Q : X -> Prop} :              (* 合并两个最终断言 *)
  Eventually F P -> Eventually F Q ->
  Eventually F (fun x => P x /\ Q x).
Proof.
  intros HP HQ.
  exact (meets F P Q HP HQ).                            (* 使用滤子的有限交性质 *)
Qed.

Theorem eventually_and_iff {P Q : X -> Prop} :          (* 最终合取的双向判定 *)
  Eventually F (fun x => P x /\ Q x) <->
  Eventually F P /\ Eventually F Q.
Proof.
  split.
  - intro H. split.
    + eapply eventually_mono.                           (* 转为共同区域上的逐点推理 *)
      * exact H.
      * intros x Hx. exact (proj1 Hx).
    + eapply eventually_mono.                           (* 转为共同区域上的逐点推理 *)
      * exact H.
      * intros x Hx. exact (proj2 Hx).
  - intros [HP HQ]. exact (eventually_and HP HQ).
Qed.

Theorem eventually_mp {P Q : X -> Prop} :               (* 在共同区域使用蕴含 *)
  Eventually F (fun x => P x -> Q x) ->
  Eventually F P -> Eventually F Q.
Proof.
  intros HPQ HP.
  eapply eventually_mono.                               (* 转为共同区域上的逐点推理 *)
  - exact (eventually_and HPQ HP).
  - intros x [Himp Hpx]. exact (Himp Hpx).
Qed.

Theorem eventuallyEq_refl {Y : Type} (f : X -> Y) :     (* 最终相等的自反性 *)
  EventuallyEq F f f.
Proof.
  apply eventually_of_forall. intro x. reflexivity.
Qed.

Theorem eventuallyEq_symm {Y : Type} (f g : X -> Y) :   (* 最终相等的对称性 *)
  EventuallyEq F f g -> EventuallyEq F g f.
Proof.
  intro Hfg. eapply eventually_mono.
  - exact Hfg.
  - intros x Hx. symmetry. exact Hx.
Qed.

Theorem eventuallyEq_trans {Y : Type} (f g h : X -> Y) :  (* 最终相等的传递性 *)
  EventuallyEq F f g -> EventuallyEq F g h -> EventuallyEq F f h.  (* 由f =^F g及g =^F h推出f =^F h *)
Proof.
  intros Hfg Hgh.                                       (* 假设Hfg：f =^F g，Hgh：g =^F h *)
  eapply eventually_mono.                               (* 在两个相等断言的共同区域逐点证明 *)
  - exact (eventually_and Hfg Hgh).                     (* 合并f=g与g=h的最终断言 *)
  - intros x [H1 H2]. exact (eq_trans H1 H2).           (* 逐点由f x=g x、g x=h x推出f x=h x *)
Qed.

Theorem eventuallyEq_congr {Y Z : Type}                 (* 将相等值代入同一函数 *)
    (f g : X -> Y) (phi : Y -> Z) :
  EventuallyEq F f g ->
  EventuallyEq F (fun x => phi (f x)) (fun x => phi (g x)).
Proof.
  intro Hfg. eapply eventually_mono.
  - exact Hfg.
  - intros x Hx. rewrite Hx. reflexivity.
Qed.

Theorem eventually_subst {Y : Type} (f g : X -> Y) (P : Y -> Prop) :  (* 用最终相等替换性质 *)
  EventuallyEq F f g -> Eventually F (fun x => P (f x)) ->
  Eventually F (fun x => P (g x)).
Proof.
  intros Hfg HP. eapply eventually_mono.
  - exact (eventually_and Hfg HP).
  - intros x [Hfgx Hpx]. rewrite <- Hfgx. exact Hpx.
Qed.

Theorem eventuallyLE_trans (f g h : X -> R) :           (* 最终不等式的传递性 *)
  EventuallyLE F f g -> EventuallyLE F g h -> EventuallyLE F f h.
Proof.
  intros Hfg Hgh. eapply eventually_mono.
  - exact (eventually_and Hfg Hgh).
  - intros x [H1 H2]. exact (Rle_trans _ _ _ H1 H2).
Qed.

Theorem eventuallyLE_antisymm (f g : X -> R) :          (* 双向不等式推出最终相等 *)
  EventuallyLE F f g -> EventuallyLE F g f -> EventuallyEq F f g.
Proof.
  intros Hfg Hgf. eapply eventually_mono.
  - exact (eventually_and Hfg Hgf).
  - intros x [H1 H2]. apply Rle_antisym; assumption.
Qed.

Theorem eventuallyLE_add (f g u v : X -> R) :           (* 相加两个最终不等式 *)
  EventuallyLE F f g -> EventuallyLE F u v ->
  EventuallyLE F (fun x => f x + u x) (fun x => g x + v x).
Proof.
  intros Hfg Huv. eapply eventually_mono.
  - exact (eventually_and Hfg Huv).
  - intros x [H1 H2]. apply Rplus_le_compat; assumption.
Qed.

Theorem eventually_abs_add_bound (f g : X -> R) :       (* 由两个上界估计和的绝对值 *)
  Eventually F (fun x => Rabs (f x) <= 1) ->
  Eventually F (fun x => Rabs (g x) <= 2) ->
  Eventually F (fun x => Rabs (f x + g x) <= 3).
Proof.
  intros Hf Hg. eapply eventually_mono.
  - exact (eventually_and Hf Hg).
  - intros x [Hf1 Hg2].
    pose proof (Rabs_triang (f x) (g x)) as Htri.       (* 把已有定理加入当前假设 *)
    lra.                                                (* 核对线性实数不等式 *)
Qed.

Theorem not_eventually_false :                          (* 恒假不可能最终成立 *)
  IsProper F -> ~ Eventually F (fun _ => False).
Proof.
  intro HF. exact HF.
Qed.

Theorem eventually_exists {P : X -> Prop} :             (* 非平凡性给出满足点 *)
  IsProper F -> Eventually F P -> exists x, P x.
Proof.
  intros HF HP. apply NNPP. intro Hnone.
  apply HF. eapply eventually_mono.                     (* 转为共同区域上的逐点推理 *)
  - exact HP.
  - intros x Hx. apply Hnone. exists x. exact Hx.
Qed.

End Rules.

Definition changed_at_zero (n : nat) : nat :=           (* 只修改数列的第零项 *)
  if Nat.eq_dec n 0%nat then 100%nat else n.            (* 仅在第零项取值 100 *)

Theorem changed_at_zero_eventuallyEq :                  (* 修改第零项不改变最终相等 *)
  EventuallyEq tail_filter changed_at_zero (fun n => n).
Proof.
  exists 1%nat. intros n Hn.                            (* 选取1作为见证 *)
  unfold changed_at_zero.
  destruct (Nat.eq_dec n 0%nat) as [Hz | Hnz].
  - lia.                                                (* 核对自然数或整数算术 *)
  - reflexivity.                                        (* 两边展开定义后相同 *)
Qed.

End Ch02Logic.
