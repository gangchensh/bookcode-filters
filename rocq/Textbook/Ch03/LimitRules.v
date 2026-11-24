From Stdlib Require Import Reals Lra Psatz.
From Textbook.Ch02 Require Import Filters Logic.
From Textbook.Ch03 Require Import StandardFilters Approach.

Module Ch03Rules.
Import Ch02 Ch03 Ch03Approach.
Open Scope R_scope.

Theorem approaches_id {X : Type} (F : BookFilter X) :   (* 恒等函数保持趋近 *)
  Approaches (fun x => x) F F.
Proof. intros V HV. exact HV. Qed.

Theorem approaches_comp {X Y Z : Type} (f : X -> Y) (g : Y -> Z)  (* 复合两个趋近关系 *)
    (F : BookFilter X) (G : BookFilter Y) (H : BookFilter Z) :  (* F、G指定输入与输出的趋近方式 *)
  Approaches f F G -> Approaches g G H ->
  Approaches (fun x => g (f x)) F H.
Proof.
  intros Hf Hg W HW. exact (Hf (preimage g W) (Hg W HW)).
Qed.

Theorem approaches_congr {X Y : Type} (f g : X -> Y)    (* 最终相等不改变极限 *)
    (F : BookFilter X) (G : BookFilter Y) :             (* F、G指定输入与输出的趋近方式 *)
  Eventually F (fun x => f x = g x) ->
  Approaches f F G -> Approaches g F G.
Proof.
  intros Hfg Hf V HV. eapply upward.
  - eapply meets; [exact Hfg | exact (Hf V HV)].
  - intros x [Heq Hx]. unfold preimage in *. rewrite <- Heq. exact Hx.
Qed.

Theorem const_limit {X : Type} (F : BookFilter X) (b : R) :  (* 常值函数趋于其常值 *)
  Approaches (fun _ => b) F (neighborhood_filter b).
Proof.
  apply (proj2 (real_iff _ _ _)). intros eps Heps.      (* 将极限目标转为绝对值判定 *)
  apply Ch02Logic.eventually_of_forall.
  intros x. rewrite Rminus_diag_eq, Rabs_R0; lra.
Qed.

Theorem shift_limit (a c : R) :                         (* 证明平移函数的极限 *)
  Approaches (fun x => x+c) (neighborhood_filter a)
    (neighborhood_filter (a+c)).
Proof.
  apply (proj2 (real_iff _ _ _)). intros eps Heps.      (* 将极限目标转为绝对值判定 *)
  exists eps. split; [exact Heps |]. intros x Hx.       (* 选取eps作为见证，再分别证明各项要求 *)
  replace (x+c-(a+c)) with (x-a) by ring. exact Hx.     (* 用等式改写相应表达式 *)
Qed.

Theorem affine_limit (a : R) :                          (* 复合得到仿射函数极限 *)
  Approaches (fun x => 2*x+3) (neighborhood_filter a)
    (neighborhood_filter (2*a+3)).
Proof.
  exact (approaches_comp (fun x => 2*x) (fun y => y+3)
    _ _ _ (double_limit a) (shift_limit (2*a) 3)).      (* 把倍乘和加常数的极限结论复合 *)
Qed.

Theorem approaches_within_source {X Y : Type} (f : X -> Y)  (* 限制源仍保持趋近 *)
    (F : BookFilter X) (G : BookFilter Y) (S : X -> Prop) :  (* F、G指定输入与输出的趋近方式 *)
  Approaches f F G -> Approaches f (within F S) G.
Proof.
  intros H V HV. change (members F (fun x => S x -> V (f x))).
  eapply upward; [exact (H V HV) |]. intros x Hx HS. exact Hx.
Qed.

Theorem target_proper {X Y : Type} (f : X -> Y)         (* 源非平凡推出目标非平凡 *)
    (F : BookFilter X) (G : BookFilter Y) :             (* F、G指定输入与输出的趋近方式 *)
  Approaches f F G -> IsProper F -> IsProper G.
Proof.
  intros H HF Hempty. apply HF. exact (H (fun _ => False) Hempty).
Qed.

End Ch03Rules.
