import Textbook.Ch03.Approach

namespace Ch03Rules
open Ch02 Ch03 Ch03Approach

theorem approaches_eventually_iff {α β : Type*} (f : α → β)  -- 趋近等价于传递所有最终断言
    (F : BookFilter α) (G : BookFilter β) :             -- F、G指定输入与输出的趋近方式
    Approaches f F G ↔ ∀ P : β → Prop,
      Eventually G P → Eventually F (fun x => P (f x)) := Iff.rfl  -- 两边展开定义后相同

theorem approaches_id {α : Type*} (F : BookFilter α) :  -- 恒等函数保持趋近
    Approaches (fun x => x) F F := by
  intro V hV
  exact hV

theorem approaches_comp {α β γ : Type*} {f : α → β} {g : β → γ}  -- 复合两个趋近关系
    {F : BookFilter α} {G : BookFilter β} {H : BookFilter γ}
    (hf : Approaches f F G) (hg : Approaches g G H) :
    Approaches (fun x => g (f x)) F H := by
  intro W hW
  exact hf (g ⁻¹' W) (hg W hW)

theorem approaches_congr {α β : Type*} {f g : α → β}    -- 最终相等不改变极限
    {F : BookFilter α} {G : BookFilter β}
    (hfg : Eventually F (fun x => f x = g x))
    (hf : Approaches f F G) : Approaches g F G := by
  intro V hV
  apply F.upward (F.inter_mem hfg (hf V hV))
  intro x hx
  change g x ∈ V
  rw [← hx.1]                                           -- 使用← hx.1中的等式或等价式改写
  exact hx.2

theorem const_limit {α : Type*} (F : BookFilter α) (b : ℝ) :  -- 常值函数趋于其常值
    Approaches (fun _ => b) F (neighborhoodFilter b) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  apply eventually_of_forall
  intro x
  simpa using hε                                        -- 化简后使用已有证明

theorem shift_limit (a c : ℝ) :                         -- 证明平移函数的极限
    Approaches (fun x : ℝ => x+c)
      (neighborhoodFilter a) (neighborhoodFilter (a+c)) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  refine ⟨ε, hε, ?_⟩                                    -- 选取ε，留下其余证明任务
  intro x hx
  change |(x+c)-(a+c)| < ε
  rw [show (x+c)-(a+c) = x-a by ring]                   -- 按代码中显式给出的等式改写
  exact hx

theorem affine_limit (a : ℝ) :                          -- 复合得到仿射函数极限
    Approaches (fun x : ℝ => 2*x+3)
      (neighborhoodFilter a) (neighborhoodFilter (2*a+3)) := by
  exact approaches_comp (double_limit a) (shift_limit (2*a) 3)

theorem approaches_within_source {α β : Type*} {f : α → β}  -- 限制源仍保持趋近
    {F : BookFilter α} {G : BookFilter β} (S : Set α)
    (h : Approaches f F G) : Approaches f (within F S) G := by
  intro V hV
  exact eventually_to_within (h V hV)

theorem target_proper {α β : Type*} {f : α → β}         -- 源非平凡推出目标非平凡
    {F : BookFilter α} {G : BookFilter β}
    (h : Approaches f F G) (hF : IsProper F) : IsProper G := by
  intro hempty
  apply hF
  simpa using h ∅ hempty                                -- 化简后使用已有证明

theorem real_limit_unique {α : Type*} {f : α → ℝ}       -- 非平凡源下极限唯一
    {F : BookFilter α} {b c : ℝ} (hF : IsProper F)
    (hb : Approaches f F (neighborhoodFilter b))
    (hc : Approaches f F (neighborhoodFilter c)) : b = c := by
  by_contra hne                                         -- 通过反证得到矛盾
  have hd : 0 < |b-c| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hε : 0 < |b-c|/3 := by positivity
  rcases eventually_exists hF
      (eventually_and ((real_iff _ _ _).1 hb _ hε)
        ((real_iff _ _ _).1 hc _ hε)) with ⟨x, hxb, hxc⟩
  have htri : |b-c| ≤ |f x-b| + |f x-c| := by
    calc                                                -- 开始逐步等式或不等式链
      |b-c| = |(b-f x)+(f x-c)| := by congr 1; ring
      _ ≤ |b-f x| + |f x-c| := abs_add_le _ _
      _ = |f x-b| + |f x-c| := by rw [abs_sub_comm b (f x)]
  linarith                                              -- 核对线性实数不等式

theorem approaches_iff_mathlib {α β : Type*} (f : α → β)  -- 教学趋近关系等价于Mathlib的Tendsto
    (F : BookFilter α) (G : BookFilter β) :             -- F、G指定输入与输出的趋近方式
    Approaches f F G ↔ Filter.Tendsto f (toMathlib F) (toMathlib G) := by
  rfl                                                   -- 两边展开定义后相同

end Ch03Rules
