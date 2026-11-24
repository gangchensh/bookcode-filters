import Textbook.Ch03.Approach

namespace Ch03Definitions
open Ch02 Ch03 Ch03Approach

def SequenceLimit (u : ℕ → ℝ) (b : ℝ) : Prop :=         -- 定义实数数列收敛
  Approaches u tailFilter (neighborhoodFilter b)

theorem sequence_limit_iff (u : ℕ → ℝ) (b : ℝ) :        -- 本书数列收敛等价于ε-N判定
    SequenceLimit u b ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |u n-b| < ε := by
  unfold SequenceLimit
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem sequence_mathlib_iff (u : ℕ → ℝ) (b : ℝ) :      -- Mathlib数列收敛等价于ε-N判定
    Filter.Tendsto u Filter.atTop (nhds b) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |u n-b| < ε := by
  simpa only [Real.dist_eq] using (Metric.tendsto_atTop (u := u) (a := b))  -- 化简后使用已有证明

theorem sequence_limit_mathlib (u : ℕ → ℝ) (b : ℝ) :    -- 本书数列收敛等价于Mathlib数列收敛
    SequenceLimit u b ↔ Filter.Tendsto u Filter.atTop (nhds b) := by
  rw [sequence_limit_iff, sequence_mathlib_iff]         -- 把两种收敛都改写成相同ε-N公式

theorem finite_atTop_iff (f : ℝ → ℝ) (b : ℝ) :          -- 正无穷处实数极限的ε-B判定
    Approaches f (upperFilter ℝ) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ B : ℝ, ∀ x : ℝ, B ≤ x → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem finite_atBot_iff (f : ℝ → ℝ) (b : ℝ) :          -- 负无穷处实数极限的ε-B判定
    Approaches f (lowerFilter ℝ) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ B : ℝ, ∀ x : ℝ, x ≤ B → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem finite_neighborhood_iff (f : ℝ → ℝ) (a b : ℝ) :  -- 完整邻域趋近的ε-δ判定
    Approaches f (neighborhoodFilter a) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x-a| < δ → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

def ContinuousAtPoint (f : ℝ → ℝ) (a : ℝ) : Prop :=     -- 用邻域滤子定义函数在一点连续
  Approaches f (neighborhoodFilter a) (neighborhoodFilter (f a))

theorem continuousAtPoint_iff (f : ℝ → ℝ) (a : ℝ) :     -- 连续性等价于传统ε-δ判定
    ContinuousAtPoint f a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x-a| < δ → |f x-f a| < ε := by
  exact finite_neighborhood_iff f a (f a)               -- 在邻域极限判定中代入b=f(a)

theorem continuousAtPoint_mathlib (f : ℝ → ℝ) (a : ℝ) :  -- 本书连续性等价于Mathlib的ContinuousAt
    ContinuousAtPoint f a ↔ ContinuousAt f a := by
  change Approaches f (neighborhoodFilter a) (neighborhoodFilter (f a)) ↔
    Filter.Tendsto f (nhds a) (nhds (f a))
  rw [approaches_mathlib_iff, Ch02.toMathlib_neighborhood a,  -- 用等式改写相应表达式
    Ch02.toMathlib_neighborhood (f a)]             -- 按括号内列出的等式或等价式改写

theorem finite_within_iff (f : ℝ → ℝ) (S : Set ℝ) (a b : ℝ) :  -- 集合内极限的ε-δ判定
    Approaches f (nearWithin a S) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ,
        |x-a| < δ → x ∈ S → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem finite_punctured_iff (f : ℝ → ℝ) (a b : ℝ) :    -- 去心函数极限的ε-δ判定
    Approaches f (punctured a) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ,
        |x-a| < δ → x ≠ a → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem finite_right_iff (f : ℝ → ℝ) (a b : ℝ) :        -- 右极限的ε-δ判定
    Approaches f (rightNear a) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ,
        |x-a| < δ → a < x → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem finite_left_iff (f : ℝ → ℝ) (a b : ℝ) :         -- 左极限的ε-δ判定
    Approaches f (leftNear a) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ,
        |x-a| < δ → x < a → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem upper_target_iff {α : Type*} (f : α → ℝ) (F : BookFilter α) :  -- 趋于正无穷等价于逐个超过目标阈值
    Approaches f F (upperFilter ℝ) ↔
      ∀ M : ℝ, Eventually F (fun x => M ≤ f x) := by
  constructor
  · intro h M                                           -- 正向：由趋近假设h，任取目标阈值M
    exact h {y | M ≤ y} ⟨M, fun y hy => hy⟩             -- 把目标基本上尾集交给h
  · intro h V hV                                        -- 反向：任取目标成员V
    rcases hV with ⟨M, hM⟩
    exact F.upward (h M) (fun x hx => hM (f x) hx)      -- 把基本上尾集的原像扩大到V的原像

end Ch03Definitions
