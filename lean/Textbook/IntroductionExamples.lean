import Mathlib.Analysis.SpecificLimits.Basic

open Topology

-- Integer division is a total operation, with division by zero defined as zero.
example : (1 : ℤ) / 0 = 0 := by norm_num
example : ∀ a : ℤ, a / 0 = 0 := by
  intro a
  simp                                                  -- 化简后使用已有证明

-- Here the division takes place in the real numbers, not in the integers.
example : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
    Filter.atTop (nhds (0 : ℝ)) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

-- 完整邻域作源：平方函数在a处连续。
theorem limit_x_sq (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => x ^ 2) (𝓝 a) (𝓝 (a ^ 2)) := by
  exact (Filter.tendsto_id : Filter.Tendsto
    (fun x : ℝ => x) (𝓝 a) (𝓝 a)).pow 2

-- 限制为去心邻域，取得通常的函数极限。
theorem limit_x_sq_punctured (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => x ^ 2) (𝓝[≠] a) (𝓝 (a ^ 2)) := by
  exact (limit_x_sq a).mono_left nhdsWithin_le_nhds
