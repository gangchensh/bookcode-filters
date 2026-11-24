import Mathlib

namespace Ch05Bounds

theorem sqrt_two_bounds :                           -- 精确有理端点夹住√2
    (14142 / 10000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (14143 / 10000 : ℝ) := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith                        -- 对两个有理端点作平方比较

end Ch05Bounds
