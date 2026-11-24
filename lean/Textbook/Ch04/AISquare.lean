import Textbook.Ch03.Approach

open scoped Topology

namespace Ch04AISquare
open Ch02 Ch03Approach

-- Mathlib写法：源为完整邻域，结论还包含中心点处的要求。
theorem limit_x_sq (a : ℝ) :
  Filter.Tendsto (fun x : ℝ => x^2) (𝓝 a) (𝓝 (a^2)) := by
  exact (continuous_id.pow 2).continuousAt

-- 教学写法：使用本书的BookFilter与Approaches，展开基本邻域判定。
theorem limit_x_sq_book (a : ℝ) :
  Approaches (fun x : ℝ => x^2)
    (neighborhoodFilter a) (neighborhoodFilter (a^2)) := by
  apply (real_iff _ _ _).2                            -- 转成绝对值界最终成立
  intro ε hε
  have hden : 0 < 2*|a|+1 := by positivity
  refine ⟨min 1 (ε/(2*|a|+1)), lt_min zero_lt_one (div_pos hε hden), ?_⟩
  intro x hx
  change |x-a| < min 1 (ε/(2*|a|+1)) at hx
  change |x^2-a^2| < ε
  have hx1 : |x-a| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hxε : |x-a| < ε/(2*|a|+1) := lt_of_lt_of_le hx (min_le_right _ _)
  have hfactor : |x+a| ≤ 2*|a|+1 := by
    calc
      |x+a| = |(x-a)+2*a| := by congr 1; ring
      _ ≤ |x-a|+|2*a| := abs_add_le _ _
      _ = |x-a|+2*|a| := by rw [abs_mul]; norm_num
      _ ≤ 2*|a|+1 := by linarith                     -- 先控制另一个因子
  calc
    |x^2-a^2| = |x-a| * |x+a| := by
      rw [show x^2-a^2 = (x-a)*(x+a) by ring, abs_mul]
    _ ≤ |x-a| * (2*|a|+1) := mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
    _ < ε := (lt_div_iff₀ hden).mp hxε               -- 再用半径中的ε要求

end Ch04AISquare
