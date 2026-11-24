import Textbook.Ch02.Neighborhoods

namespace Ch03Estimates

open Ch02Neighborhoods

-- BEGIN positive
theorem locally_positive :                         -- x > 0在2附近成立
    LocallyHolds 2 (fun x => 0 < x) := by
  refine ⟨1, by norm_num, ?_⟩                       -- 取半径1
  intro x hx
  change |x - (2 : ℝ)| < 1 at hx
  have hl : -1 < x - 2 := (abs_lt.mp hx).1          -- 从绝对值取出左侧不等式
  change 0 < x                                     -- 展开目标中的集合成员命题
  linarith                                         -- 由1 < x推出0 < x
-- END positive

-- BEGIN bound
theorem locally_abs_bound (a : ℝ) :                -- |x|在a附近有统一上界
    LocallyHolds a (fun x => |x| < |a| + 1) := by
  refine ⟨1, by norm_num, ?_⟩                       -- 半径1对每个中心a都可用
  intro x hx
  change |x - a| < 1 at hx
  calc
    |x| = |(x - a) + a| := by congr 1; ring
    _ ≤ |x - a| + |a| := abs_add_le _ _            -- 使用三角不等式
    _ < |a| + 1 := by linarith                     -- 用hx控制与中心的距离
-- END bound

end Ch03Estimates
