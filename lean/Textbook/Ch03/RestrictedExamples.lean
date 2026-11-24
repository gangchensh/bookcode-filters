import Textbook.Ch03.LimitRules

namespace Ch03RestrictedExamples
open Ch02 Ch03 Ch03Approach Ch03Rules

theorem abs_div_right :                              -- |x|/x在零处的右极限为1
    Approaches (fun x : ℝ => |x|/x) (rightNear 0) (neighborhoodFilter 1) := by
  apply (real_iff _ _ _).2
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩                        -- 半径1足够，关键是右侧保证x>0
  intro x hx hxpos
  change 0 < x at hxpos
  change |(|x|/x)-1| < ε
  simpa [abs_of_pos hxpos, div_self (ne_of_gt hxpos)] using hε

theorem abs_div_left :                               -- |x|/x在零处的左极限为-1
    Approaches (fun x : ℝ => |x|/x) (leftNear 0) (neighborhoodFilter (-1)) := by
  apply (real_iff _ _ _).2
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro x hx hxneg
  change x < 0 at hxneg
  change |(|x|/x)-(-1)| < ε
  simpa [abs_of_neg hxneg, neg_div, div_self (ne_of_lt hxneg)] using hε

theorem removable_zero :                             -- x²/x在零处的去心极限为零
    Approaches (fun x : ℝ => x^2/x) (punctured 0) (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2
  intro ε hε
  refine ⟨ε, hε, ?_⟩                                 -- 取δ=ε
  intro x hx hxne
  change x ≠ 0 at hxne                               -- 非零条件来自去心源滤子
  change |x-0| < ε at hx
  have hid : x^2/x = x := by
    field_simp [hxne]                                 -- 只在x≠0的区域约去分母
  change |x^2/x-0| < ε
  simpa only [hid] using hx

end Ch03RestrictedExamples
