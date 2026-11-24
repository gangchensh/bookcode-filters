import Textbook.Ch04.LimitRules

namespace Ch04Continuity
open Ch02 Ch03 Ch03Approach
open Filter
open scoped Topology

-- BEGIN bridge
def BookContinuousAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Approaches f (neighborhoodFilter a) (neighborhoodFilter (f a))

theorem continuous_mathlib (f : ℝ → ℝ) (a : ℝ) :
    BookContinuousAt f a ↔ ContinuousAt f a := by
  unfold BookContinuousAt
  rw [approaches_mathlib_iff, Ch03.toMathlib_neighborhood,
    Ch03.toMathlib_neighborhood]
  rfl
-- END bridge



-- BEGIN rational
theorem rational_at_two :                         -- 去心源上组合有理函数的极限
    Filter.Tendsto (fun x : ℝ => (x ^ 2 + 3 * x - 1) / (x + 1))
      (𝓝[≠] 2) (𝓝 3) := by
  have hx : Filter.Tendsto (fun x : ℝ => x) (𝓝[≠] 2) (𝓝 2) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hc : Filter.Tendsto (fun _ : ℝ => (3 : ℝ)) (𝓝[≠] 2) (𝓝 3) :=
    tendsto_const_nhds
  have hnum := ((hx.pow 2).add (hc.mul hx)).sub
    (tendsto_const_nhds (x := (1 : ℝ)))
  have hden := hx.add (tendsto_const_nhds (x := (1 : ℝ)))
  have h := hnum.div hden (by norm_num : (2 : ℝ) + 1 ≠ 0)
  convert h using 1 <;> norm_num
-- END rational

-- BEGIN operations
theorem continuous_add_book {f g : ℝ → ℝ} {a : ℝ}
    (hf : BookContinuousAt f a) (hg : BookContinuousAt g a) :
    BookContinuousAt (fun x => f x + g x) a := by
  apply (continuous_mathlib _ _).2
  exact ((continuous_mathlib _ _).1 hf).add
    ((continuous_mathlib _ _).1 hg)                  -- 将和的极限规则用于完整邻域源

theorem continuous_mul_book {f g : ℝ → ℝ} {a : ℝ}
    (hf : BookContinuousAt f a) (hg : BookContinuousAt g a) :
    BookContinuousAt (fun x => f x * g x) a := by
  apply (continuous_mathlib _ _).2
  exact ((continuous_mathlib _ _).1 hf).mul
    ((continuous_mathlib _ _).1 hg)

theorem continuous_div_book {f g : ℝ → ℝ} {a : ℝ}
    (hf : BookContinuousAt f a) (hg : BookContinuousAt g a) (hne : g a ≠ 0) :
    BookContinuousAt (fun x => f x / g x) a := by
  apply (continuous_mathlib _ _).2
  exact ((continuous_mathlib _ _).1 hf).div
    ((continuous_mathlib _ _).1 hg) hne               -- 非零假设作用于中心的分母值
-- END operations

end Ch04Continuity
