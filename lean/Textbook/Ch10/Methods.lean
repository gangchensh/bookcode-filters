import Textbook.Ch09.Integration

namespace Ch10
open MeasureTheory Filter
open scoped Topology Interval

-- BEGIN substitution
theorem change_variable {g g' f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ContinuousOn g' (Set.uIcc a b)) (hf : Continuous f) :
    (∫ x in a..b, g' x * f (g x)) = ∫ y in g a..g b, f y := by
  simpa only [smul_eq_mul, Function.comp_apply] using
    intervalIntegral.integral_deriv_smul_comp hd hg' hf  -- 区间方向由g(a)、g(b)保留
-- END substitution

-- BEGIN parts
theorem integration_by_parts {u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ContinuousOn u (Set.uIcc a b))
    (hv : ContinuousOn v (Set.uIcc a b))
    (hdu : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hdv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hiu : IntervalIntegrable u' volume a b)
    (hiv : IntervalIntegrable v' volume a b) :
    (∫ x in a..b, u x * v' x) =
      u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hv hdu hdv hiu hiv                            -- 连续、导数关系与可积性分别传入
-- END parts

-- BEGIN polynomial
theorem polynomial_substitution :
    (∫ x : ℝ in (0 : ℝ)..1, 2*x*(x^2+1)) = 3/2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t => (t^2+1)^2/2) (2*x*(x^2+1)) x := by
    intro x
    convert
      ((((hasDerivAt_id x).fun_pow 2).add_const 1).fun_pow 2).div_const 2
      using 1 <;> simp <;> ring                     -- 链式求导后核对系数
  have hi : IntervalIntegrable (fun x : ℝ => 2*x*(x^2+1)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop                                        -- 多项式连续，故紧区间可积
  rw [Ch09.primitive_integral (fun x _ => hd x) hi]
  norm_num                                          -- 只计算原函数的两个端点值
-- END polynomial

-- BEGIN xexp
theorem integral_x_exp :
    (∫ x : ℝ in (0 : ℝ)..1, x * Real.exp x) = 1 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t => (t-1)*Real.exp t) (x*Real.exp x) x := by
    intro x
    convert ((hasDerivAt_id' x).sub_const 1).mul (Real.hasDerivAt_exp x)
      using 1 <;>
      first | rfl | ring
  have hi : IntervalIntegrable (fun x : ℝ => x*Real.exp x) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop                                        -- 先保证有限区间上的可积性
  rw [Ch09.primitive_integral (fun x _ => hd x) hi]
  norm_num                                          -- (1-1)e¹-(0-1)e⁰=1
-- END xexp

-- BEGIN improper
def ImproperRight (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  (∀ T, a ≤ T → IntervalIntegrable f volume a T) ∧
    Tendsto (fun T => ∫ x in a..T, f x) atTop (𝓝 L)
-- END improper

theorem improper_right_epsilon_iff (f : ℝ → ℝ) (a L : ℝ) :
    ImproperRight f a L ↔
      (∀ T, a ≤ T → IntervalIntegrable f volume a T) ∧
      (∀ ε > 0, ∃ B ≥ a, ∀ T ≥ B, |(∫ x in a..T, f x) - L| < ε) := by
  rw [ImproperRight, Metric.tendsto_atTop]
  simp only [Real.dist_eq]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun ε hε => ?_⟩
    obtain ⟨B, hB⟩ := h ε hε
    exact ⟨max B a, le_max_right _ _, fun T hT => hB T ((le_max_left _ _).trans hT)⟩
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun ε hε => ?_⟩
    obtain ⟨B, _, hB⟩ := h ε hε
    exact ⟨B, hB⟩

-- BEGIN decay
theorem decay_truncation (T : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..T, Real.exp (-x)) = 1 - Real.exp (-T) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
    intro x
    convert ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id' x).neg).neg
      using 1 <;>
      first | rfl | ring
  have hi : IntervalIntegrable (fun x : ℝ => Real.exp (-x)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [Ch09.primitive_integral (fun x _ => hd x) hi]
  simp only [neg_zero, Real.exp_zero, sub_neg_eq_add]
  ring                                              -- exp(0)=1，得到截断积分公式

theorem exponential_improper :
    ImproperRight (fun x : ℝ => Real.exp (-x)) 0 1 := by
  constructor
  · intro T hT
    apply Continuous.intervalIntegrable
    fun_prop                                        -- 每个有限截断区间都可积
  · simp_rw [decay_truncation]
    simpa using tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
-- END decay

-- BEGIN certificate
theorem decay_tail_error (T : ℝ) :
    |1 - (∫ x : ℝ in (0 : ℝ)..T, Real.exp (-x))| = Real.exp (-T) := by
  rw [decay_truncation]
  simp [abs_of_pos (Real.exp_pos (-T))]               -- 尾部余量严格为正

theorem total_error_budget {I A Q disc tail : ℝ}
    (ht : |I-A| ≤ tail) (hd : |A-Q| ≤ disc) : |I-Q| ≤ tail+disc := by
  calc
    |I-Q| = |(I-A)+(A-Q)| := by congr 1; ring
    _ ≤ |I-A|+|A-Q| := abs_add_le _ _
    _ ≤ tail+disc := add_le_add ht hd                -- 截断余量加有限区间求积误差
-- END certificate

end Ch10
