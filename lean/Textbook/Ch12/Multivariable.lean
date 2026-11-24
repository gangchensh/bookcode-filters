import Textbook.Ch06.Derivatives

namespace Ch12
open Filter Asymptotics
open scoped Topology

theorem punctured_limit_norm_iff {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : E → G) (a : E) (b : G) :
    Tendsto f (𝓝[≠] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < ‖x-a‖ ∧ ‖x-a‖ < δ → ‖f x-b‖ < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, dist_eq_norm,
    norm_pos_iff, sub_ne_zero, and_imp]

theorem within_punctured_limit_norm_iff {E G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup G] (f : E → G) (S : Set E) (a : E) (b : G) :
    Tendsto f (𝓝[{x | x ∈ S ∧ x ≠ a}] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ S ∧ x ≠ a → ‖x-a‖ < δ → ‖f x-b‖ < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_setOf_eq, dist_eq_norm]

-- BEGIN definition
def HasTotalDerivative (f : (ℝ × ℝ) → ℝ)
    (a : ℝ × ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) : Prop :=
  (fun x => f x - f a - L (x - a)) =o[𝓝 a]
    (fun x => x - a)                              -- 余项相对输入增量为小o

theorem total_native_iff (f : (ℝ × ℝ) → ℝ)
    (a : ℝ × ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ) :
    HasTotalDerivative f a L ↔ HasFDerivAt f L a := by
  exact hasFDerivAt_iff_isLittleO.symm             -- 库定义与余项表述等价
-- END definition

-- BEGIN linear
def linearModel (c d : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  c • ContinuousLinearMap.fst ℝ ℝ ℝ +
    d • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem linearModel_apply (c d : ℝ) (h : ℝ × ℝ) :
    linearModel c d h = c * h.1 + d * h.2 := by
  rfl                                            -- 两个系数作用于两个坐标

theorem linear_derivative (c d : ℝ) (a : ℝ × ℝ) :
    HasFDerivAt (linearModel c d) (linearModel c d) a := by
  exact (linearModel c d).hasFDerivAt              -- 线性映射的微分就是自身
-- END linear

-- BEGIN product
theorem product_derivative (a : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => x.1 * x.2)
      (linearModel a.2 a.1) a := by
  convert!
    (hasFDerivAt_fst (𝕜 := ℝ) (p := a)).mul
      (hasFDerivAt_snd (𝕜 := ℝ) (p := a)) using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [linearModel, add_comm]                    -- 微分为a₂h₁+a₁h₂

theorem product_remainder (a h : ℝ × ℝ) :
    (a.1 + h.1) * (a.2 + h.2) - a.1 * a.2 -
      linearModel a.2 a.1 h = h.1 * h.2 := by
  simp only [linearModel_apply]
  ring                                           -- 剩余项恰为h₁h₂
-- END product

-- BEGIN quadratic
def sensor (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 * x.1 + x.2, x.1 * x.2)

def sensorDifferential (a : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (linearModel (2 * a.1) 1).prod (linearModel a.2 a.1)

theorem sensor_derivative (a : ℝ × ℝ) :
    HasFDerivAt sensor (sensorDifferential a) a := by
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (p := a)
  have hy := hasFDerivAt_snd (𝕜 := ℝ) (p := a)
  have hfirst : HasFDerivAt
      (fun x : ℝ × ℝ => x.1 * x.1 + x.2)
      (linearModel (2 * a.1) 1) a := by
    convert! (hx.mul hx).add hy using 1
    apply ContinuousLinearMap.ext
    intro h
    simp [linearModel]
    ring                                         -- 两份a₁h₁合并为2a₁h₁
  exact hfirst.prodMk (product_derivative a)       -- 分别核验两个输出分量
-- END quadratic

-- BEGIN chain
theorem chain_derivative (c d : ℝ) (a : ℝ × ℝ) :
    HasFDerivAt (fun x => linearModel c d (sensor x))
      ((linearModel c d).comp (sensorDifferential a)) a := by
  exact ((linearModel c d).hasFDerivAt).comp a
    (sensor_derivative a)                         -- 先内层微分，再外层微分

theorem chain_coefficients (c d : ℝ) (a h : ℝ × ℝ) :
    (linearModel c d).comp (sensorDifferential a) h =
      (2 * c * a.1 + d * a.2) * h.1 +
        (c + d * a.1) * h.2 := by
  simp [sensorDifferential, linearModel]
  ring                                           -- 矩阵行乘内层雅可比
-- END chain

-- BEGIN limit
theorem polynomial_limit (a : ℝ × ℝ) :
    Tendsto sensor (𝓝 a) (𝓝 (sensor a)) := by
  exact (sensor_derivative a).continuousAt        -- 全微分存在蕴含连续

theorem restricted_limit (S : Set (ℝ × ℝ)) (a : ℝ × ℝ) :
    Tendsto sensor (𝓝[S] a) (𝓝 (sensor a)) := by
  exact (polynomial_limit a).mono_left nhdsWithin_le_nhds
-- END limit

-- BEGIN rules
theorem linear_combination {f g : (ℝ × ℝ) → ℝ} {a : ℝ × ℝ}
    {L M : (ℝ × ℝ) →L[ℝ] ℝ} (hf : HasFDerivAt f L a)
    (hg : HasFDerivAt g M a) (c d : ℝ) :
    HasFDerivAt (fun x => c * f x + d * g x) (c • L + d • M) a := by
  exact (hf.const_mul c).add (hg.const_mul d)       -- 两个主部按相同系数相加

theorem product_rule {f g : (ℝ × ℝ) → ℝ} {a : ℝ × ℝ}
    {L M : (ℝ × ℝ) →L[ℝ] ℝ} (hf : HasFDerivAt f L a)
    (hg : HasFDerivAt g M a) :
    HasFDerivAt (fun x => f x * g x) (f a • M + g a • L) a := by
  exact hf.mul hg                                 -- 微分为f(a)Dg(a)+g(a)Df(a)
-- END rules

-- BEGIN remainder_certificate
theorem sensor_remainder_estimate (a h : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r)
    (h₁ : |h.1| ≤ r) (h₂ : |h.2| ≤ r) :
    |(sensor (a+h)).1 - (sensor a).1 - (sensorDifferential a h).1| ≤ r^2 ∧
    |(sensor (a+h)).2 - (sensor a).2 - (sensorDifferential a h).2| ≤ r^2 := by
  have heq₁ : (sensor (a+h)).1 - (sensor a).1 -
      (sensorDifferential a h).1 = h.1^2 := by
    simp [sensor, sensorDifferential, linearModel]; ring
  have heq₂ : (sensor (a+h)).2 - (sensor a).2 -
      (sensorDifferential a h).2 = h.1 * h.2 := by
    simp [sensor, sensorDifferential, linearModel]; ring
  rw [heq₁, heq₂, abs_of_nonneg (sq_nonneg h.1), abs_mul]
  constructor
  · calc
      h.1^2 = |h.1|^2 := (sq_abs h.1).symm
      _ ≤ r^2 := pow_le_pow_left₀ (abs_nonneg _) h₁ 2 -- 第一分量余项为h₁²
  · calc
      |h.1| * |h.2| ≤ r * r := mul_le_mul h₁ h₂ (abs_nonneg _) hr
      _ = r^2 := by ring                          -- 第二分量余项为h₁h₂
-- END remainder_certificate

end Ch12
