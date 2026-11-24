import Textbook.Ch03.Approach
import Textbook.Ch04.Continuity
import Textbook.Ch03.Statements

namespace Ch06
open Ch02 Ch03 Ch03Approach
open scoped Topology

-- BEGIN definition
def HasDerivative (f : ℝ → ℝ) (a d : ℝ) : Prop :=    -- 差商沿去心源趋于d
  Approaches (fun x => (f x - f a) / (x - a))
    (punctured a) (neighborhoodFilter d)
-- END definition

theorem derivative_epsilon_iff (f : ℝ → ℝ) (a d : ℝ) :
    HasDerivative f a d ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x-a| ∧ |x-a| < δ →
        |(f x - f a) / (x - a) - d| < ε :=
  Ch03Statements.punctured_limit_iff _ a d

def HasDerivativeAlong (f : ℝ → ℝ) (S : Set ℝ) (a d : ℝ) : Prop :=
  Approaches (fun x => (f x - f a) / (x - a))
    (nearWithin a {x | x ∈ S ∧ x ≠ a}) (neighborhoodFilter d)

theorem derivative_along_epsilon_iff (f : ℝ → ℝ) (S : Set ℝ) (a d : ℝ) :
    HasDerivativeAlong f S a d ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x-a| < δ → x ∈ S ∧ x ≠ a →
        |(f x - f a) / (x - a) - d| < ε :=
  Ch03Definitions.finite_within_iff _ _ a d

def HasLeftDerivative (f : ℝ → ℝ) (a d : ℝ) : Prop :=
  Approaches (fun x => (f x - f a) / (x - a)) (leftNear a) (neighborhoodFilter d)

def HasRightDerivative (f : ℝ → ℝ) (a d : ℝ) : Prop :=
  Approaches (fun x => (f x - f a) / (x - a)) (rightNear a) (neighborhoodFilter d)

theorem derivative_left_epsilon_iff (f : ℝ → ℝ) (a d : ℝ) :
    HasLeftDerivative f a d ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, a - δ < x ∧ x < a →
        |(f x - f a) / (x - a) - d| < ε := by
  unfold HasLeftDerivative
  rw [Ch03Definitions.finite_left_iff]
  constructor
  · rintro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx => h x (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hx.2⟩
  · rintro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxa => h x ⟨by linarith [(abs_lt.mp hx).1], hxa⟩⟩

theorem derivative_right_epsilon_iff (f : ℝ → ℝ) (a d : ℝ) :
    HasRightDerivative f a d ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, a < x ∧ x < a + δ →
        |(f x - f a) / (x - a) - d| < ε := by
  unfold HasRightDerivative
  rw [Ch03Definitions.finite_right_iff]
  constructor
  · rintro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx => h x (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hx.1⟩
  · rintro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hax => h x ⟨hax, by linarith [(abs_lt.mp hx).2]⟩⟩

theorem derivative_sides_iff (f : ℝ → ℝ) (a d : ℝ) :
    HasDerivative f a d ↔ HasLeftDerivative f a d ∧ HasRightDerivative f a d :=
  approaches_sides_iff _ _ _

theorem derivative_along_distance_iff (f : ℝ → ℝ) (S : Set ℝ) (a d : ℝ) :
    HasDerivativeAlong f S a d ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, 0 < |x-a| ∧ |x-a| < δ →
        |(f x - f a) / (x - a) - d| < ε := by
  rw [derivative_along_epsilon_iff]
  constructor
  · rintro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hd => h x hd.2 ⟨hx, sub_ne_zero.mp (abs_pos.mp hd.1)⟩⟩
  · rintro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hd hx => h x hx.1 ⟨abs_pos.mpr (sub_ne_zero.mpr hx.2), hd⟩⟩

theorem derivative_to_along {f : ℝ → ℝ} {a d : ℝ} (S : Set ℝ)
    (h : HasDerivative f a d) : HasDerivativeAlong f S a d := by
  apply (derivative_along_distance_iff f S a d).2
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := (derivative_epsilon_iff f a d).1 h ε hε
  exact ⟨δ, hδ, fun x _ hx => h x hx⟩

theorem derivative_along_interior_iff {f : ℝ → ℝ} {S : Set ℝ} {a d : ℝ}
    (hS : ∃ ρ > 0, ∀ x, |x-a| < ρ → x ∈ S) :
    HasDerivativeAlong f S a d ↔ HasDerivative f a d := by
  refine ⟨?_, derivative_to_along S⟩
  intro h
  apply (derivative_epsilon_iff f a d).2
  intro ε hε
  obtain ⟨ρ, hρ, hS⟩ := hS
  obtain ⟨δ, hδ, h⟩ := (derivative_along_distance_iff f S a d).1 h ε hε
  refine ⟨min δ ρ, lt_min hδ hρ, fun x hx => ?_⟩
  exact h x (hS x (hx.2.trans_le (min_le_right _ _))) ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩

theorem derivative_locality {f g : ℝ → ℝ} {a d : ℝ}
    (hfg : ∃ ρ > 0, ∀ x, |x-a| < ρ → f x = g x) :
    HasDerivative f a d ↔ HasDerivative g a d := by
  obtain ⟨ρ, hρ, heq⟩ := hfg
  have hcenter := heq a (by simpa using hρ)
  rw [derivative_epsilon_iff, derivative_epsilon_iff]
  constructor <;> intro h ε hε <;> obtain ⟨δ, hδ, h⟩ := h ε hε <;>
    refine ⟨min δ ρ, lt_min hδ hρ, fun x hx => ?_⟩
  · rw [← heq x (hx.2.trans_le (min_le_right _ _)), ← hcenter]
    exact h x ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩
  · rw [heq x (hx.2.trans_le (min_le_right _ _)), hcenter]
    exact h x ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩

-- BEGIN bridge
theorem derivative_mathlib (f : ℝ → ℝ) (a d : ℝ) :
    HasDerivative f a d ↔ HasDerivAt f d a := by
  unfold HasDerivative
  have hp : toMathlib (punctured a) = 𝓝[≠] a := by
    change toMathlib (nearWithin a {x | x ≠ a}) = 𝓝[≠] a
    rw [toMathlib_nearWithin]
    rfl
  rw [approaches_mathlib_iff, hp,
    Ch03.toMathlib_neighborhood]
  rw [hasDerivAt_iff_tendsto_slope]
  rw [slope_fun_def_field]
-- END bridge

-- BEGIN constants
theorem derivative_const (c a : ℝ) :               -- 常值函数的导数为0
    HasDerivative (fun _ => c) a 0 := by
  exact (derivative_mathlib _ _ _).2 (hasDerivAt_const a c)

theorem derivative_id (a : ℝ) :                    -- 恒等函数的导数为1
    HasDerivative (fun x => x) a 1 := by
  exact (derivative_mathlib _ _ _).2 (hasDerivAt_id a)
-- END constants

-- BEGIN square
theorem derivative_square (a : ℝ) :                -- 平方函数在a处的导数为2a
    HasDerivative (fun x => x ^ 2) a (2 * a) := by
  apply (derivative_mathlib _ _ _).2
  simpa using (hasDerivAt_id a).fun_pow 2
-- END square

-- BEGIN square_direct
theorem derivative_square_direct (a : ℝ) :          -- 直接核验差商，不调用求导法则
    HasDerivative (fun x => x ^ 2) a (2 * a) := by
  unfold HasDerivative
  apply (real_iff _ _ _).2                         -- 对每个ε证明差商距离最终小于ε
  intro ε hε
  refine ⟨ε, hε, ?_⟩                              -- 取半径δ=ε
  intro x hx hne
  change |x - a| < ε at hx
  change x ≠ a at hne
  have hden : x - a ≠ 0 := sub_ne_zero.mpr hne     -- 去心条件允许约去x-a
  change |(x ^ 2 - a ^ 2) / (x - a) - 2 * a| < ε
  have hid : (x ^ 2 - a ^ 2) / (x - a) - 2 * a = x - a := by
    field_simp [hden]
    <;> ring
  rw [hid]
  exact hx                                       -- 距离恰好就是|x-a|
-- END square_direct

-- BEGIN continuous
theorem derivative_continuous {f : ℝ → ℝ} {a d : ℝ}
    (h : HasDerivative f a d) :
    Ch04Continuity.BookContinuousAt f a := by
  unfold Ch04Continuity.BookContinuousAt
  apply (approaches_mathlib_iff _ _ _).2
  rw [Ch03.toMathlib_neighborhood, Ch03.toMathlib_neighborhood]
  exact ((derivative_mathlib _ _ _).1 h).continuousAt
-- END continuous

-- BEGIN unique
theorem derivative_unique {f : ℝ → ℝ} {a d e : ℝ}
    (hd : HasDerivative f a d) (he : HasDerivative f a e) : d = e := by
  exact ((derivative_mathlib _ _ _).1 hd).unique
    ((derivative_mathlib _ _ _).1 he)

theorem derivative_value {f : ℝ → ℝ} {a d : ℝ}
    (h : HasDerivative f a d) : deriv f a = d := by
  exact ((derivative_mathlib _ _ _).1 h).deriv
-- END unique

-- BEGIN affine
theorem derivative_affine (m b a : ℝ) :             -- mx+b在a处的导数为m
    HasDerivative (fun x => m * x + b) a m := by
  apply (derivative_mathlib _ _ _).2                 -- 转为库中的导数命题
  simpa using ((hasDerivAt_id a).const_mul m).add_const b
-- END affine

-- BEGIN reciprocal
theorem derivative_reciprocal (a : ℝ) (ha : a ≠ 0) :
    HasDerivative (fun x => 1 / x) a (-(a ^ 2)⁻¹) := by
  apply (derivative_mathlib _ _ _).2
  simpa only [one_div] using (hasDerivAt_inv ha)
-- END reciprocal

-- BEGIN stationary
theorem cubic_stationary :                         -- x³在0处导数为0，不代表局部极值
    HasDerivative (fun x : ℝ => x ^ 3) 0 0 := by
  apply (derivative_mathlib _ _ _).2
  simpa using (hasDerivAt_id (0 : ℝ)).fun_pow 3
-- END stationary

-- BEGIN remainder
theorem square_remainder (a h : ℝ) :               -- 线性近似的剩余项恰好为h²
    (a + h) ^ 2 - (a ^ 2 + (2 * a) * h) = h ^ 2 := by
  ring

theorem square_error_bound (a h η : ℝ)
    (hη : 0 ≤ η) (hh : |h| ≤ η) :                 -- 输入界η给出平方阶剩余项界
    |(a + h) ^ 2 - (a ^ 2 + (2 * a) * h)| ≤ η ^ 2 := by
  rw [square_remainder, abs_of_nonneg (sq_nonneg h)]
  nlinarith [sq_abs h, abs_nonneg h]
-- END remainder

-- BEGIN reciprocal_error
theorem reciprocal_remainder (a h : ℝ)
    (ha : a ≠ 0) (hah : a + h ≠ 0) :              -- 两个非零条件分别控制两个分母
    1 / (a + h) - (1 / a - h / a ^ 2) =
      h ^ 2 / (a ^ 2 * (a + h)) := by
  field_simp [ha, hah]
  ring
-- END reciprocal_error

end Ch06
