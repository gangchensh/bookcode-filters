import Textbook.Ch06.Derivatives

namespace Ch06
open Ch02 Ch03 Ch03Approach
open scoped Topology

theorem derivative_sqrt (a : ℝ) (ha : 0 < a) :
    HasDerivative Real.sqrt a (1 / (2 * Real.sqrt a)) :=
  (derivative_mathlib _ _ _).2 (Real.hasDerivAt_sqrt ha.ne')

theorem abs_has_no_derivative : ¬ ∃ d, HasDerivative (abs : ℝ → ℝ) 0 d := by
  rintro ⟨d, hd⟩
  exact not_differentiableAt_abs_zero ((derivative_mathlib _ _ _).1 hd).differentiableAt

theorem square_right_at_zero : HasRightDerivative (fun x => x^2) 0 0 :=
  ((derivative_sides_iff _ _ _).1 (by simpa using derivative_square 0)).2

theorem quotient_at_center (f : ℝ → ℝ) (a : ℝ) :
    (f a - f a) / (a - a) = 0 := by simp

theorem increment_limit_iff (q : ℝ → ℝ) (d : ℝ) :
    Approaches q (punctured 0) (neighborhoodFilter d) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ h, 0 < |h| ∧ |h| < δ → |q h-d| < ε := by
  simpa only [Ch03Statements.PuncturedLimit, sub_zero] using Ch03Statements.punctured_limit_iff q 0 d

theorem derivative_increment_iff (f : ℝ → ℝ) (a d : ℝ) :
    HasDerivative f a d ↔
      Approaches (fun h => (f (a+h) - f a)/h) (punctured 0) (neighborhoodFilter d) := by
  rw [derivative_epsilon_iff, increment_limit_iff]
  constructor
  · intro H ε hε
    obtain ⟨δ, hδ, H⟩ := H ε hε
    refine ⟨δ, hδ, fun h hh => ?_⟩
    have he : a+h-a = h := by ring
    simpa only [he] using H (a+h) (by simpa only [he, sub_zero] using hh)
  · intro H ε hε
    obtain ⟨δ, hδ, H⟩ := H ε hε
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have he : a+(x-a) = x := by ring
    simpa only [he] using H (x-a) (by simpa only [sub_zero] using hx)

def LittleOIncrement (r : ℝ → ℝ) : Prop :=
  r 0 = 0 ∧ Approaches (fun h => r h / h) (punctured 0) (neighborhoodFilter 0)

def linearRemainder (f : ℝ → ℝ) (a d h : ℝ) : ℝ :=
  f (a+h) - f a - d*h

theorem derivative_linear_iff (f : ℝ → ℝ) (a d : ℝ) :
    HasDerivative f a d ↔ LittleOIncrement (linearRemainder f a d) := by
  rw [derivative_increment_iff, LittleOIncrement, increment_limit_iff, increment_limit_iff]
  have hz : linearRemainder f a d 0 = 0 := by simp [linearRemainder]
  simp only [hz, true_and]
  have he (h : ℝ) (hh : h ≠ 0) :
      linearRemainder f a d h / h = (f (a+h)-f a)/h-d := by
    unfold linearRemainder
    field_simp
    <;> ring
  constructor <;> intro H ε hε <;> obtain ⟨δ, hδ, H⟩ := H ε hε <;>
    refine ⟨δ, hδ, fun h hh => ?_⟩
  · simpa only [he h (abs_pos.mp (by simpa only [sub_zero] using hh.1)), sub_zero] using H h hh
  · simpa only [he h (abs_pos.mp (by simpa only [sub_zero] using hh.1)), sub_zero] using H h hh

def tangentModel (f : ℝ → ℝ) (a d x : ℝ) : ℝ := f a + d*(x-a)

def differential (d : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun h := d*h
  map_add' x y := mul_add d x y
  map_smul' c x := by simp only [smul_eq_mul, RingHom.id_apply]; ring

noncomputable def RelativeSensitivity (f : ℝ → ℝ) (a d : ℝ) : ℝ := a*d/f a

theorem square_differential_example :
    HasDerivative (fun x : ℝ => x^2) 3 6 ∧
    differential 6 (0.02 : ℝ) = 0.12 ∧ (3.02 : ℝ)^2 - 3^2 = 0.1204 := by
  constructor
  · convert derivative_square 3 using 1 <;> norm_num
  · norm_num [differential]

theorem square_tolerance (a h η : ℝ) (hη : 0 ≤ η) (hh : |h| ≤ η) :
    |(a+h)^2-tangentModel (fun x => x^2) a (2*a) (a+h)| ≤ η^2 := by
  simpa [tangentModel, show a+h-a = h by ring] using square_error_bound a h η hη hh

theorem area_sensitivity (r : ℝ) (hr : 0 < r) :
    HasDerivative (fun x => Real.pi*x^2) r (2*Real.pi*r) ∧
    RelativeSensitivity (fun x => Real.pi*x^2) r (2*Real.pi*r) = 2 := by
  constructor
  · apply (derivative_mathlib _ _ _).2
    convert ((hasDerivAt_id r).fun_pow 2).const_mul Real.pi using 1 <;> simp only [id_eq] <;> ring
  · unfold RelativeSensitivity
    field_simp [hr.ne', Real.pi_ne_zero]
    <;> ring

end Ch06
