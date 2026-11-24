import Textbook.Ch06.Statements

namespace Ch06
open Ch02 Ch03 Ch03Approach

theorem remainder_bound_iff (r : ℝ → ℝ) (hr : r 0 = 0) :
    LittleOIncrement r ↔
      ∀ ε > 0, ∃ δ > 0, ∀ h, |h| < δ → |r h| ≤ ε*|h| := by
  rw [LittleOIncrement, increment_limit_iff]
  simp only [hr, true_and, sub_zero]
  constructor
  · intro H ε hε
    obtain ⟨δ, hδ, H⟩ := H ε hε
    refine ⟨δ, hδ, fun h hh => ?_⟩
    by_cases hz : h = 0
    · simp [hz, hr]
    · have ha := abs_pos.mpr hz
      have he := H h ⟨ha, hh⟩
      rw [abs_div, div_lt_iff₀ ha] at he
      exact he.le
  · intro H ε hε
    obtain ⟨δ, hδ, H⟩ := H (ε/2) (by positivity)
    refine ⟨δ, hδ, fun h hh => ?_⟩
    rw [abs_div, div_lt_iff₀ hh.1]
    exact (H h hh.2).trans_lt (mul_lt_mul_of_pos_right (by linarith) hh.1)

theorem local_increment_bound {f : ℝ → ℝ} {a d : ℝ}
    (hd : HasDerivative f a d) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ h, |h| < δ → |f (a+h)-f a| ≤ (|d|+η)*|h| := by
  obtain ⟨δ, hδ, H⟩ := (remainder_bound_iff _ (by simp [linearRemainder])).1
    ((derivative_linear_iff _ _ _).1 hd) η hη
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have he : f (a+h)-f a = d*h + linearRemainder f a d h := by
    unfold linearRemainder
    ring
  calc
    |f (a+h)-f a| = |d*h + linearRemainder f a d h| := by rw [← he]
    _ ≤ |d*h| + |linearRemainder f a d h| := abs_add_le _ _
    _ ≤ (|d|+η)*|h| := by
      rw [abs_mul, add_mul]
      exact add_le_add_right (H h hh) _

theorem positive_derivative_local {f : ℝ → ℝ} {a d : ℝ}
    (hd : HasDerivative f a d) (hp : 0 < d) :
    ∃ δ > 0, (∀ h, 0 < h → h < δ → f a < f (a+h)) ∧
      (∀ h, -δ < h → h < 0 → f (a+h) < f a) := by
  obtain ⟨δ, hδ, H⟩ := (increment_limit_iff _ _).1
    ((derivative_increment_iff _ _ _).1 hd) (d/2) (by positivity)
  have Hpos (h : ℝ) (h0 : 0 < |h|) (hh : |h| < δ) :
      0 < (f (a+h)-f a)/h := by
    have hbound := H h (by simpa only [sub_zero] using And.intro h0 hh)
    linarith [(abs_lt.mp hbound).1]
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro h hh hlt
    have hq := Hpos h (abs_pos.mpr hh.ne') (by simpa [abs_of_pos hh] using hlt)
    have := (lt_div_iff₀ hh).1 hq
    linarith
  · intro h hlt hh
    have hq := Hpos h (abs_pos.mpr hh.ne) (by rw [abs_of_neg hh]; linarith)
    have := (lt_div_iff_of_neg hh).1 hq
    linarith

theorem tangent_unique {f : ℝ → ℝ} {a d : ℝ} (hd : HasDerivative f a d) (c : ℝ) :
    LittleOIncrement (linearRemainder f a c) ↔ c = d := by
  rw [← derivative_linear_iff]
  exact ⟨fun hc => derivative_unique hc hd, fun hc => hc.symm ▸ hd⟩

theorem abs_symmetric_zero (h : ℝ) :
    (|0+h|-|0-h|)/(2*h) = 0 := by simp

theorem affine_tangent (m b a x : ℝ) :
    tangentModel (fun t => m*t+b) a m x = m*x+b := by
  unfold tangentModel
  ring

theorem cubic_tangent_sign (x : ℝ) :
    (x < 0 → x^3 < 0) ∧ (0 < x → 0 < x^3) := by
  refine ⟨fun hx => ?_, fun hx => pow_pos hx _⟩
  have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx.ne
  simpa only [pow_succ] using mul_neg_of_pos_of_neg hx2 hx

theorem motion_model (s₀ v₀ γ t h C : ℝ) (hC : |γ| ≤ C) :
    HasDerivative (fun x => s₀+v₀*x+γ*x^2) t (v₀+2*γ*t) ∧
      linearRemainder (fun x => s₀+v₀*x+γ*x^2) t (v₀+2*γ*t) h = γ*h^2 ∧
      |linearRemainder (fun x => s₀+v₀*x+γ*x^2) t (v₀+2*γ*t) h| ≤ C*h^2 := by
  have he : linearRemainder (fun x => s₀+v₀*x+γ*x^2) t (v₀+2*γ*t) h = γ*h^2 := by
    unfold linearRemainder
    ring
  refine ⟨?_, he, ?_⟩
  · apply (derivative_mathlib _ _ _).2
    convert (((hasDerivAt_id t).const_mul v₀).add_const s₀).add
      (((hasDerivAt_id t).fun_pow 2).const_mul γ) using 1
    · funext x; simp only [Pi.add_apply, id_eq]; ring
    · simp only [id_eq]; ring
  · rw [he, abs_mul, abs_of_nonneg (sq_nonneg h)]
    exact mul_le_mul_of_nonneg_right hC (sq_nonneg h)

theorem affine_sensitivity (x : ℝ) (hx : x ≠ 0) :
    HasDerivative (fun y => 3*y+100) x 3 ∧ (3*x+100)/x = 3+100/x := by
  refine ⟨derivative_affine 3 100 x, ?_⟩
  field_simp

theorem units_change {s : ℝ → ℝ} {t d : ℝ} (hd : HasDerivative s t d) :
    HasDerivative (fun τ => 100*s (τ/1000)) (1000*t) (d/10) := by
  apply (derivative_mathlib _ _ _).2
  have h := (derivative_mathlib _ _ _).1 hd
  have hi := (hasDerivAt_id (1000*t)).div_const 1000
  have he : (id (1000*t))/1000 = t := by simp
  rw [← he] at h
  convert (h.comp (1000*t) hi).const_mul 100 using 1 <;> (try simp only [id_eq, Function.comp_apply]) <;> ring

end Ch06
