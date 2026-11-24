import Textbook.Ch06.Counterexamples

namespace Ch06
open Ch02 Ch03 Ch03Approach

noncomputable def joinedModel (c x : ℝ) : ℝ := if x ≤ 0 then x^2 else c*x

theorem joined_model (c : ℝ) :
    Ch04Continuity.BookContinuousAt (joinedModel c) 0 ∧
    HasLeftDerivative (joinedModel c) 0 0 ∧ HasRightDerivative (joinedModel c) 0 c ∧
    ((∃ d, HasDerivative (joinedModel c) 0 d) ↔ c = 0) := by
  have hL : HasLeftDerivative (joinedModel c) 0 0 := by
    apply (derivative_left_epsilon_iff _ _ _).2
    intro ε hε
    refine ⟨ε,hε,fun x hx => ?_⟩
    simp only [joinedModel, if_pos hx.2.le, le_refl, if_true, zero_pow (by decide : (2:ℕ) ≠ 0),
      sub_zero]
    rw [show x^2/x = x by field_simp [hx.2.ne]]
    rw [abs_of_neg hx.2]
    linarith [hx.1]
  have hR : HasRightDerivative (joinedModel c) 0 c := by
    apply (derivative_right_epsilon_iff _ _ _).2
    intro ε hε
    refine ⟨1,zero_lt_one,fun x hx => ?_⟩
    simp only [joinedModel, if_neg (not_le.mpr hx.1), le_refl, if_true,
      zero_pow (by decide : (2:ℕ) ≠ 0), sub_zero]
    rw [mul_div_cancel_right₀ _ hx.1.ne', sub_self, abs_zero]
    exact hε
  have hc : Ch04Continuity.BookContinuousAt (joinedModel c) 0 := by
    unfold Ch04Continuity.BookContinuousAt
    apply (real_iff _ _ _).2
    intro ε hε
    let K := |c|+1
    have hK : 0 < K := by dsimp [K]; positivity
    refine ⟨min 1 (ε/K),lt_min zero_lt_one (div_pos hε hK),fun x hx => ?_⟩
    change |x-0| < min 1 (ε/K) at hx
    rw [sub_zero] at hx
    have hx1 := hx.trans_le (min_le_left _ _)
    have hxε := (lt_div_iff₀ hK).1 (hx.trans_le (min_le_right _ _))
    have hz : joinedModel c 0 = 0 := by simp [joinedModel]
    change |joinedModel c x - joinedModel c 0| < ε
    rw [hz, sub_zero, joinedModel]
    split
    · rw [abs_of_nonneg (sq_nonneg _), ← sq_abs x]
      nlinarith [abs_nonneg x, abs_nonneg c, mul_nonneg (abs_nonneg x) (abs_nonneg c)]
    · rw [abs_mul]
      dsimp [K] at hxε
      nlinarith [abs_nonneg x]
  refine ⟨hc,hL,hR,⟨?_,?_⟩⟩
  · rintro ⟨d, hd⟩
    obtain ⟨hdL, hdR⟩ := (derivative_sides_iff _ _ _).1 hd
    have heL := Ch03Rules.real_limit_unique (left_proper 0) hdL hL
    have heR := Ch03Rules.real_limit_unique (right_proper 0) hR hdR
    exact heR.trans heL
  · intro h
    exact ⟨0,(derivative_sides_iff _ _ _).2 ⟨hL,h ▸ hR⟩⟩

noncomputable def jumpedModel (x : ℝ) : ℝ := if x < 0 then x else x+1

theorem jumped_no_left_derivative : ¬ ∃ d, HasLeftDerivative jumpedModel 0 d := by
  rintro ⟨d, hd⟩
  obtain ⟨δ, hδ, H⟩ := (derivative_left_epsilon_iff _ _ _).1 hd 1 zero_lt_one
  let K := |d|+2
  have hK : 0 < K := by dsimp [K]; positivity
  let t := min δ (1/K)/2
  have ht : 0 < t := half_pos (lt_min hδ (one_div_pos.mpr hK))
  have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ (1/K)]
  have htK : t < 1/K := (half_lt_self (lt_min hδ (one_div_pos.mpr hK))).trans_le (min_le_right _ _)
  have htK' := (lt_div_iff₀ hK).1 htK
  have hrec : K < 1/t := (lt_div_iff₀ ht).2 (by linarith)
  have h := H (-t) ⟨by linarith, neg_neg_of_pos ht⟩
  simp only [jumpedModel, if_pos (neg_neg_of_pos ht), lt_self_iff_false, if_false,
    zero_add, sub_zero] at h
  have he : (-t-1)/(-t) = 1+1/t := by field_simp [ht.ne'] <;> ring
  rw [he] at h
  dsimp [K] at hrec
  linarith [(abs_lt.mp h).2, le_abs_self d]

theorem small_perturbation_not_enough :
    Ch04Continuity.BookContinuousAt (fun x : ℝ => 3*x+|x|) 0 ∧
      ¬ ∃ d, HasDerivative (fun x : ℝ => 3*x+|x|) 0 d := by
  have ha := ((derivative_mathlib _ _ _).1 (derivative_affine 3 0 0))
  have ha' : HasDerivAt (fun x : ℝ => 3*x) 3 0 := by simpa using ha
  refine ⟨(Ch04Continuity.continuous_mathlib _ _).2
    (ha'.continuousAt.add ((continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt)), ?_⟩
  rintro ⟨d, hd⟩
  have hs := ((derivative_mathlib _ _ _).1 hd).sub ha'
  have he : ((fun x : ℝ => 3*x+|x|) - fun x => 3*x) = abs := by
    funext x
    simp [Pi.sub_apply]
  rw [he] at hs
  exact abs_has_no_derivative ⟨d-3, (derivative_mathlib _ _ _).2 hs⟩

theorem cusp_no_derivative :
    Ch04Continuity.BookContinuousAt (fun x : ℝ => Real.sqrt |x|) 0 ∧
      ¬ ∃ d, HasDerivative (fun x : ℝ => Real.sqrt |x|) 0 d := by
  refine ⟨(Ch04Continuity.continuous_mathlib _ _).2
    (Real.continuous_sqrt.comp continuous_abs).continuousAt, ?_⟩
  rintro ⟨d, hd⟩
  have hr := ((derivative_sides_iff _ _ _).1 hd).2
  apply sqrt_right_no_finite
  refine ⟨d, (derivative_right_epsilon_iff _ _ _).2 ?_⟩
  intro ε hε
  obtain ⟨δ,hδ,H⟩ := (derivative_right_epsilon_iff _ _ _).1 hr ε hε
  refine ⟨δ,hδ,fun x hx => ?_⟩
  have hp : 0 < x := hx.1
  simpa only [abs_of_pos hp, abs_zero] using H x hx

noncomputable def oscillatingModel (x : ℝ) : ℝ := x^2*Real.sin (1/x)

theorem oscillating_derivative_zero : HasDerivative oscillatingModel 0 0 := by
  have h := (derivative_mathlib _ _ _).1 oscillatory_remainder
  have hlin : HasDerivAt (fun x : ℝ => 3*x) 3 0 := by
    simpa using (derivative_mathlib _ _ _).1 (derivative_affine 3 0 0)
  have hs := h.sub hlin
  have he : ((fun x : ℝ => 3*x+x^2*Real.sin (1/x)) - fun x => 3*x) = oscillatingModel := by
    funext x
    simp only [Pi.sub_apply, oscillatingModel]
    ring
  rw [he, sub_self] at hs
  exact (derivative_mathlib _ _ _).2 hs

theorem oscillating_derivative_nonzero (x : ℝ) (hx : x ≠ 0) :
    HasDerivative oscillatingModel x (2*x*Real.sin (1/x)-Real.cos (1/x)) := by
  apply (derivative_mathlib _ _ _).2
  have h := ((hasDerivAt_id x).fun_pow 2).mul ((hasDerivAt_inv hx).sin)
  convert h using 1
  · funext y
    simp only [oscillatingModel, one_div, id_eq, Pi.mul_apply]
  · simp only [one_div, id_eq]
    field_simp [hx]
    <;> ring

theorem oscillating_derivative_discontinuous :
    ¬ ContinuousAt (deriv oscillatingModel) 0 := by
  intro hc
  obtain ⟨δ,hδ,H⟩ := Metric.continuousAt_iff.mp hc 1 zero_lt_one
  have hpi : 0 < 2*Real.pi := by positivity
  obtain ⟨n,hn⟩ := exists_nat_gt (1/(δ*(2*Real.pi)))
  have hn' : 0 < (n:ℝ) := (one_div_pos.mpr (mul_pos hδ hpi)).trans hn
  let x := 1/((n:ℝ)*(2*Real.pi))
  have hx : 0 < x := one_div_pos.mpr (mul_pos hn' hpi)
  have hxδ : x < δ := by
    apply (div_lt_iff₀ (mul_pos hn' hpi)).2
    have hn'' := (div_lt_iff₀ (mul_pos hδ hpi)).1 hn
    calc
      1 < (n:ℝ)*(δ*(2*Real.pi)) := hn''
      _ = δ*((n:ℝ)*(2*Real.pi)) := by ring
  have he : 1/x = (n:ℝ)*(2*Real.pi) := by simp [x, one_div]
  have hsin : Real.sin ((n:ℝ)*(2*Real.pi)) = 0 := by
    simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 n
  have hdx := derivative_value (oscillating_derivative_nonzero x hx.ne')
  rw [he, hsin, Real.cos_nat_mul_two_pi, mul_zero, zero_sub] at hdx
  have h := H (show dist x 0 < δ by simpa [Real.dist_eq, abs_of_pos hx] using hxδ)
  rw [hdx, derivative_value oscillating_derivative_zero] at h
  norm_num [Real.dist_eq] at h

end Ch06
