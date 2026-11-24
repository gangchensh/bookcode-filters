import Textbook.Ch13.Audit

namespace Ch13
open Set MeasureTheory
open scoped Interval

noncomputable def swapFailureIntegrand (z : ℝ × ℝ) : ℝ :=
  (z.1^2-z.2^2)/(z.1^2+z.2^2)^2

theorem swap_failure_vertical (x : ℝ) (hx : x ≠ 0) :
    IntervalIntegrable (fun y => swapFailureIntegrand (x,y)) volume 0 1 ∧
      (∫ y in (0 : ℝ)..1, swapFailureIntegrand (x,y)) = 1/(1+x^2) := by
  have hn (y : ℝ) : x^2+y^2 ≠ 0 := by
    exact (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)).ne'
  have hc : Continuous (fun y => swapFailureIntegrand (x,y)) := by
    have hnum : Continuous (fun y : ℝ => x^2-y^2) := by fun_prop
    have hden : Continuous (fun y : ℝ => (x^2+y^2)^2) := by fun_prop
    exact hnum.div hden (fun y => pow_ne_zero _ (hn y))
  have hi : IntervalIntegrable (fun y => swapFailureIntegrand (x,y)) volume 0 1 :=
    hc.intervalIntegrable 0 1
  refine ⟨hi,?_⟩
  have hd (y : ℝ) :
      HasDerivAt (fun t => t/(x^2+t^2)) (swapFailureIntegrand (x,y)) y := by
    have hp := (hasDerivAt_const y (x^2)).add ((hasDerivAt_id y).fun_pow 2)
    convert (hasDerivAt_id y).div hp (hn y) using 1
    · funext t
      rfl
    · simp [swapFailureIntegrand]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) hi]
  simp [add_comm]

theorem swap_failure_horizontal (y : ℝ) (hy : y ≠ 0) :
    IntervalIntegrable (fun x => swapFailureIntegrand (x,y)) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, swapFailureIntegrand (x,y)) = -(1/(1+y^2)) := by
  obtain ⟨hi,he⟩ := swap_failure_vertical y hy
  have hs : (fun x => swapFailureIntegrand (x,y)) = fun x => -swapFailureIntegrand (y,x) := by
    funext x
    simp only [swapFailureIntegrand]
    rw [← neg_div,neg_sub,add_comm (y^2)]
  rw [hs]
  exact ⟨hi.neg,by rw [intervalIntegral.integral_neg,he]⟩

theorem swap_failure_iterated_values :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, swapFailureIntegrand (x,y)) = Real.pi/4 ∧
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, swapFailureIntegrand (x,y)) = -(Real.pi/4) := by
  have hunit : (∫ x in (0 : ℝ)..1, 1/(1+x^2)) = Real.pi/4 := by
    simp only [one_div]
    rw [integral_inv_one_add_sq,Real.arctan_one,Real.arctan_zero,sub_zero]
  constructor
  · exact (intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      (fun x hx => (swap_failure_vertical x hx.1.ne').2)).trans hunit
  · rw [intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      (fun y hy => (swap_failure_horizontal y hy.1.ne').2),intervalIntegral.integral_neg,hunit]

theorem swap_failure_outer_integrable :
    IntervalIntegrable (fun x => ∫ y in (0 : ℝ)..1, swapFailureIntegrand (x,y)) volume 0 1 ∧
    IntervalIntegrable (fun y => ∫ x in (0 : ℝ)..1, swapFailureIntegrand (x,y)) volume 0 1 := by
  have hc : Continuous (fun x : ℝ => 1/(1+x^2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
  have hi : IntervalIntegrable (fun x : ℝ => 1/(1+x^2)) volume 0 1 :=
    hc.intervalIntegrable 0 1
  constructor
  · apply hi.congr_uIoo
    rw [uIoo_of_le zero_le_one]
    exact fun x hx => (swap_failure_vertical x hx.1.ne').2.symm
  · apply hi.neg.congr_uIoo
    rw [uIoo_of_le zero_le_one]
    exact fun y hy => (swap_failure_horizontal y hy.1.ne').2.symm

theorem swap_failure_zero_slices :
    (¬ IntervalIntegrable (fun y => swapFailureIntegrand (0,y)) volume 0 1) ∧
    (¬ IntervalIntegrable (fun x => swapFailureIntegrand (x,0)) volume 0 1) := by
  have hbad : ¬ IntervalIntegrable (fun x : ℝ => x^(-2 : ℝ)) volume 0 1 := by
    intro h
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h
    have hh := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).1 hi
    norm_num at hh
  have hpow (x : ℝ) (hx : 0 < x) : x^(-2 : ℝ) = (x^2)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num,Real.rpow_neg hx.le,Real.rpow_natCast]
  constructor
  · intro h
    apply hbad
    apply h.neg.congr_uIoo
    rw [uIoo_of_le zero_le_one]
    intro x hx
    change -swapFailureIntegrand (0,x) = x^(-2 : ℝ)
    rw [hpow x hx.1]
    simp only [swapFailureIntegrand,zero_pow (by norm_num : 2 ≠ 0),zero_sub,zero_add]
    field_simp [hx.1.ne']
  · intro h
    apply hbad
    apply h.congr_uIoo
    rw [uIoo_of_le zero_le_one]
    intro x hx
    change swapFailureIntegrand (x,0) = x^(-2 : ℝ)
    rw [hpow x hx.1]
    simp only [swapFailureIntegrand,zero_pow (by norm_num : 2 ≠ 0),sub_zero,add_zero]
    field_simp [hx.1.ne']

/-- Fubini would equate the two distinct iterated values if the function were absolutely integrable. -/
theorem swap_failure_not_integrable :
    ¬ IntegrableOn swapFailureIntegrand (Ioo 0 1 ×ˢ Ioo 0 1) (volume.prod volume) := by
  intro hi
  have he : ((volume : Measure ℝ).restrict (Ioc 0 1)) =
      volume.restrict (Ioo 0 1) := Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hp : Integrable swapFailureIntegrand
      (((volume : Measure ℝ).restrict (Ioc 0 1)).prod (volume.restrict (Ioc 0 1))) := by
    rw [he,Measure.prod_restrict]
    exact hi
  have hs := integral_integral_swap (f := fun x y => swapFailureIntegrand (x,y)) hp
  simp only [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
  rw [swap_failure_iterated_values.1,swap_failure_iterated_values.2] at hs
  linarith [Real.pi_pos]

end Ch13
