import Textbook.Ch10.RootExamples

namespace Ch10

open Filter MeasureTheory Set
open scoped Topology Interval Pointwise

theorem reciprocal_truncation (p : ℝ) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    (∫ x in c..(1:ℝ), x ^ (-p)) = ∫ y in (1:ℝ)..c⁻¹, y ^ (p-2) := by
  have hci : 1 ≤ c⁻¹ := (one_le_inv₀ hc).2 hc₁
  have hd (y : ℝ) (hy : y ∈ uIcc 1 c⁻¹) : 0 < y := by
    rw [uIcc_of_le hci] at hy
    exact zero_lt_one.trans_le hy.1
  have h := change_variable_local
    (g := fun y : ℝ => y⁻¹) (dg := fun y : ℝ => -(y^2)⁻¹)
    (f := fun x : ℝ => x ^ (-p)) (a := 1) (b := c⁻¹)
    (fun y hy => hasDerivAt_inv (hd y hy).ne')
    (((continuous_id.pow 2).continuousOn.inv₀
      (fun y hy => pow_ne_zero _ (hd y hy).ne')).neg)
    (by
      rintro _ ⟨y,hy,rfl⟩
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (inv_pos.mpr (hd y hy)).ne')).continuousWithinAt)
  simp only [inv_one, inv_inv] at h
  rw [intervalIntegral.integral_symm c (1:ℝ)] at h
  have he' : (∫ y in (1:ℝ)..c⁻¹, (y⁻¹) ^ (-p) * (-(y^2)⁻¹)) =
      -(∫ y in (1:ℝ)..c⁻¹, y ^ (p-2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    have hy₀ := hd y hy
    change (y⁻¹) ^ (-p) * (-(y^2)⁻¹) = -(y ^ (p-2))
    rw [← Real.rpow_neg_one y, ← Real.rpow_mul hy₀.le]
    rw [show (-1:ℝ) * -p = p by ring, sub_eq_add_neg,Real.rpow_add hy₀,
      Real.rpow_neg hy₀.le,Real.rpow_two]
    ring
  linarith

theorem reciprocal_improper_iff (p L : ℝ) :
    ImproperEndpointLeft (fun x => x ^ (-p)) 0 1 L ↔
      ImproperRight (fun y => y ^ (p-2)) 1 L := by
  have he : (fun c => ∫ x in c..(1:ℝ), x ^ (-p)) =ᶠ[𝓝[>] (0:ℝ)]
      fun c => (fun T => ∫ y in (1:ℝ)..T, y ^ (p-2)) c⁻¹ :=
    Filter.Eventually.mono (Ioo_mem_nhdsGT zero_lt_one)
      fun c hc => reciprocal_truncation p hc.1 hc.2.le
  have hl : Tendsto (fun c => ∫ x in c..(1:ℝ), x ^ (-p)) (𝓝[>] (0:ℝ)) (𝓝 L) ↔
      Tendsto (fun T => ∫ y in (1:ℝ)..T, y ^ (p-2)) atTop (𝓝 L) := by
    rw [tendsto_congr' he]
    change Tendsto ((fun T => ∫ y in (1:ℝ)..T, y ^ (p-2)) ∘ Inv.inv) (𝓝[>] (0:ℝ)) (𝓝 L) ↔ _
    rw [← tendsto_map'_iff]
    change Tendsto _ ((𝓝[>] (0:ℝ))⁻¹) _ ↔ _
    rw [inv_nhdsGT_zero]
  constructor
  · intro h
    refine ⟨fun T hT => ContinuousOn.intervalIntegrable_of_Icc hT ?_,hl.mp h.2⟩
    exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt
  · intro h
    refine ⟨fun c hc hc₁ => ContinuousOn.intervalIntegrable_of_Icc hc₁ ?_,hl.mpr h.2⟩
    exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (hc.trans_le hx.1).ne')).continuousWithinAt

noncomputable def betaHalfIntegrand (x : ℝ) : ℝ := 1 / Real.sqrt (x*(1-x))

private theorem betaHalf_continuous : ContinuousOn betaHalfIntegrand (Ioo 0 1) := by
  unfold betaHalfIntegrand
  apply continuousOn_const.div (by fun_prop)
  intro x hx
  exact (Real.sqrt_pos_of_pos (mul_pos hx.1 (sub_pos.mpr hx.2))).ne'

theorem beta_half_truncation {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ x in a..b, betaHalfIntegrand x) =
      Real.arcsin (2*b-1) - Real.arcsin (2*a-1) := by
  have hsub : Icc a b ⊆ Ioo (0:ℝ) 1 :=
    fun _ hx => ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => Real.arcsin (2*t-1)) (betaHalfIntegrand x) x := by
    rw [uIcc_of_le hab] at hx
    have hx' := hsub hx
    have h₁ : 2*x-1 ≠ -1 := by linarith [hx'.1]
    have h₂ : 2*x-1 ≠ 1 := by linarith [hx'.2]
    have hd' : HasDerivAt (fun t : ℝ => 2*t-1) 2 x := by
      simpa using (((hasDerivAt_id x).const_mul (2:ℝ)).sub_const 1)
    have hs : Real.sqrt (1-(2*x-1)^2) = 2 * Real.sqrt (x*(1-x)) := by
      rw [show 1-(2*x-1)^2 = 4*(x*(1-x)) by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    have hvalue : (1 / Real.sqrt (1-(2*x-1)^2)) * 2 = betaHalfIntegrand x := by
      unfold betaHalfIntegrand
      rw [hs]
      have hn := (Real.sqrt_pos_of_pos (mul_pos hx'.1 (sub_pos.mpr hx'.2))).ne'
      field_simp
    rw [← hvalue]
    simpa only [Function.comp_def] using (Real.hasDerivAt_arcsin h₁ h₂).comp x hd'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((betaHalf_continuous.mono hsub).intervalIntegrable_of_Icc hab)

theorem beta_half_two_endpoints :
    ImproperEndpointLeft betaHalfIntegrand 0 (1/2) (Real.pi/2) ∧
    ImproperEndpointRight betaHalfIntegrand (1/2) 1 (Real.pi/2) := by
  have hc : Continuous (fun x : ℝ => Real.arcsin (2*x-1)) := by fun_prop
  have hmid : Real.arcsin (2*(1/2:ℝ)-1) = 0 := by norm_num
  have hzero : Real.arcsin (2*(0:ℝ)-1) = -(Real.pi/2) := by norm_num [Real.arcsin_neg]
  have hone : Real.arcsin (2*(1:ℝ)-1) = Real.pi/2 := by norm_num
  constructor
  · refine ⟨fun c hc hc' => (betaHalf_continuous.mono (fun _ hx =>
      ⟨hc.trans_le hx.1,hx.2.trans_lt (by norm_num)⟩)).intervalIntegrable_of_Icc hc',?_⟩
    have hl := (hc.continuousAt (x := (0:ℝ))).continuousWithinAt (s := Ioi 0)
    have ht := (tendsto_const_nhds (x := (0:ℝ))).sub hl
    change Tendsto _ (𝓝[>] (0:ℝ)) (𝓝 (0 - Real.arcsin (2*0-1))) at ht
    rw [hzero] at ht
    have ht' : Tendsto (fun c : ℝ => 0 - Real.arcsin (2*c-1)) (𝓝[>] (0:ℝ))
        (𝓝 (Real.pi/2)) := by simpa using ht
    apply ht'.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1/2)] with c hc
    rw [beta_half_truncation hc.1 hc.2.le (by norm_num),hmid]
  · refine ⟨fun c hc hc' => (betaHalf_continuous.mono (fun _ hx =>
      ⟨(by norm_num : (0:ℝ) < 1/2).trans_le hx.1,hx.2.trans_lt hc'⟩)).intervalIntegrable_of_Icc hc,?_⟩
    have hl := (hc.continuousAt (x := (1:ℝ))).continuousWithinAt (s := Iio 1)
    change Tendsto (fun x : ℝ => Real.arcsin (2*x-1)) (𝓝[<] (1:ℝ))
      (𝓝 (Real.arcsin (2*1-1))) at hl
    rw [hone] at hl
    apply hl.congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1/2:ℝ) < 1)] with c hc
    rw [beta_half_truncation (by norm_num) hc.1.le hc.2,hmid,sub_zero]

end Ch10
