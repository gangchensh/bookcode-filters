import Textbook.Ch10.PowerCriteria

namespace Ch10

open Filter MeasureTheory Set
open scoped Topology Interval

private theorem scaled_power_truncation {L c C p : ℝ}
    (hL : 0 < L) (hc : 0 < c) (hcL : c ≤ L) :
    (∫ x in c..L, C*(x/L)^(-p)) = C*L * ∫ y in (c/L)..(1:ℝ), y^(-p) := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => t/L) (1/L) x := by
    simpa using (hasDerivAt_id x).div_const L
  have hf : ContinuousOn (fun y : ℝ => y^(-p)) ((fun x => x/L) '' uIcc c L) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [uIcc_of_le hcL] at hx
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (div_pos (hc.trans_le hx.1) hL).ne')).continuousWithinAt
  have h := change_variable_local (fun x _ => hd x) continuousOn_const hf
  rw [div_self hL.ne'] at h
  rw [← h,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change C*(x/L)^(-p) = C*L*((x/L)^(-p)*(1/L))
  field_simp

private theorem scaled_power_integrable {L c C p : ℝ}
    (hL : 0 < L) (hc : 0 < c) (hcL : c ≤ L) :
    IntervalIntegrable (fun x => C*(x/L)^(-p)) volume c L := by
  apply ContinuousOn.intervalIntegrable_of_Icc hcL
  apply continuousOn_const.mul
  intro x hx
  have h : ContinuousAt (fun y : ℝ => y/L) x := (continuous_id.div_const L).continuousAt
  have hpow : ContinuousAt (fun y : ℝ => y^(-p)) ((fun y : ℝ => y/L) x) :=
    Real.continuousAt_rpow_const _ _ (Or.inl (div_pos (hc.trans_le hx.1) hL).ne')
  have hcomp : ContinuousAt ((fun y : ℝ => y^(-p)) ∘ (fun y : ℝ => y/L)) x :=
    ContinuousAt.comp (f := fun y : ℝ => y/L) (x := x) hpow h
  exact hcomp.continuousWithinAt

private theorem scaled_cutoff {L : ℝ} (hL : 0 < L) :
    Tendsto (fun c : ℝ => c/L) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_,?_⟩
  · simpa using ((continuous_id.div_const L).continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact div_pos hc hL

private theorem scaled_power_integral {L C p : ℝ} (hL : 0 < L) (hp : p < 1) :
    ImproperEndpointLeft (fun x => C*(x/L)^(-p)) 0 L (C*L/(1-p)) := by
  refine ⟨fun c hc hcL => scaled_power_integrable hL hc hcL,?_⟩
  have ht := ((origin_power_converges hp).2.comp (scaled_cutoff hL)).const_mul (C*L)
  have ht' : Tendsto (fun c => C*L*(∫ y in (c/L)..(1:ℝ), y^(-p)))
      (𝓝[>] (0:ℝ)) (𝓝 (C*L/(1-p))) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_assoc,one_mul] using ht
  apply ht'.congr'
  filter_upwards [Ioo_mem_nhdsGT hL] with c hc
  exact (scaled_power_truncation hL hc.1 hc.2.le).symm

private theorem scaled_power_diverges {L C p : ℝ} (hL : 0 < L) (hC : 0 < C) (hp : 1 ≤ p) :
    Tendsto (fun c => ∫ x in c..L, C*(x/L)^(-p)) (𝓝[>] (0:ℝ)) atTop := by
  have ht := Tendsto.const_mul_atTop (mul_pos hC hL)
    ((power_diverges_at_zero hp).comp (scaled_cutoff hL))
  have ht' : Tendsto (fun c => C*L*(∫ y in (c/L)..(1:ℝ), y^(-p)))
      (𝓝[>] (0:ℝ)) atTop := by
    simpa only [Function.comp_def] using ht
  apply ht'.congr'
  filter_upwards [Ioo_mem_nhdsGT hL] with c hc
  exact (scaled_power_truncation hL hc.1 hc.2.le).symm

private theorem moment_integral {L C p : ℝ} (hL : 0 < L) (hp : p < 2) :
    ImproperEndpointLeft (fun x => x*(C*(x/L)^(-p))) 0 L (C*L^2/(2-p)) := by
  have he (x : ℝ) (hx : 0 < x) :
      x*(C*(x/L)^(-p)) = (C*L)*(x/L)^(-(p-1)) := by
    have hz := div_pos hx hL
    rw [show -(p-1) = 1 + (-p) by ring,Real.rpow_add hz,Real.rpow_one]
    field_simp
  have hs := scaled_power_integral (C := C*L) hL (show p-1 < 1 by linarith)
  rw [show 1-(p-1) = 2-p by ring,show C*L*L = C*L^2 by ring] at hs
  refine ⟨fun c hc hcL => ?_,?_⟩
  · apply (hs.1 c hc hcL).congr
    intro x hx
    rw [uIoc_of_le hcL] at hx
    exact (he x (hc.trans hx.1)).symm
  · apply hs.2.congr'
    filter_upwards [Ioo_mem_nhdsGT hL] with c hc
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hc.2.le]
    intro x hx
    exact (he x (hc.1.trans_le hx.1)).symm

theorem singular_density_centroid {L ρ p : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hp : p < 1) :
    ImproperEndpointLeft (fun x => ρ*(x/L)^(-p)) 0 L (ρ*L/(1-p)) ∧
    ImproperEndpointLeft (fun x => x*(ρ*(x/L)^(-p))) 0 L (ρ*L^2/(2-p)) ∧
    (ρ*L^2/(2-p))/(ρ*L/(1-p)) = L*(1-p)/(2-p) ∧
    L*(1-p)/(2-p) ∈ Ioo 0 L := by
  have h₁ : 0 < 1-p := by linarith
  have h₂ : 0 < 2-p := by linarith
  refine ⟨scaled_power_integral hL hp,moment_integral hL (by linarith),?_,⟨by positivity,?_⟩⟩
  · field_simp
  · apply (div_lt_iff₀ h₂).2
    nlinarith

theorem singular_density_infinite_mass {L ρ p : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ) (hp : 1 ≤ p) (hp' : p < 2) :
    Tendsto (fun c => ∫ x in c..L, ρ*(x/L)^(-p)) (𝓝[>] (0:ℝ)) atTop ∧
    ImproperEndpointLeft (fun x => x*(ρ*(x/L)^(-p))) 0 L (ρ*L^2/(2-p)) :=
  ⟨scaled_power_diverges hL hρ hp,moment_integral hL hp'⟩

end Ch10
