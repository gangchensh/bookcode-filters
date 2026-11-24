import Textbook.Ch10.Audit
import Textbook.Ch09.Accumulation

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem finite_endpoint_agreement {f : ℝ → ℝ} {a b I : ℝ}
    (hab : a < b) (h : Ch09.HasTaggedIntegral f a b I) :
    ImproperEndpointLeft f a b I := by
  obtain ⟨hi,hI⟩ := Ch09.tagged_measure_agreement hab h
  obtain ⟨M,_,hM⟩ := Ch09.tagged_integrable_bounded hab h
  have hint (c : ℝ) (hc : c ∈ Icc a b) : IntervalIntegrable f volume c b := by
    apply hi.mono_set
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc hc (right_mem_Icc.mpr hab.le)
  refine ⟨fun c hc hcb => hint c ⟨hc.le,hcb⟩,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d := ε/(M+1)
  have hM₀ := (abs_nonneg (f a)).trans (hM a (left_mem_Icc.mpr hab.le))
  have hd : 0 < d := div_pos hε (by linarith)
  have hd' : d*(M+1) = ε := div_mul_cancel₀ _ (by linarith)
  have hclose : ∀ᶠ c in 𝓝[>] a, c ∈ Ioo a b ∧ dist c a < d := by
    have he : ∀ᶠ c in 𝓝[>] a, c < b :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hab)
    have hdist : ∀ᶠ c in 𝓝[>] a, dist c a < d :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds a hd)
    filter_upwards [self_mem_nhdsWithin,he,hdist] with c hc hcb hc'
    exact ⟨⟨hc,hcb⟩,hc'⟩
  filter_upwards [hclose] with c hc
  have hca : c ∈ Icc a b := ⟨hc.1.1.le,hc.1.2.le⟩
  have he : (∫ x in a..c, f x) + (∫ x in c..b, f x) = I := by
    rw [← hI]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hi.trans (hint c hca).symm) (hint c hca)
  rw [Real.dist_eq, ← he]
  have he' : (∫ x in c..b, f x) -
      ((∫ x in a..c, f x)+(∫ x in c..b, f x)) = -(∫ x in a..c, f x) := by ring
  rw [he',abs_neg]
  have hb : ∀ x ∈ Ι a c, ‖f x‖ ≤ M := by
    rw [uIoc_of_le hca.1]
    intro x hx
    rw [Real.norm_eq_abs]
    exact hM x ⟨hx.1.le,hx.2.trans hca.2⟩
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hca.1)] at hnorm
  have hdist := hc.2
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hca.1)] at hdist
  exact hnorm.trans_lt (by nlinarith)

theorem log_one_plus_integral :
    (∫ x in (0:ℝ)..1, Real.log (1+x)) = 2*Real.log 2 - 1 := by
  have hd (x : ℝ) (hx : x ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun t => (1+t)*Real.log (1+t)-(1+t)) (Real.log (1+x)) x := by
    rw [uIcc_of_le zero_le_one] at hx
    have hn : 1+x ≠ 0 := by linarith [hx.1]
    have h₁ := (hasDerivAt_id' x).const_add 1
    have h₂ := (Real.hasDerivAt_log hn).comp x h₁
    convert (h₁.mul h₂).sub h₁ using 1
    · rfl
    · dsimp
      field_simp
      <;> ring
  have hc : ContinuousOn (fun x : ℝ => Real.log (1+x)) (Icc 0 1) := by
    intro x hx
    exact ((Real.continuousAt_log (by linarith [hx.1] : 1+x ≠ 0)).comp
      (by fun_prop : ContinuousAt (fun t : ℝ => 1+t) x)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc zero_le_one)]
  norm_num [Real.log_one] <;> ring

theorem sine_square_integral :
    (∫ x in (0:ℝ)..Real.pi, Real.sin x ^ 2) = Real.pi/2 := by
  rw [integral_sin_sq]
  simp

theorem gaussian_finite_positive {a b : ℝ} (hab : a < b) :
    Ch09.HasTaggedIntegral (fun x => Real.exp (-x^2)) a b (∫ x in a..b, Real.exp (-x^2)) ∧
      0 < ∫ x in a..b, Real.exp (-x^2) := by
  have hc : ContinuousOn (fun x : ℝ => Real.exp (-x^2)) (Icc a b) := by fun_prop
  exact ⟨Ch09.continuous_tagged_integral hab hc,
    intervalIntegral.integral_pos hab hc (fun x _ => (Real.exp_pos _).le)
      ⟨a,left_mem_Icc.mpr hab.le,Real.exp_pos _⟩⟩

end Ch10
