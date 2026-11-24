import Textbook.Ch09.MeasureBridge

namespace Ch09

open MeasureTheory Set
open scoped Interval

theorem tagged_integral_positive {f : ℝ → ℝ} {a b I : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hp : ∃ c ∈ Icc a b, 0 < f c) (h : HasTaggedIntegral f a b I) : 0 < I := by
  rw [← (tagged_measure_agreement hab h).2]
  exact intervalIntegral.integral_pos hab hf (fun x hx => hn x (Ioc_subset_Icc_self hx)) hp

theorem tagged_integral_zero_iff {f : ℝ → ℝ} {a b I : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (h : HasTaggedIntegral f a b I) : I = 0 ↔ ∀ x ∈ Icc a b, f x = 0 := by
  constructor
  · intro hI x hx
    by_contra hne
    have hp : 0 < I := tagged_integral_positive hab hf hn
      ⟨x,hx,lt_of_le_of_ne (hn x hx) (Ne.symm hne)⟩ h
    linarith
  · intro hz
    rw [← (tagged_measure_agreement hab h).2]
    rw [intervalIntegral.integral_congr (g := fun _ => 0) (by
      rwa [uIcc_of_le hab.le])]
    simp

theorem weighted_integral_mean {f w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hn : ∀ x ∈ Icc a b, 0 ≤ w x) (hW : 0 < ∫ x in a..b, w x) :
    ∃ c ∈ Icc a b, (∫ x in a..b, f x*w x) = f c * (∫ x in a..b, w x) := by
  let W := ∫ x in a..b, w x
  let J := ∫ x in a..b, f x*w x
  obtain ⟨l,hl,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a,left_mem_Icc.mpr hab.le⟩ hf
  obtain ⟨r,hr,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a,left_mem_Icc.mpr hab.le⟩ hf
  have hi : IntervalIntegrable (fun x => f x * w x) volume a b :=
    (hf.mul hw).intervalIntegrable_of_Icc hab.le
  have hwi : IntervalIntegrable w volume a b := hw.intervalIntegrable_of_Icc hab.le
  have hlow := intervalIntegral.integral_mono_on hab.le (hwi.const_mul (f l)) hi
    (fun x hx => mul_le_mul_of_nonneg_right (hmin hx) (hn x hx))
  have hupp := intervalIntegral.integral_mono_on hab.le hi (hwi.const_mul (f r))
    (fun x hx => mul_le_mul_of_nonneg_right (hmax hx) (hn x hx))
  rw [intervalIntegral.integral_const_mul] at hlow hupp
  have hmem : J/W ∈ Icc (f l) (f r) := ⟨(le_div_iff₀ hW).2 hlow, (div_le_iff₀ hW).2 hupp⟩
  obtain ⟨c,hc,he⟩ := isPreconnected_Icc.intermediate_value hl hr hf hmem
  exact ⟨c,hc,((eq_div_iff hW.ne').mp he).symm⟩

theorem continuous_integral_mean {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, (∫ x in a..b, f x) = f c * (b-a) := by
  have h := weighted_integral_mean hab hf
    (w := fun _ => 1) continuous_const.continuousOn (fun _ _ => zero_le_one)
    (by simpa [intervalIntegral.integral_const,smul_eq_mul] using sub_pos.mpr hab)
  simpa [intervalIntegral.integral_const,smul_eq_mul] using h

end Ch09
