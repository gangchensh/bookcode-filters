import Textbook.Ch09.MeasureBridge

namespace Ch09

open MeasureTheory Set
open scoped Interval

/-- Once all three tagged integrals exist, the bridge identifies their values. -/
theorem tagged_adjacent_values {f : ℝ → ℝ} {a c b I J K : ℝ}
    (hac : a < c) (hcb : c < b)
    (h : HasTaggedIntegral f a b I) (hl : HasTaggedIntegral f a c J)
    (hr : HasTaggedIntegral f c b K) : I = J + K := by
  obtain ⟨_,hi⟩ := tagged_measure_agreement (hac.trans hcb) h
  obtain ⟨hl',hj⟩ := tagged_measure_agreement hac hl
  obtain ⟨hr',hk⟩ := tagged_measure_agreement hcb hr
  rw [← hi, ← hj, ← hk, intervalIntegral.integral_add_adjacent_intervals hl' hr']

noncomputable def intervalAverage (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, f x) / (b-a)

theorem tagged_average_bounds {f : ℝ → ℝ} {a b I m M : ℝ}
    (hab : a < b) (h : HasTaggedIntegral f a b I)
    (hf : ∀ x ∈ Icc a b, m ≤ f x ∧ f x ≤ M) :
    m ≤ intervalAverage f a b ∧ intervalAverage f a b ≤ M := by
  obtain ⟨hl,hu⟩ := tagged_integral_bounds hab h hf
  rw [intervalAverage, (tagged_measure_agreement hab h).2]
  exact ⟨(le_div_iff₀ (sub_pos.mpr hab)).2 (by linarith [mul_comm m (b-a)]),
    (div_le_iff₀ (sub_pos.mpr hab)).2 (by linarith [mul_comm M (b-a)])⟩

theorem sensor_baseline {f : ℝ → ℝ} {T I b η : ℝ}
    (hT : 0 < T) (h : HasTaggedIntegral f 0 T I) (hb : |b| ≤ η) :
    HasTaggedIntegral (fun t => f t + b) 0 T (I + b*T) ∧
      |(I+b*T)-I| ≤ η*T := by
  constructor
  · have he := tagged_integral_linear h
      (tagged_constant_integral (a := 0) (b := T) b) 1 1
    simpa [sub_zero, mul_comm T b] using he
  · rw [add_sub_cancel_left, abs_mul, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_right hb hT.le

end Ch09
