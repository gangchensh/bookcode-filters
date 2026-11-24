import Textbook.Ch09.DarbouxCriterion

namespace Ch09

open Set MeasureTheory
open scoped Interval

private theorem interval_integrable_between {f : ℝ → ℝ} {l r I x y : ℝ} (hlr : l < r)
    (h : HasTaggedIntegral f l r I) (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) :
    IntervalIntegrable f volume x y := by
  apply (tagged_measure_agreement hlr h).1.mono_set
  rw [uIcc_of_le hlr.le]
  exact uIcc_subset_Icc hx hy

theorem tagged_accumulation_lipschitz {f : ℝ → ℝ} {a b I M : ℝ} (hab : a < b)
    (h : HasTaggedIntegral f a b I) (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |(∫ t in a..y, f t) - (∫ t in a..x, f t)| ≤ M * |y-x| := by
  have ha := left_mem_Icc.mpr hab.le
  rw [intervalIntegral.integral_interval_sub_left
    (interval_integrable_between hab h ha hy) (interval_integrable_between hab h ha hx)]
  have hb : ∀ t ∈ Ι x y, ‖f t‖ ≤ M := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact hM t (uIcc_subset_Icc hx hy (uIoc_subset_uIcc ht))
  simpa only [Real.norm_eq_abs, abs_sub_comm x y] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem tagged_accumulation_derivative {f : ℝ → ℝ} {l r a x I : ℝ}
    (hx : x ∈ Ioo l r) (ha : a ∈ Icc l r)
    (h : HasTaggedIntegral f l r I) (hf : ContinuousAt f x) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x := by
  apply tagged_accumulation_derivative_of_increments hx.1 hx.2 hf
  intro u v hlu huv hvr
  obtain ⟨_,⟨J,hJ⟩⟩ := tagged_adjacent_restrict hlu (huv.trans hvr) h
  obtain ⟨⟨K,hK⟩,_⟩ := tagged_adjacent_restrict huv hvr hJ
  have hlr := hx.1.trans hx.2
  have hu : u ∈ Icc l r := ⟨hlu.le,(huv.trans hvr).le⟩
  have hv : v ∈ Icc l r := ⟨(hlu.trans huv).le,hvr.le⟩
  rw [intervalIntegral.integral_interval_sub_left
    (interval_integrable_between hlr h ha hv) (interval_integrable_between hlr h ha hu),
    (tagged_measure_agreement huv hK).2]
  exact hK

end Ch09
