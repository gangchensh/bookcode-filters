import Textbook.Ch13.GridGap

namespace Ch13
open MeasureTheory Set Filter
open scoped ENNReal

theorem tagged_rectangle_measure_agreement {a b c d I : ℝ}
    (hab : a < b) (hcd : c < d) (f : ℝ × ℝ → ℝ) (M : ℝ)
    (hf : ∀ z ∈ Icc a b ×ˢ Icc c d, |f z| ≤ M)
    (hI : HasRectangleIntegral f a b c d I) :
    IntegrableOn f (Icc a b ×ˢ Icc c d) (volume.prod volume) ∧
      (∫ z in Icc a b ×ˢ Icc c d, f z ∂volume.prod volume) = I := by
  let R := Ioc a b ×ˢ Ioc c d
  let Q := Icc a b ×ˢ Icc c d
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  let g := R.indicator f
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hsub : R ⊆ Q := by
    intro z hz
    change z.1 ∈ Ioc a b ∧ z.2 ∈ Ioc c d at hz
    exact ⟨Ioc_subset_Icc_self hz.1,Ioc_subset_Icc_self hz.2⟩
  have haeq : R =ᵐ[μ] Q := by
    refine ae_eq_of_subset_of_measure_ge hsub ?_ hR.nullMeasurableSet ?_
    · simp only [μ,Q,R,Measure.prod_prod,Real.volume_Ioc,Real.volume_Icc,le_refl]
    · dsimp [μ,Q]
      rw [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have happrox := grid_gap_of_tagged_integral hab hcd f hI
  have ht (n : ℕ) : 0 < 1/((n:ℝ)+1) := by positivity
  choose P hP using fun n : ℕ => happrox (1/((n:ℝ)+1)) (ht n)
  let l := fun n => gridLower (P n) f
  let u := fun n => gridUpper (P n) f
  have hb (n : ℕ) (z : ℝ × ℝ) : l n z ≤ g z ∧ g z ≤ u n z :=
    grid_bounds_zero_extended (P n) f M hf z
  have hlm (n : ℕ) : Measurable (l n) := gridStep_measurable (P n) _
  have hum (n : ℕ) : Measurable (u n) := gridStep_measurable (P n) _
  have hli (n : ℕ) : Integrable (l n) μ := gridStep_integrable (P n) _
  have hui (n : ℕ) : Integrable (u n) μ := gridStep_integrable (P n) _
  have hg : AEStronglyMeasurable g μ := by
    apply ae_measurable_of_envelopes g l u hlm hum hli hui (ae_of_all _ (fun z n => hb n z))
    intro ε hε
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n,(hP n).2.2.trans hn⟩
  have hgi : Integrable g μ := by
    apply ((hli 0).norm.add (hui 0).norm).mono' hg
    apply ae_of_all
    intro z
    change ‖g z‖ ≤ ‖l 0 z‖ + ‖u 0 z‖
    simp only [Real.norm_eq_abs]
    rw [abs_le]
    have h := hb 0 z
    constructor
    · linarith [neg_abs_le (l 0 z), abs_nonneg (u 0 z),h.1]
    · linarith [le_abs_self (u 0 z), abs_nonneg (l 0 z),h.2]
  have hval : (∫ z, g z ∂μ) = I := by
    by_contra hn
    have hpos : 0 < |(∫ z, g z ∂μ) - I| := abs_pos.mpr (sub_ne_zero.mpr hn)
    obtain ⟨n,hn'⟩ := exists_nat_one_div_lt hpos
    have hlow := integral_mono (hli n) hgi (fun z => (hb n z).1)
    have hupp := integral_mono hgi (hui n) (fun z => (hb n z).2)
    have hlo : I - (1/((n:ℝ)+1))/2 < (∫ z, l n z ∂μ) := (hP n).1
    have hhi : (∫ z, u n z ∂μ) < I + (1/((n:ℝ)+1))/2 := (hP n).2.1
    have ht' := ht n
    rcases le_total (∫ z, g z ∂μ) I with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hn'
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hn'
      linarith
  have hrestrict : μ.restrict R = μ.restrict Q := Measure.restrict_congr_set haeq
  have hiR : IntegrableOn f R μ := (integrable_indicator_iff hR).1 hgi
  have hvalR : (∫ z in R, f z ∂μ) = I := (integral_indicator hR).symm.trans hval
  change Integrable f (μ.restrict Q) ∧ (∫ z, f z ∂μ.restrict Q) = I
  rw [← hrestrict]
  exact ⟨hiR,hvalR⟩

theorem tagged_region_measure_agreement {a b c d I : ℝ}
    (hab : a < b) (hcd : c < d) (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (f : ℝ × ℝ → ℝ) (M : ℝ)
    (hf : ∀ z ∈ D, |f z| ≤ M) (hM : 0 ≤ M)
    (hI : HasRegionIntegral a b c d D f I) :
    IntegrableOn f D (volume.prod volume) ∧
      (∫ z in D, f z ∂volume.prod volume) = I := by
  let Q := Icc a b ×ˢ Icc c d
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  have hbound : ∀ z ∈ Q, |D.indicator f z| ≤ M := by
    intro z _
    by_cases hz : z ∈ D
    · simpa [indicator_of_mem hz] using hf z hz
    · simpa [indicator_of_notMem hz] using hM
  obtain ⟨hi,he⟩ := tagged_rectangle_measure_agreement hab hcd (D.indicator f) M hbound hI.2
  change Integrable (D.indicator f) (μ.restrict Q) at hi
  have hiD := (integrable_indicator_iff hD).1 hi
  change Integrable f ((μ.restrict Q).restrict D) at hiD
  rw [Measure.restrict_restrict_of_subset hI.1] at hiD
  change (∫ z, D.indicator f z ∂μ.restrict Q) = I at he
  rw [integral_indicator hD, Measure.restrict_restrict_of_subset hI.1] at he
  exact ⟨hiD,he⟩

end Ch13
