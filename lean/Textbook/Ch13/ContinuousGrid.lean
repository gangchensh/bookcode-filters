import Textbook.Ch13.GridAgreement

namespace Ch13
open MeasureTheory Set
open scoped BigOperators ENNReal Interval

theorem continuous_rectangle_integrable {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    HasRectangleIntegral f a b c d
      (∫ z in Icc a b ×ˢ Icc c d, f z ∂volume.prod volume) := by
  let R := Ioc a b ×ˢ Ioc c d
  let Q := Icc a b ×ˢ Icc c d
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  let g := R.indicator f
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hsub : R ⊆ Q := fun z hz => ⟨Ioc_subset_Icc_self hz.1,Ioc_subset_Icc_self hz.2⟩
  have haeq : R =ᵐ[μ] Q := by
    refine ae_eq_of_subset_of_measure_ge hsub ?_ hR.nullMeasurableSet ?_
    · simp only [μ,Q,R,Measure.prod_prod,Real.volume_Ioc,Real.volume_Icc,le_refl]
    · dsimp [μ,Q]
      rw [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hiQ : IntegrableOn f Q μ := hf.integrableOn_compact hQ
  have hgi : Integrable g μ := (integrable_indicator_iff hR).2 (hiQ.mono_set hsub)
  have hg : (∫ z, g z ∂μ) = ∫ z in Q, f z ∂μ := by
    rw [show g = R.indicator f from rfl, integral_indicator hR, Measure.restrict_congr_set haeq]
  apply (rectangle_mesh_iff _ _ _ _ _ _).2
  intro ε hε
  let A := (b-a)*(d-c)
  have hA : 0 < A := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hcd)
  let η := (ε/2)/A
  have hη : 0 < η := div_pos (half_pos hε) hA
  have he : η*A = ε/2 := div_mul_cancel₀ _ hA.ne'
  obtain ⟨δ,hδ,huc⟩ := Metric.uniformContinuousOn_iff.mp
    (hQ.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ,hδ,?_⟩
  intro P hP
  let k := fun i j => f (P.tag i j)
  have hbound (z : ℝ × ℝ) : gridStep P (fun i j => k i j - η) z ≤ g z ∧
      g z ≤ gridStep P (fun i j => k i j + η) z := by
    by_cases hz : z ∈ R
    · obtain ⟨i,hi⟩ := tagged_half_open_cover P.x hz.1
      obtain ⟨j,hj⟩ := tagged_half_open_cover P.y hz.2
      have ht : P.tag i j ∈ Q :=
        ⟨P.x.subinterval_subset i (P.tag_x i j),P.y.subinterval_subset j (P.tag_y i j)⟩
      have hx : dist z.1 (P.tag i j).1 ≤ P.x.width i := by
        rw [Real.dist_eq, abs_le, Ch09.TaggedPartition.width]
        exact ⟨by linarith [hi.1,(P.tag_x i j).2],by linarith [hi.2,(P.tag_x i j).1]⟩
      have hy : dist z.2 (P.tag i j).2 ≤ P.y.width j := by
        rw [Real.dist_eq, abs_le, Ch09.TaggedPartition.width]
        exact ⟨by linarith [hj.1,(P.tag_y i j).2],by linarith [hj.2,(P.tag_y i j).1]⟩
      have hdist : dist z (P.tag i j) < δ := by
        change max (dist z.1 (P.tag i j).1) (dist z.2 (P.tag i j).2) < δ
        exact max_lt
          (hx.trans_lt ((Finset.le_sup' (f := P.x.width) (Finset.mem_univ i)).trans_lt
            ((le_max_left _ _).trans_lt hP)))
          (hy.trans_lt ((Finset.le_sup' (f := P.y.width) (Finset.mem_univ j)).trans_lt
            ((le_max_right _ _).trans_lt hP)))
      have h := huc z (hsub hz) _ ht hdist
      rw [Real.dist_eq, abs_lt] at h
      have hc : z ∈ gridCell P i j := ⟨hi,hj⟩
      rw [gridStep_on_cell P _ hc, gridStep_on_cell P _ hc]
      change k i j - η ≤ R.indicator f z ∧ R.indicator f z ≤ k i j + η
      rw [indicator_of_mem hz]
      dsimp [k]
      constructor <;> linarith [h.1,h.2]
    · change _ ≤ R.indicator f z ∧ R.indicator f z ≤ _
      rw [indicator_of_notMem hz, gridStep_off_rectangle P _ hz, gridStep_off_rectangle P _ hz]
      exact ⟨le_rfl,le_rfl⟩
  have hl := integral_mono (gridStep_integrable P (fun i j => k i j - η)) hgi
    (fun z => (hbound z).1)
  have hu := integral_mono hgi (gridStep_integrable P (fun i j => k i j + η))
    (fun z => (hbound z).2)
  rw [hg, gridStep_integral] at hl hu
  have hsum : (∑ i, ∑ j, η * (P.x.width i * P.y.width j)) = ε/2 := by
    rw [show (∑ i, ∑ j, η * (P.x.width i * P.y.width j)) =
      η * (∑ i, ∑ j, P.x.width i * P.y.width j) by simp_rw [Finset.mul_sum],
      grid_total_area P, he]
  simp only [sub_mul, Finset.sum_sub_distrib, hsum] at hl
  simp only [add_mul, Finset.sum_add_distrib, hsum] at hu
  change rectangleSum f P - ε/2 ≤ _ at hl
  change _ ≤ rectangleSum f P + ε/2 at hu
  rw [abs_lt]
  exact ⟨by linarith,by linarith⟩

theorem continuous_rectangle_fubini {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    let I := ∫ z in Icc a b ×ˢ Icc c d, f z ∂volume.prod volume
    HasRectangleIntegral f a b c d I ∧
      I = (∫ x in a..b, ∫ y in c..d, f (x,y)) ∧
      I = (∫ y in c..d, ∫ x in a..b, f (x,y)) := by
  dsimp only
  let R := Ioc a b ×ˢ Ioc c d
  let Q := Icc a b ×ˢ Icc c d
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hsub : R ⊆ Q := fun z hz => ⟨Ioc_subset_Icc_self hz.1,Ioc_subset_Icc_self hz.2⟩
  have haeq : R =ᵐ[μ] Q := by
    refine ae_eq_of_subset_of_measure_ge hsub ?_ hR.nullMeasurableSet ?_
    · simp only [μ,Q,R,Measure.prod_prod,Real.volume_Ioc,Real.volume_Icc,le_refl]
    · dsimp [μ,Q]
      rw [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hiQ : IntegrableOn f Q μ := hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi : Integrable f ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hiQ.mono_set hsub
  refine ⟨continuous_rectangle_integrable hab hcd f hf, ?_, ?_⟩
  all_goals
    change (∫ z in Q, f z ∂μ) = _
    rw [setIntegral_congr_set haeq.symm]
    change (∫ z, f z ∂(volume.prod volume).restrict (Ioc a b ×ˢ Ioc c d)) = _
    rw [← Measure.prod_restrict]
    simp only [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hcd.le]
  · exact integral_prod f hi
  · exact integral_prod_symm f hi

end Ch13
