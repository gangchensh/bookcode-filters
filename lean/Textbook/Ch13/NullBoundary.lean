import Textbook.Ch13.IntegralRules

namespace Ch13
open Set MeasureTheory
open scoped BigOperators ENNReal

private theorem dist_tag_le_mesh {a b c d : ℝ} (P : RectPartition a b c d)
    {z : ℝ × ℝ} {i : Fin (P.x.n+1)} {j : Fin (P.y.n+1)}
    (hz : z ∈ gridCell P i j) : dist z (P.tag i j) ≤ rectangleMesh P := by
  have hx : dist z.1 (P.tag i j).1 ≤ P.x.width i := by
    rw [Real.dist_eq, abs_le, Ch09.TaggedPartition.width]
    exact ⟨by linarith [hz.1.1,(P.tag_x i j).2],by linarith [hz.1.2,(P.tag_x i j).1]⟩
  have hy : dist z.2 (P.tag i j).2 ≤ P.y.width j := by
    rw [Real.dist_eq, abs_le, Ch09.TaggedPartition.width]
    exact ⟨by linarith [hz.2.1,(P.tag_y i j).2],by linarith [hz.2.2,(P.tag_y i j).1]⟩
  change max (dist z.1 (P.tag i j).1) (dist z.2 (P.tag i j).2) ≤ _
  exact max_le
    (hx.trans ((Finset.le_sup' (f := P.x.width) (Finset.mem_univ i)).trans (le_max_left _ _)))
    (hy.trans ((Finset.le_sup' (f := P.y.width) (Finset.mem_univ j)).trans (le_max_right _ _)))

/-- A bounded function supported on a compact set with arbitrarily small open
neighborhoods has tagged Riemann integral zero. -/
theorem rectangle_integral_supported_on_null {a b c d M : ℝ}
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ O : Set (ℝ × ℝ),
      K ⊆ O ∧ IsOpen O ∧ (volume.prod volume) O < ENNReal.ofReal ε)
    (f : ℝ × ℝ → ℝ) (hM : 0 ≤ M)
    (hb : ∀ z ∈ Icc a b ×ˢ Icc c d, |f z| ≤ M)
    (hz : ∀ z ∈ Icc a b ×ˢ Icc c d, z ∉ K → f z = 0) :
    HasRectangleIntegral f a b c d 0 := by
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  apply (rectangle_mesh_iff _ _ _ _ _ _).2
  intro ε hε
  obtain ⟨O,hKO,hO,hμO⟩ := hcover (ε/(M+1)) (div_pos hε (by positivity))
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hO hKO
  refine ⟨δ,hδ,?_⟩
  intro P hP
  let k := fun i j => |f (P.tag i j)|
  have hle (z : ℝ × ℝ) : gridStep P k z ≤ O.indicator (fun _ => M) z := by
    by_cases hzR : z ∈ Ioc a b ×ˢ Ioc c d
    · obtain ⟨i,hi⟩ := tagged_half_open_cover P.x hzR.1
      obtain ⟨j,hj⟩ := tagged_half_open_cover P.y hzR.2
      have hc : z ∈ gridCell P i j := ⟨hi,hj⟩
      have htag : P.tag i j ∈ Icc a b ×ˢ Icc c d :=
        ⟨P.x.subinterval_subset i (P.tag_x i j),P.y.subinterval_subset j (P.tag_y i j)⟩
      rw [gridStep_on_cell P _ hc]
      by_cases ht : P.tag i j ∈ K
      · have hzO : z ∈ O := hthick (Metric.thickening_subset_cthickening _ _
          (Metric.mem_thickening_iff.mpr ⟨P.tag i j,ht,(dist_tag_le_mesh P hc).trans_lt hP⟩))
        rw [indicator_of_mem hzO]
        exact hb _ htag
      · simp only [k,hz _ htag ht,abs_zero]
        exact indicator_nonneg (fun _ _ => hM) _
    · rw [gridStep_off_rectangle P _ hzR]
      exact indicator_nonneg (fun _ _ => hM) _
  have hfin : μ O < ∞ := hμO.trans ENNReal.ofReal_lt_top
  have hdom : Integrable (O.indicator fun _ => M) μ :=
    (integrable_indicator_iff hO.measurableSet).2 (integrableOn_const hfin.ne)
  have hbound := integral_mono (gridStep_integrable P k) hdom hle
  rw [gridStep_integral, integral_indicator_const _ hO.measurableSet, smul_eq_mul] at hbound
  have hsum : |rectangleSum f P| ≤ ∫ z, gridStep P k z ∂μ := by
    rw [gridStep_integral, rectangleSum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_of_nonneg (cell_area_nonneg P i j)]
  have hμ : μ.real O ≤ ε/(M+1) :=
    ((ENNReal.toReal_le_toReal hfin.ne ENNReal.ofReal_ne_top).mpr hμO.le).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have he : ε/(M+1)*(M+1) = ε := div_mul_cancel₀ _ (by positivity)
  have hprod := mul_le_mul_of_nonneg_right hμ hM
  have hpos : 0 < ε/(M+1) := div_pos hε (by positivity)
  have hsmall : μ.real O * M < ε := by nlinarith
  rw [sub_zero]
  rw [gridStep_integral] at hsum
  exact hsum.trans_lt (hbound.trans_lt hsmall)

theorem rectangle_integral_congr_off_null {a b c d I M : ℝ}
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ O : Set (ℝ × ℝ),
      K ⊆ O ∧ IsOpen O ∧ (volume.prod volume) O < ENNReal.ofReal ε)
    {f g : ℝ × ℝ → ℝ} (hf : HasRectangleIntegral f a b c d I)
    (hM : 0 ≤ M) (hb : ∀ z ∈ Icc a b ×ˢ Icc c d, |g z - f z| ≤ M)
    (he : ∀ z ∈ Icc a b ×ˢ Icc c d, z ∉ K → g z = f z) :
    HasRectangleIntegral g a b c d I := by
  have hzero := rectangle_integral_supported_on_null K hK hcover (fun z => g z - f z)
    hM hb (fun z hQ hz => sub_eq_zero.mpr (he z hQ hz))
  have hsum := rectangle_integral_linear hf hzero 1 1
  have hfg : (fun z => 1*f z + 1*(g z - f z)) = g := by
    funext z
    ring
  rwa [hfg,one_mul, mul_zero, add_zero] at hsum

/-- The small neighborhood controls the bad cells; uniform continuity controls the others. -/
theorem rectangle_integral_continuous_off_null {a b c d M : ℝ}
    (hab : a < b) (hcd : c < d) (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ O : Set (ℝ × ℝ),
      K ⊆ O ∧ IsOpen O ∧ (volume.prod volume) O < ENNReal.ofReal ε)
    (f : ℝ × ℝ → ℝ) (hM : 0 ≤ M)
    (hb : ∀ z ∈ Icc a b ×ˢ Icc c d, |f z| ≤ M)
    (hf : ContinuousOn f ((Icc a b ×ˢ Icc c d) \ K)) :
    HasRectangleIntegral f a b c d
      (∫ z in Ioc a b ×ˢ Ioc c d, f z ∂volume.prod volume) := by
  let μ : Measure (ℝ × ℝ) := volume.prod volume
  let Q := Icc a b ×ˢ Icc c d
  let R := Ioc a b ×ˢ Ioc c d
  let g := R.indicator f
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hRQ : R ⊆ Q := fun z hz => ⟨Ioc_subset_Icc_self hz.1,Ioc_subset_Icc_self hz.2⟩
  have hRfin : μ R ≠ ∞ := by
    change (volume.prod volume) (Ioc a b ×ˢ Ioc c d) ≠ ∞
    rw [Measure.prod_prod,Real.volume_Ioc,Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hμK : μ K = 0 := by
    have hfin : μ K ≠ ∞ := by
      obtain ⟨O,hKO,_,hO⟩ := hcover 1 zero_lt_one
      exact ((measure_mono hKO).trans_lt (hO.trans ENNReal.ofReal_lt_top)).ne
    by_contra hn
    have hp : 0 < (μ K).toReal := ENNReal.toReal_pos hn hfin
    obtain ⟨O,hKO,_,hO⟩ := hcover (μ K).toReal hp
    rw [ENNReal.ofReal_toReal hfin] at hO
    exact (not_lt_of_ge (measure_mono hKO)) hO
  have hRae : R \ K =ᵐ[μ] R := by
    have hn : ∀ᵐ z ∂μ, z ∉ K := by
      rw [ae_iff]
      simpa using hμK
    filter_upwards [hn] with z hz
    simp [hz]
  have hm : AEStronglyMeasurable f (μ.restrict R) := by
    rw [← Measure.restrict_congr_set hRae]
    exact (hf.mono (fun z hz => ⟨hRQ hz.1,hz.2⟩)).aestronglyMeasurable
      (hR.diff hK.isClosed.measurableSet)
  have hgi : Integrable g μ := by
    apply (integrable_indicator_iff hR).2
    refine ⟨hm, ?_⟩
    exact HasFiniteIntegral.restrict_of_bounded (C := M) hRfin.lt_top
      ((ae_restrict_mem hR).mono (fun z hz => by simpa [Real.norm_eq_abs] using hb z (hRQ hz)))
  apply (rectangle_mesh_iff _ _ _ _ _ _).2
  intro ε hε
  let A := (b-a)*(d-c)
  let η := (ε/2)/A
  have hA : 0 < A := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hcd)
  have hη : 0 < η := div_pos (half_pos hε) hA
  have hηA : η*A = ε/2 := div_mul_cancel₀ _ hA.ne'
  have hpos : 0 < ε/(4*(M+1)) := div_pos hε (by positivity)
  obtain ⟨O,hKO,hO,hμO⟩ := hcover _ hpos
  obtain ⟨r,hr,hrO⟩ := hK.exists_cthickening_subset_open hO hKO
  let U := Metric.thickening (r/2) K
  have hU : IsOpen U := Metric.isOpen_thickening
  have hKU : K ⊆ U := Metric.self_subset_thickening (half_pos hr) _
  have hcompact : IsCompact (Q \ U) := (isCompact_Icc.prod isCompact_Icc).diff hU
  have hcont : ContinuousOn f (Q \ U) :=
    hf.mono (fun _ hz => ⟨hz.1,fun hk => hz.2 (hKU hk)⟩)
  obtain ⟨δ,hδ,huc⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hcont) η hη
  refine ⟨min δ (r/2),lt_min hδ (half_pos hr),?_⟩
  intro P hP
  let s := gridStep P (fun i j => f (P.tag i j))
  let e := fun z => s z - g z
  let w := fun z => R.indicator (fun _ => η) z + O.indicator (fun _ => 2*M) z
  have hwR (z) : 0 ≤ R.indicator (fun _ => η) z := indicator_nonneg (fun _ _ => hη.le) _
  have hwO (z) : 0 ≤ O.indicator (fun _ => 2*M) z :=
    indicator_nonneg (fun _ _ => by positivity) _
  have hreach {z t : ℝ × ℝ} (ht : t ∈ U) (hz : dist z t < r/2) : z ∈ O := by
    obtain ⟨k,hk,hkt⟩ := Metric.mem_thickening_iff.mp ht
    apply hrO (Metric.thickening_subset_cthickening _ _ ?_)
    exact Metric.mem_thickening_iff.mpr ⟨k,hk,(dist_triangle z t k).trans_lt (by linarith)⟩
  have hbnd (z) : |e z| ≤ w z := by
    by_cases hz : z ∈ R
    · obtain ⟨i,hi⟩ := tagged_half_open_cover P.x hz.1
      obtain ⟨j,hj⟩ := tagged_half_open_cover P.y hz.2
      have hcell : z ∈ gridCell P i j := ⟨hi,hj⟩
      have ht : P.tag i j ∈ Q :=
        ⟨P.x.subinterval_subset i (P.tag_x i j),P.y.subinterval_subset j (P.tag_y i j)⟩
      have hd := (dist_tag_le_mesh P hcell).trans_lt hP
      dsimp [e,s,g,w]
      rw [gridStep_on_cell P _ hcell]
      simp only [indicator_of_mem hz]
      by_cases hbad : z ∈ U ∨ P.tag i j ∈ U
      · have hzO : z ∈ O := hbad.elim
          (fun h => hreach h (by simpa using half_pos hr))
          (fun h => hreach h (hd.trans_le (min_le_right _ _)))
        rw [indicator_of_mem hzO]
        have htriangle : |f (P.tag i j) - f z| ≤ |f (P.tag i j)| + |f z| := by
          simpa using abs_sub_le (f (P.tag i j)) 0 (f z)
        have h := htriangle.trans (add_le_add (hb _ ht) (hb z (hRQ hz)))
        linarith
      · push Not at hbad
        have h := huc z ⟨hRQ hz,hbad.1⟩ _ ⟨ht,hbad.2⟩ (hd.trans_le (min_le_left _ _))
        rw [Real.dist_eq, abs_sub_comm] at h
        linarith [hwO z]
    · dsimp [e,s,g,w]
      rw [gridStep_off_rectangle P _ hz,indicator_of_notMem hz,sub_zero,abs_zero]
      exact add_nonneg (hwR z) (hwO z)
  have hOfin : μ O < ∞ := hμO.trans ENNReal.ofReal_lt_top
  have hiR : Integrable (R.indicator (fun _ => η)) μ :=
    (integrable_indicator_iff hR).2 (integrableOn_const hRfin)
  have hiO : Integrable (O.indicator (fun _ => 2*M)) μ :=
    (integrable_indicator_iff hO.measurableSet).2 (integrableOn_const hOfin.ne)
  have hei : Integrable e μ := (gridStep_integrable P _).sub hgi
  have hbound := integral_mono hei.norm (hiR.add hiO)
    (fun z => by
      change ‖e z‖ ≤ w z
      rw [Real.norm_eq_abs]
      exact hbnd z)
  have hn := norm_integral_le_integral_norm (μ := μ) e
  have heq : (∫ z, e z ∂μ) = rectangleSum f P - ∫ z in R, f z ∂μ := by
    change (∫ z, s z - R.indicator f z ∂μ) = _
    rw [integral_sub (gridStep_integrable P _) hgi,gridStep_integral,integral_indicator hR]
    rfl
  have harea : μ.real R = A := by
    change ((volume.prod volume) (Ioc a b ×ˢ Ioc c d)).toReal = A
    rw [Measure.prod_prod,Real.volume_Ioc,Real.volume_Ioc,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),ENNReal.toReal_ofReal (sub_nonneg.mpr hcd.le)]
  have ho : μ.real O ≤ ε/(4*(M+1)) :=
    ((ENNReal.toReal_le_toReal hOfin.ne ENNReal.ofReal_ne_top).mpr hμO.le).trans_eq
      (ENNReal.toReal_ofReal hpos.le)
  have heps : ε/(4*(M+1))*(4*(M+1)) = ε := div_mul_cancel₀ _ (by positivity)
  dsimp [w] at hbound
  rw [integral_add hiR hiO,integral_indicator_const _ hR,
    integral_indicator_const _ hO.measurableSet,smul_eq_mul,smul_eq_mul,harea,mul_comm A η,hηA]
      at hbound
  rw [heq,Real.norm_eq_abs] at hn
  have hmul := mul_le_mul_of_nonneg_right ho (show 0 ≤ 2*M by positivity)
  exact (hn.trans hbound).trans_lt (by nlinarith)

/-- The geometric covering hypothesis, with total area counted with multiplicity. -/
def SmallOpenRectangleCovers (K : Set (ℝ × ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (l r : Fin n → ℝ × ℝ),
    (∀ i, (l i).1 ≤ (r i).1 ∧ (l i).2 ≤ (r i).2) ∧
    K ⊆ (⋃ i, Ioo (l i).1 (r i).1 ×ˢ Ioo (l i).2 (r i).2) ∧
    (∑ i, ((r i).1 - (l i).1)*((r i).2 - (l i).2)) < ε

theorem SmallOpenRectangleCovers.open_neighborhoods {K : Set (ℝ × ℝ)}
    (hK : SmallOpenRectangleCovers K) :
    ∀ ε : ℝ, 0 < ε → ∃ O : Set (ℝ × ℝ),
      K ⊆ O ∧ IsOpen O ∧ (volume.prod volume) O < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨n,l,r,hle,hsub,hsum⟩ := hK ε hε
  let V (i : Fin n) := Ioo (l i).1 (r i).1 ×ˢ Ioo (l i).2 (r i).2
  let area (i : Fin n) := ((r i).1 - (l i).1)*((r i).2 - (l i).2)
  have harea (i : Fin n) : 0 ≤ area i :=
    mul_nonneg (sub_nonneg.mpr (hle i).1) (sub_nonneg.mpr (hle i).2)
  refine ⟨⋃ i, V i,hsub,isOpen_iUnion (fun _ => isOpen_Ioo.prod isOpen_Ioo),?_⟩
  calc
    _ ≤ ∑' i, (volume.prod volume) (V i) := measure_iUnion_le V
    _ = ENNReal.ofReal (∑ i, area i) := by
      rw [tsum_fintype,ENNReal.ofReal_sum_of_nonneg (fun i _ => harea i)]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [V,area]
      rw [Measure.prod_prod,Real.volume_Ioo,Real.volume_Ioo,
        ENNReal.ofReal_mul (sub_nonneg.mpr (hle i).1)]
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff hε).2 hsum

theorem rectangle_integrable_of_small_boundary {a b c d M : ℝ}
    (hab : a < b) (hcd : c < d) (K : Set (ℝ × ℝ))
    (hclosed : IsClosed K) (hK : K ⊆ Icc a b ×ˢ Icc c d)
    (hcover : SmallOpenRectangleCovers K)
    (f : ℝ × ℝ → ℝ) (hM : 0 ≤ M)
    (hb : ∀ z ∈ Icc a b ×ˢ Icc c d, |f z| ≤ M)
    (hf : ContinuousOn f ((Icc a b ×ˢ Icc c d) \ K)) :
    ∃ I, HasRectangleIntegral f a b c d I := by
  have hc := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hK
  exact ⟨_,rectangle_integral_continuous_off_null hab hcd K hc
    hcover.open_neighborhoods f hM hb hf⟩

theorem region_integral_union_null_overlap {a b c d I J M : ℝ}
    {D E K : Set (ℝ × ℝ)} (hK : IsCompact K) (hDE : D ∩ E ⊆ K)
    (hcover : ∀ ε : ℝ, 0 < ε → ∃ O : Set (ℝ × ℝ),
      K ⊆ O ∧ IsOpen O ∧ (volume.prod volume) O < ENNReal.ofReal ε)
    {f : ℝ × ℝ → ℝ} (hf : HasRegionIntegral a b c d D f I)
    (hg : HasRegionIntegral a b c d E f J)
    (hM : 0 ≤ M) (hb : ∀ z ∈ D ∩ E, |f z| ≤ M) :
    HasRegionIntegral a b c d (D ∪ E) f (I+J) := by
  have hsum : HasRectangleIntegral (fun z => D.indicator f z + E.indicator f z)
      a b c d (I+J) := by
    simpa only [one_mul] using rectangle_integral_linear hf.2 hg.2 1 1
  have hdiff (z) : (D ∪ E).indicator f z - (D.indicator f z + E.indicator f z) =
      -(D ∩ E).indicator f z := by
    by_cases hd : z ∈ D <;> by_cases he : z ∈ E <;> simp [hd,he]
  refine ⟨union_subset hf.1 hg.1, ?_⟩
  apply rectangle_integral_congr_off_null K hK hcover hsum hM
  · intro z _
    rw [hdiff,abs_neg]
    by_cases hz : z ∈ D ∩ E
    · simpa [indicator_of_mem hz] using hb z hz
    · simpa [indicator_of_notMem hz] using hM
  · intro z _ hz
    apply sub_eq_zero.mp
    rw [hdiff,indicator_of_notMem (fun h => hz (hDE h)),neg_zero]

end Ch13
