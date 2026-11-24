import Textbook.Ch13.NullBoundary
import Textbook.Ch13.Examples
import Textbook.Ch13.Slices

namespace Ch13
open Set MeasureTheory Filter
open scoped ENNReal Interval Topology

def verticalRegion (a b : ℝ) (l u : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc a b ∧ z.2 ∈ Icc (l z.1) (u z.1)}

private theorem graph_null {a b : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    (volume.prod volume) ((fun x : ℝ => (x,g x)) '' Icc a b) = 0 := by
  let G := (fun x : ℝ => (x,g x)) '' Icc a b
  have hc : IsCompact G := isCompact_Icc.image (continuous_id.prodMk hg)
  apply (Measure.measure_prod_null hc.isClosed.measurableSet).2
  apply ae_of_all
  intro x
  apply measure_mono_null _ (measure_singleton (g x))
  rintro y ⟨t,_,ht⟩
  have h : t = x := congrArg Prod.fst ht
  subst t
  exact congrArg Prod.snd ht |>.symm

/-- A continuous function on a vertically simple region has a tagged integral
after zero extension to an enclosing rectangle. -/
theorem vertical_region_integrable {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (l u : ℝ → ℝ) (hl : ContinuousOn l (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hbox : verticalRegion a b l u ⊆ Icc a b ×ˢ Icc c d)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f (verticalRegion a b l u)) :
    IsCompact (verticalRegion a b l u) ∧
      ∃ I, HasRegionIntegral a b c d (verticalRegion a b l u) f I := by
  let D := verticalRegion a b l u
  obtain ⟨L,hL⟩ := ContinuousMap.exists_restrict_eq isClosed_Icc
    (⟨_,continuousOn_iff_continuous_domRestrict.mp hl⟩ : C(Icc a b, ℝ))
  obtain ⟨U,hU⟩ := ContinuousMap.exists_restrict_eq isClosed_Icc
    (⟨_,continuousOn_iff_continuous_domRestrict.mp hu⟩ : C(Icc a b, ℝ))
  have hL' (x : ℝ) (hx : x ∈ Icc a b) : L x = l x :=
    congrArg (fun g : C(Icc a b, ℝ) => g ⟨x,hx⟩) hL
  have hU' (x : ℝ) (hx : x ∈ Icc a b) : U x = u x :=
    congrArg (fun g : C(Icc a b, ℝ) => g ⟨x,hx⟩) hU
  have hD (z : ℝ × ℝ) : z ∈ D ↔ z.1 ∈ Icc a b ∧ L z.1 ≤ z.2 ∧ z.2 ≤ U z.1 := by
    constructor <;> rintro ⟨hx,hy⟩ <;> exact ⟨hx,by simpa [hL' _ hx,hU' _ hx] using hy⟩
  have hDc : IsClosed D := by
    have he : D = Prod.fst ⁻¹' Icc a b ∩ ({z | L z.1 ≤ z.2} ∩ {z | z.2 ≤ U z.1}) :=
      Set.ext hD
    rw [he]
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_le (L.continuous.comp continuous_fst) continuous_snd).inter
        (isClosed_le continuous_snd (U.continuous.comp continuous_fst)))
  let G (g : ℝ → ℝ) := (fun x : ℝ => (x,g x)) '' Icc a b
  let W : Set (ℝ × ℝ) := ({a,b} : Set ℝ) ×ˢ Icc c d
  let K := (G L ∪ G U) ∪ W
  have hGc (g : C(ℝ,ℝ)) : IsCompact (G g) :=
    isCompact_Icc.image (continuous_id.prodMk g.continuous)
  have hKc : IsCompact K := ((hGc L).union (hGc U)).union
    ((Set.finite_singleton b |>.insert a).isCompact.prod isCompact_Icc)
  have hW : (volume.prod volume) W = 0 := by
    change (volume.prod volume) (({a,b} : Set ℝ) ×ˢ Icc c d) = 0
    rw [Measure.prod_prod]
    rw [(Set.finite_singleton b |>.insert a).measure_zero volume,zero_mul]
  have hK : (volume.prod volume) K = 0 := by
    apply measure_union_null _ hW
    exact measure_union_null (graph_null L.continuous) (graph_null U.continuous)
  have hcover : ∀ ε : ℝ, 0 < ε → ∃ O : Set (ℝ × ℝ),
      K ⊆ O ∧ IsOpen O ∧ (volume.prod volume) O < ENNReal.ofReal ε := by
    intro ε hε
    rw [← Measure.volume_eq_prod] at hK ⊢
    exact K.exists_isOpen_lt_of_lt _ (hK ▸ ENNReal.ofReal_pos.mpr hε)
  have hDcompact : IsCompact D :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hDc hbox
  obtain ⟨M,hM⟩ := hDcompact.bddAbove_image hf.abs
  have hb (z : ℝ × ℝ) : |D.indicator f z| ≤ max 0 M := by
    by_cases hz : z ∈ D
    · rw [indicator_of_mem hz]
      exact (hM ⟨z,hz,rfl⟩).trans (le_max_right _ _)
    · simp [hz]
  have hcont : ContinuousOn (D.indicator f) ((Icc a b ×ˢ Icc c d) \ K) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    by_cases hd : z ∈ D
    · obtain ⟨hx,hlo,hhi⟩ := (hD z).1 hd
      have hx' : z.1 ∈ Ioo a b := by
        refine ⟨lt_of_le_of_ne hx.1 ?_,lt_of_le_of_ne hx.2 ?_⟩
        · intro h
          exact hz.2 (Or.inr ⟨Or.inl h.symm,hz.1.2⟩)
        · intro h
          exact hz.2 (Or.inr ⟨Or.inr h,hz.1.2⟩)
      have hl' : L z.1 < z.2 := hlo.lt_of_ne (fun h =>
        hz.2 (Or.inl (Or.inl ⟨z.1,hx,Prod.ext rfl h⟩)))
      have hu' : z.2 < U z.1 := hhi.lt_of_ne (fun h =>
        hz.2 (Or.inl (Or.inr ⟨z.1,hx,Prod.ext rfl h.symm⟩)))
      let V : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioo a b ∩ ({w | L w.1 < w.2} ∩ {w | w.2 < U w.1})
      have ho : IsOpen V := (isOpen_Ioo.preimage continuous_fst).inter
        ((isOpen_lt (L.continuous.comp continuous_fst) continuous_snd).inter
          (isOpen_lt continuous_snd (U.continuous.comp continuous_fst)))
      have hVD : V ⊆ D := fun w hw => (hD w).2
        ⟨Ioo_subset_Icc_self hw.1,hw.2.1.le,hw.2.2.le⟩
      have hn : D ∈ 𝓝 z := mem_of_superset (ho.mem_nhds ⟨hx',hl',hu'⟩) hVD
      exact ((hf z hd).continuousAt hn).congr
        (mem_of_superset hn (fun _ hw => (indicator_of_mem hw _).symm))
    · exact continuousAt_const.congr
        (mem_of_superset (hDc.isOpen_compl.mem_nhds hd)
          (fun _ hw => (indicator_of_notMem hw _).symm))
  exact ⟨hDcompact,_,hbox,rectangle_integral_continuous_off_null hab hcd K hKc hcover
    (D.indicator f) (le_max_left _ _) (fun z _ => hb z) hcont⟩

theorem vertical_region_slicing {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (l u : ℝ → ℝ) (hl : ContinuousOn l (Icc a b)) (hu : ContinuousOn u (Icc a b))
    (hlu : ∀ x ∈ Icc a b, l x ≤ u x)
    (hbox : verticalRegion a b l u ⊆ Icc a b ×ˢ Icc c d)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f (verticalRegion a b l u)) :
    (∀ x ∈ Icc a b, IntervalIntegrable (fun y => f (x,y)) volume (l x) (u x)) ∧
      HasRegionIntegral a b c d (verticalRegion a b l u) f
        (∫ x in a..b, ∫ y in l x..u x, f (x,y)) := by
  let D := verticalRegion a b l u
  obtain ⟨hc,I,hI⟩ := vertical_region_integrable hab hcd l u hl hu hbox f hf
  refine ⟨?_,?_⟩
  · intro x hx
    have h : ContinuousOn (fun y => f (x,y)) (Icc (l x) (u x)) :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => ⟨hx,hy⟩)
    exact h.intervalIntegrable_of_Icc (hlu x hx)
  obtain ⟨M,hM⟩ := hc.bddAbove_image hf.abs
  have hbound (z) (hz : z ∈ D) : |f z| ≤ max 0 M :=
    (hM ⟨z,hz,rfl⟩).trans (le_max_right _ _)
  obtain ⟨hi,he⟩ := tagged_region_measure_agreement hab hcd D
    hc.isClosed.measurableSet f (max 0 M) hbound (le_max_left _ _) hI
  have hfub := (region_fubini D hc.isClosed.measurableSet f hi).1
  have hslice (x : ℝ) :
      (∫ y : ℝ, D.indicator f (x,y)) =
        (Icc a b).indicator (fun t => ∫ y in l t..u t, f (t,y)) x := by
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx,intervalIntegral.integral_of_le (hlu x hx),
        ← integral_Icc_eq_integral_Ioc,← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      apply ae_of_all
      intro y
      change D.indicator f (x,y) = (Icc (l x) (u x)).indicator (fun t => f (x,t)) y
      by_cases hy : y ∈ Icc (l x) (u x)
      · rw [indicator_of_mem (show (x,y) ∈ D from ⟨hx,hy⟩),indicator_of_mem hy]
      · rw [indicator_of_notMem (show (x,y) ∉ D from fun h => hy h.2),
          indicator_of_notMem hy]
    · rw [indicator_of_notMem hx]
      have hz (y : ℝ) : D.indicator f (x,y) = 0 :=
        indicator_of_notMem (fun h => hx h.1) _
      simp [hz]
  rw [show (∫ x in a..b, ∫ y in l x..u x, f (x,y)) = I by
    rw [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    simp_rw [← hslice]
    exact hfub.symm.trans he]
  exact hI

private theorem tagged_slice_on_enclosure {c d l u : ℝ} (hcd : c < d)
    (hlu : l ≤ u) (hbox : Icc l u ⊆ Icc c d)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc l u)) :
    Ch09.HasTaggedIntegral ((Icc l u).indicator f) c d (∫ y in l..u, f y) := by
  let D := verticalRegion 0 1 (fun _ => l) (fun _ => u)
  have hD : D ⊆ Icc 0 1 ×ˢ Icc c d := fun _ hz => ⟨hz.1,hbox hz.2⟩
  have hcont : ContinuousOn (fun z : ℝ × ℝ => f z.2) D :=
    hf.comp continuous_snd.continuousOn (fun _ hz => hz.2)
  have h := (vertical_region_slicing zero_lt_one hcd _ _ continuous_const.continuousOn
    continuous_const.continuousOn (fun _ _ => hlu) hD _ hcont).2.2
  simp only [intervalIntegral.integral_const,smul_eq_mul,sub_zero,one_mul] at h
  apply (Ch09.tagged_integral_iff _ _ _ _).2
  intro ε hε
  obtain ⟨δ,hδ,hfine⟩ := (rectangle_mesh_iff _ _ _ _ _ _).1 h ε hε
  obtain ⟨X,hX⟩ := Ch09.arbitrarily_fine zero_lt_one δ hδ
  refine ⟨δ,hδ,fun Y hY => ?_⟩
  let P : RectPartition 0 1 c d := ⟨X,Y,fun i j => (X.tag i,Y.tag j),
    fun i _ => X.tag_mem i,fun _ j => Y.tag_mem j⟩
  have htag (i : Fin (X.n+1)) (j : Fin (Y.n+1)) :
      D.indicator (fun z => f z.2) (X.tag i,Y.tag j) =
        (Icc l u).indicator f (Y.tag j) := by
    have hx := X.subinterval_subset i (X.tag_mem i)
    by_cases hy : Y.tag j ∈ Icc l u
    · rw [indicator_of_mem (show (X.tag i,Y.tag j) ∈ D from ⟨hx,hy⟩),indicator_of_mem hy]
    · rw [indicator_of_notMem (show (X.tag i,Y.tag j) ∉ D from fun hz => hy hz.2),
        indicator_of_notMem hy]
  have hsum : rectangleSum (D.indicator fun z => f z.2) P =
      Y.riemannSum ((Icc l u).indicator f) := by
    unfold rectangleSum Ch09.TaggedPartition.riemannSum
    change (∑ i, ∑ j, D.indicator (fun z => f z.2) (X.tag i,Y.tag j) *
      (X.width i * Y.width j)) = _
    simp_rw [htag,show ∀ q x y : ℝ, q*(x*y) = x*(q*y) by intros; ring,← Finset.mul_sum]
    rw [← Finset.sum_mul]
    unfold Ch09.TaggedPartition.width
    rw [Ch09.sum_endpoint_differences,X.first,X.last,sub_zero,one_mul]
  have hP := hfine P (max_lt hX hY)
  change |rectangleSum (D.indicator fun z => f z.2) P - _| < ε at hP
  rwa [hsum] at hP

/-- The tagged integral of every zero-extended vertical slice, including a singleton slice. -/
theorem vertical_region_tagged_slice {a b c d x : ℝ} (hcd : c < d)
    (l u : ℝ → ℝ) (hx : x ∈ Icc a b) (hlu : l x ≤ u x)
    (hbox : verticalRegion a b l u ⊆ Icc a b ×ˢ Icc c d)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f (verticalRegion a b l u)) :
    Ch09.HasTaggedIntegral (fun y => (verticalRegion a b l u).indicator f (x,y)) c d
      (∫ y in l x..u x, f (x,y)) := by
  have he : (fun y => (verticalRegion a b l u).indicator f (x,y)) =
      (Icc (l x) (u x)).indicator (fun y => f (x,y)) := by
    funext y
    by_cases hy : y ∈ Icc (l x) (u x)
    · rw [indicator_of_mem (show (x,y) ∈ verticalRegion a b l u from ⟨hx,hy⟩),
        indicator_of_mem hy]
    · rw [indicator_of_notMem (show (x,y) ∉ verticalRegion a b l u from fun hz => hy hz.2),
        indicator_of_notMem hy]
  rw [he]
  exact tagged_slice_on_enclosure hcd hlu
    (fun y hy => (hbox (show (x,y) ∈ verticalRegion a b l u from ⟨hx,hy⟩)).2) _
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => ⟨hx,hy⟩))

private theorem region_integral_swap {a b c d I : ℝ}
    {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (h : HasRegionIntegral c d a b (Prod.swap ⁻¹' D) (fun z => f z.swap) I) :
    HasRegionIntegral a b c d D f I := by
  refine ⟨fun z hz => ?_,?_⟩
  · exact ⟨(h.1 (show z.swap ∈ Prod.swap ⁻¹' D from hz)).2,
      (h.1 (show z.swap ∈ Prod.swap ⁻¹' D from hz)).1⟩
  apply (rectangle_mesh_iff _ a b c d I).2
  intro ε hε
  obtain ⟨δ,hδ,h₁⟩ := (rectangle_mesh_iff _ c d a b I).1 h.2 ε hε
  refine ⟨δ,hδ,fun P hP => ?_⟩
  have hs (z : ℝ × ℝ) : (Prod.swap ⁻¹' D).indicator (fun w => f w.swap) z.swap =
      D.indicator f z := by
    by_cases hz : z ∈ D <;> simp [hz]
  have hsum : rectangleSum (D.indicator f) P =
      rectangleSum ((Prod.swap ⁻¹' D).indicator (fun z => f z.swap)) P.swap := by
    unfold rectangleSum RectPartition.swap
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    change _ = (Prod.swap ⁻¹' D).indicator (fun z => f z.swap) (P.tag i j).swap *
      (P.y.width j * P.x.width i)
    rw [hs,mul_comm (P.y.width j)]
  rw [hsum]
  exact h₁ P.swap (by simpa [rectangleMesh, RectPartition.swap, max_comm] using hP)

private theorem region_value_unique {a b c d I J : ℝ} (hab : a < b) (hcd : c < d)
    {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hI : HasRegionIntegral a b c d D f I) (hJ : HasRegionIntegral a b c d D f J) :
    I = J :=
  le_antisymm (rectangle_integral_mono hab hcd hI.2 hJ.2 (fun _ _ => le_rfl))
    (rectangle_integral_mono hab hcd hJ.2 hI.2 (fun _ _ => le_rfl))

def unitTriangle : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

theorem triangle_region_both_orders (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f unitTriangle) :
    HasRegionIntegral 0 1 0 1 unitTriangle f
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1-x), f (x,y)) ∧
    HasRegionIntegral 0 1 0 1 unitTriangle f
      (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..(1-y), f (x,y)) := by
  have hD : unitTriangle = verticalRegion 0 1 (fun _ => 0) (fun x => 1-x) :=
    Set.ext fun z => by
      simpa [unitTriangle,verticalRegion,mem_Icc,and_assoc] using triangle_slice_bounds z.1 z.2
  have hbox : unitTriangle ⊆ Icc 0 1 ×ˢ Icc 0 1 := by
    rintro z ⟨hx,hy,hxy⟩
    exact ⟨⟨hx,by linarith⟩,⟨hy,by linarith⟩⟩
  have hv (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g unitTriangle) :
      HasRegionIntegral 0 1 0 1 unitTriangle g
        (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1-x), g (x,y)) := by
    rw [hD] at hg hbox ⊢
    exact (vertical_region_slicing zero_lt_one zero_lt_one _ _
      continuous_const.continuousOn (by fun_prop) (fun _ hx => sub_nonneg.mpr hx.2) hbox g hg).2
  have hswap : Prod.swap ⁻¹' unitTriangle = unitTriangle := by
    ext z
    change (0 ≤ z.2 ∧ 0 ≤ z.1 ∧ z.2 + z.1 ≤ 1) ↔ _
    simp only [unitTriangle,mem_ofPred_eq,add_comm z.2 z.1, and_left_comm]
  refine ⟨hv f hf,region_integral_swap ?_⟩
  rw [hswap]
  apply hv
  apply hf.comp continuous_swap.continuousOn
  intro z hz
  change z ∈ Prod.swap ⁻¹' unitTriangle
  rwa [hswap]

theorem triangle_region_area :
    HasRegionIntegral 0 1 0 1 unitTriangle (fun _ => 1) (1/2) := by
  have h := (triangle_region_both_orders (fun _ => 1) continuous_const.continuousOn).1
  simp_rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at h
  have he : (∫ x in (0 : ℝ)..1, 1-x) = 1/2 := by
    have hx : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub (f := fun _ => 1) intervalIntegrable_const hx,
      intervalIntegral.integral_const,integral_id]
    norm_num
  rwa [he] at h

def parabolaRegion : Set (ℝ × ℝ) := verticalRegion 0 1 (fun x => x^2) id

theorem parabola_region_both_orders (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f parabolaRegion) :
    HasRegionIntegral 0 1 0 1 parabolaRegion f
      (∫ x in (0 : ℝ)..1, ∫ y in x^2..x, f (x,y)) ∧
    HasRegionIntegral 0 1 0 1 parabolaRegion f
      (∫ y in (0 : ℝ)..1, ∫ x in y..Real.sqrt y, f (x,y)) := by
  have hbox : parabolaRegion ⊆ Icc 0 1 ×ˢ Icc 0 1 := by
    rintro z ⟨hx,hy⟩
    exact ⟨hx,⟨(sq_nonneg z.1).trans hy.1,hy.2.trans hx.2⟩⟩
  have hswap : Prod.swap ⁻¹' parabolaRegion = verticalRegion 0 1 id Real.sqrt := by
    ext z
    simpa [parabolaRegion,verticalRegion,mem_Icc,and_assoc] using parabola_slice_bounds z.2 z.1
  refine ⟨(vertical_region_slicing zero_lt_one zero_lt_one _ _ (by fun_prop)
    continuous_id.continuousOn (fun x hx => by
      change x^2 ≤ x
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]) hbox f hf).2,
    region_integral_swap ?_⟩
  rw [hswap]
  have hbox' : verticalRegion 0 1 id Real.sqrt ⊆ Icc 0 1 ×ˢ Icc 0 1 := by
    intro z hz
    have he : z.swap ∈ parabolaRegion := by
      change z ∈ Prod.swap ⁻¹' parabolaRegion
      rwa [hswap]
    exact ⟨(hbox he).2,(hbox he).1⟩
  have hf' : ContinuousOn (fun z : ℝ × ℝ => f z.swap) (verticalRegion 0 1 id Real.sqrt) := by
    apply hf.comp continuous_swap.continuousOn
    intro z hz
    change z ∈ Prod.swap ⁻¹' parabolaRegion
    rwa [hswap]
  exact (vertical_region_slicing zero_lt_one zero_lt_one id Real.sqrt
    continuous_id.continuousOn Real.continuous_sqrt.continuousOn (fun y hy => by
      change y ≤ Real.sqrt y
      have hs := Real.sq_sqrt hy.1
      exact (sq_le_sq₀ hy.1 (Real.sqrt_nonneg y)).mp (by
        nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)])) hbox' _ hf').2

theorem parabola_region_area :
    HasRegionIntegral 0 1 0 1 parabolaRegion (fun _ => 1) (1/6) ∧
      (∫ y in (0 : ℝ)..1, Real.sqrt y-y) = 1/6 := by
  obtain ⟨hv,hh⟩ := parabola_region_both_orders (fun _ => 1) continuous_const.continuousOn
  simp_rw [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hv hh
  have he : (∫ x in (0 : ℝ)..1, x-x^2) = 1/6 := by
    have hx : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
      continuous_id.intervalIntegrable _ _
    have hx2 : IntervalIntegrable (fun x : ℝ => x^2) volume 0 1 :=
      (continuous_id.pow 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hx hx2,integral_id,integral_pow]
    norm_num
  rw [he] at hv
  exact ⟨hv,region_value_unique zero_lt_one zero_lt_one hh hv⟩

def roofRegion : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ 2-z.2}

def roofLeft : Set (ℝ × ℝ) := verticalRegion 0 1 (fun _ => 0) id

def roofRight : Set (ℝ × ℝ) := verticalRegion 1 2 (fun _ => 0) (fun x => 2-x)

theorem roof_region_split : roofRegion = roofLeft ∪ roofRight := by
  ext z
  simp only [roofRegion,roofLeft,roofRight,verticalRegion,mem_union,mem_ofPred_eq,mem_Icc,id_eq]
  constructor
  · rintro ⟨hy,hl,hr⟩
    rcases le_total z.1 1 with hx | hx
    · exact Or.inl ⟨⟨hy.trans hl,hx⟩,hy,hl⟩
    · exact Or.inr ⟨⟨hx,by linarith⟩,hy,by linarith⟩
  · rintro (⟨⟨_,hx⟩,hy,hl⟩ | ⟨⟨hx,_⟩,hy,hr⟩)
    · exact ⟨hy,hl,by linarith⟩
    · exact ⟨hy,by linarith,by linarith⟩

private theorem roof_affine_integral (k m a b : ℝ) :
    (∫ t in a..b, k+m*t) = (b-a)*k + m*((b^2-a^2)/2) := by
  have hm : IntervalIntegrable (fun t : ℝ => m*t) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (f := fun _ => k) intervalIntegrable_const hm,
    intervalIntegral.integral_const,smul_eq_mul,intervalIntegral.integral_const_mul,integral_id]

private theorem roof_quadratic_integral (k m n a b : ℝ) :
    (∫ t in a..b, k+m*t+n*t^2) =
      (b-a)*k + m*((b^2-a^2)/2) + n*((b^3-a^3)/3) := by
  have h₁ : IntervalIntegrable (fun t : ℝ => k+m*t) volume a b :=
    (continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun t : ℝ => n*t^2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h₁ h₂,roof_affine_integral,
    intervalIntegral.integral_const_mul,integral_pow]
  norm_num

theorem roof_region_both_orders :
    HasRegionIntegral 0 2 0 1 roofRegion (fun z => z.1+2*z.2)
      (∫ y in (0 : ℝ)..1, ∫ x in y..(2-y), x+2*y) ∧
    HasRegionIntegral 0 1 0 1 roofLeft (fun z => z.1+2*z.2)
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, x+2*y) ∧
    HasRegionIntegral 1 2 0 1 roofRight (fun z => z.1+2*z.2)
      (∫ x in (1 : ℝ)..2, ∫ y in (0 : ℝ)..(2-x), x+2*y) := by
  have hs : Prod.swap ⁻¹' roofRegion = verticalRegion 0 1 id (fun y => 2-y) := by
    ext z
    change (0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 2-z.1) ↔
      (0 ≤ z.1 ∧ z.1 ≤ 1) ∧ (z.1 ≤ z.2 ∧ z.2 ≤ 2-z.1)
    constructor
    · rintro ⟨h₀,h₁,h₂⟩
      exact ⟨⟨h₀,by linarith⟩,h₁,h₂⟩
    · exact fun h => ⟨h.1.1,h.2⟩
  refine ⟨region_integral_swap ?_, ?_, ?_⟩
  · rw [hs]
    apply (vertical_region_slicing zero_lt_one (by norm_num : (0 : ℝ) < 2) id (fun y => 2-y)
      continuous_id.continuousOn (by fun_prop) (fun y hy => by
        change y ≤ 2-y
        linarith [hy.2]) ?_ _ (by fun_prop)).2
    rintro z ⟨hx,hy⟩
    exact ⟨hx,⟨hx.1.trans hy.1,by dsimp at hy; linarith [hx.1,hy.2]⟩⟩
  · apply (vertical_region_slicing zero_lt_one zero_lt_one (fun _ => 0) id
      continuous_const.continuousOn continuous_id.continuousOn (fun _ hx => hx.1)
      (fun z hz => ⟨hz.1,⟨hz.2.1,hz.2.2.trans hz.1.2⟩⟩) _ (by fun_prop)).2
  · apply (vertical_region_slicing (by norm_num : (1 : ℝ) < 2) zero_lt_one (fun _ => 0)
      (fun x => 2-x) continuous_const.continuousOn (by fun_prop)
      (fun _ hx => sub_nonneg.mpr hx.2) ?_ _ (by fun_prop)).2
    rintro z ⟨hx,hy⟩
    exact ⟨hx,⟨hy.1,by linarith [hx.1,hy.2]⟩⟩

theorem roof_region_integral_values :
    (∫ y in (0 : ℝ)..1, ∫ x in y..(2-y), x+2*y) = 5/3 ∧
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, x+2*y) = 2/3 ∧
    (∫ x in (1 : ℝ)..2, ∫ y in (0 : ℝ)..(2-x), x+2*y) = 1 := by
  constructor
  · have h (y : ℝ) : (∫ x in y..(2-y), x+2*y) = 2+2*y+(-4)*y^2 := by
      calc
        _ = ∫ x in y..(2-y), 2*y+1*x :=
          intervalIntegral.integral_congr (fun x _ => by ring)
        _ = _ := by rw [roof_affine_integral]; ring
    simp_rw [h]
    rw [roof_quadratic_integral]
    norm_num
  constructor
  · have h (x : ℝ) : (∫ y in (0 : ℝ)..x, x+2*y) = 0+0*x+2*x^2 := by
      rw [roof_affine_integral]
      ring
    simp_rw [h]
    rw [roof_quadratic_integral]
    norm_num
  · have h (x : ℝ) : (∫ y in (0 : ℝ)..(2-x), x+2*y) = 4+(-2)*x+0*x^2 := by
      rw [roof_affine_integral]
      ring
    simp_rw [h]
    rw [roof_quadratic_integral]
    norm_num

end Ch13
