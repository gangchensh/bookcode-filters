import Textbook.Ch13.Audit
import Textbook.Ch13.Applications

namespace Ch13
open MeasureTheory Set Filter
open scoped Interval Matrix BigOperators ENNReal Topology

/-- The common lower and upper integral bounds determine a unique value. -/
theorem integral_agreement_of_sandwich {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : X → ℝ) (I : ℝ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ ε > 0, ∃ l u : X → ℝ,
      Integrable l μ ∧ Integrable u μ ∧ (∀ᵐ x ∂μ, l x ≤ f x) ∧
      (∀ᵐ x ∂μ, f x ≤ u x) ∧
      (∫ x, l x ∂μ) ≤ I ∧ I ≤ (∫ x, u x ∂μ) ∧
      (∫ x, u x ∂μ) - (∫ x, l x ∂μ) < ε) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = I := by
  have hfi : Integrable f μ := by
    obtain ⟨l,u,hl,hu,hlf,hfu,_⟩ := h 1 zero_lt_one
    apply (hl.norm.add hu.norm).mono' hf
    filter_upwards [hlf, hfu] with x hx hy
    change ‖f x‖ ≤ ‖l x‖ + ‖u x‖
    simp only [Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (l x), abs_nonneg (u x)]
    · linarith [le_abs_self (u x), abs_nonneg (l x)]
  refine ⟨hfi, ?_⟩
  by_contra hn
  have hp : 0 < |(∫ x, f x ∂μ) - I| := abs_pos.mpr (sub_ne_zero.mpr hn)
  obtain ⟨l,u,hl,hu,hlf,hfu,hlI,hIu,hgap⟩ := h _ hp
  have hl' := integral_mono_ae hl hfi hlf
  have hu' := integral_mono_ae hfi hu hfu
  rcases le_total (∫ x, f x ∂μ) I with hle | hge
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hgap
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hge)] at hgap
    linarith

theorem cross_columns (p q : Fin 3 → ℝ) (a b c d : ℝ) :
    crossProduct (a • p + c • q) (b • p + d • q) =
      (a*d-b*c) • crossProduct p q := by
  funext i
  fin_cases i <;> simp [cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem cross_area_scale (p q : Fin 3 → ℝ) (a b c d : ℝ) :
    Real.sqrt (∑ i, (crossProduct (a • p + c • q) (b • p + d • q) i)^2) =
      |a*d-b*c| * Real.sqrt (∑ i, (crossProduct p q i)^2) := by
  rw [cross_columns]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem surface_pullback (E D : Set (ℝ × ℝ)) (Φ : (ℝ × ℝ) → ℝ × ℝ)
    (J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (σ du dv : (ℝ × ℝ) → Fin 3 → ℝ) (w : (Fin 3 → ℝ) → ℝ)
    (a b c d : (ℝ × ℝ) → ℝ)
    (hE : MeasurableSet E) (hD : Φ '' E = D) (hΦ : InjOn Φ E)
    (hJ : ∀ x ∈ E, HasFDerivWithinAt Φ (J x) E x)
    (hdet : ∀ x ∈ E, (J x).det = a x*d x-b x*c x)
    (hf : IntegrableOn
      (fun x => w (σ x) * Real.sqrt (∑ i, (crossProduct (du x) (dv x) i)^2)) D) :
    scalarSurfaceIntegral E (σ ∘ Φ)
      (fun x => a x • du (Φ x) + c x • dv (Φ x))
      (fun x => b x • du (Φ x) + d x • dv (Φ x)) w =
      scalarSurfaceIntegral D σ du dv w := by
  let f := fun x => w (σ x) * Real.sqrt (∑ i, (crossProduct (du x) (dv x) i)^2)
  have hfi : IntegrableOn f (Φ '' E) := by rw [hD]; exact hf
  have h := (change_variables E Φ J f hE hJ hΦ hfi).2
  rw [hD] at h
  unfold scalarSurfaceIntegral
  rw [h]
  apply setIntegral_congr_fun hE
  intro x hx
  dsimp [f, Function.comp_def]
  rw [cross_area_scale, hdet x hx]
  ring

theorem length_from_chord_estimate {V : Type*} [NormedAddCommGroup V]
    (γ v : ℝ → V) {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b))
    (hchord : ∀ η > 0, ∃ δ > 0, ∀ P : Ch09.TaggedPartition a b, P.mesh < δ →
      ∀ i : Fin (P.n + 1),
        |‖γ (P.points i.succ) - γ (P.points i.castSucc)‖ -
          ‖v (P.tag i)‖ * P.width i| ≤ η * P.width i) :
    HasPolygonalLength (Ch09.TaggedPartition.mesh (a := a) (b := b)) (polygonalSum γ)
      (∫ t in a..b, ‖v t‖) := by
  apply (curve_length_mesh_iff γ _).2
  intro ε hε
  let η := ε / (2 * (b-a))
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hc⟩ := hchord η hη
  have hi := Ch09.continuous_tagged_integral hab hv.norm
  obtain ⟨d, hd, hs⟩ := (Ch09.tagged_integral_iff _ _ _ _).1 hi (ε/2) (half_pos hε)
  refine ⟨min δ d, lt_min hδ hd, ?_⟩
  intro P hP
  have hwidth : (∑ i : Fin (P.n+1), P.width i) = b-a := by
    unfold Ch09.TaggedPartition.width
    rw [Ch09.sum_endpoint_differences, P.first, P.last]
  have hsum : |polygonalSum γ P - P.riemannSum (fun t => ‖v t‖)| ≤ η * (b-a) := by
    unfold polygonalSum Ch09.TaggedPartition.riemannSum
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin (P.n+1), |‖γ (P.points i.succ) - γ (P.points i.castSucc)‖ -
            ‖v (P.tag i)‖ * P.width i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (P.n+1), η * P.width i :=
        Finset.sum_le_sum (fun i _ => hc P (hP.trans_le (min_le_left _ _)) i)
      _ = η * (b-a) := by rw [← Finset.mul_sum, hwidth]
  have hηeq : η * (b-a) = ε/2 := by
    dsimp [η]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
  rw [hηeq] at hsum
  exact (abs_sub_le _ (P.riemannSum (fun t => ‖v t‖)) _).trans_lt
    (by linarith [hs P (hP.trans_le (min_le_right _ _))])

theorem length_of_continuous_velocity {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (γ v : ℝ → V) {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t) :
    HasPolygonalLength (Ch09.TaggedPartition.mesh (a := a) (b := b)) (polygonalSum γ)
      (∫ t in a..b, ‖v t‖) := by
  apply length_from_chord_estimate γ v hab hv
  intro η hη
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hv) η hη
  refine ⟨δ, hδ, ?_⟩
  intro P hP i
  let l := P.points i.castSucc
  let r := P.points i.succ
  have hlr : l ≤ r := (P.increasing (Fin.castSucc_lt_succ (i := i))).le
  have hsub : Icc l r ⊆ Icc a b := P.subinterval_subset i
  have hvi : IntervalIntegrable v volume l r := (hv.mono hsub).intervalIntegrable_of_Icc hlr
  have hFTC : (∫ t in l..r, v t) = γ r - γ l := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr (hcont.mono hsub) _ hvi
    intro t ht
    have hleft := (hsub (left_mem_Icc.mpr hlr)).1
    have hright := (hsub (right_mem_Icc.mpr hlr)).2
    exact hγ t ⟨hleft.trans_lt ht.1, ht.2.trans_le hright⟩
  have hwidth : r-l ≤ P.mesh := Finset.le_sup' (f := P.width) (Finset.mem_univ i)
  have hbound : ∀ x ∈ Ι l r, ‖v x - v (P.tag i)‖ ≤ η := by
    rw [uIoc_of_le hlr]
    intro x hx
    have hx' : x ∈ Icc l r := Ioc_subset_Icc_self hx
    have ht : P.tag i ∈ Icc l r := P.tag_mem i
    have hdist : dist x (P.tag i) ≤ r-l := by
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [ht.2, hx'.1], by linarith [ht.1, hx'.2]⟩
    rw [← dist_eq_norm]
    exact (huc x (hsub hx') _ (hsub ht) (hdist.trans_lt (hwidth.trans_lt hP))).le
  have herr := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub hvi intervalIntegrable_const,
    hFTC, intervalIntegral.integral_const, abs_of_nonneg (sub_nonneg.mpr hlr)] at herr
  have hnorm := abs_norm_sub_norm_le (γ r - γ l) ((r-l) • v (P.tag i))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlr)] at hnorm
  change |‖γ r-γ l‖ - ‖v (P.tag i)‖ * (r-l)| ≤ η * (r-l)
  rw [mul_comm ‖v (P.tag i)‖]
  exact hnorm.trans herr

noncomputable def nonnegativeRegionIntegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (D : Set X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in D, f x ∂μ

theorem nonnegative_region_exhaustion {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : Set X) (Dk : ℕ → Set X) (f : X → ℝ≥0∞)
    (hf : Measurable f) (hm : ∀ k, MeasurableSet (Dk k))
    (hmono : Monotone Dk) (hD : (⋃ k, Dk k) = D) :
    Tendsto (fun k => nonnegativeRegionIntegral μ (Dk k) f) atTop
      (𝓝 (nonnegativeRegionIntegral μ D f)) := by
  let g := fun k => (Dk k).indicator f
  have hgm : ∀ k, Measurable (g k) := fun k => hf.indicator (hm k)
  have hgmono : Monotone g := by
    intro i j hij x
    by_cases hx : x ∈ Dk i
    · simp [g, hx, hmono hij hx]
    · simp [g, hx]
  have hmeas : MeasurableSet D := hD ▸ MeasurableSet.iUnion hm
  have hsup : (fun x => ⨆ k, g k x) = D.indicator f := by
    funext x
    by_cases hx : x ∈ D
    · have hmem : x ∈ ⋃ k, Dk k := hD.symm ▸ hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hmem
      rw [indicator_of_mem hx]
      apply le_antisymm
      · apply iSup_le
        intro j
        by_cases hj : x ∈ Dk j <;> simp [g, hj]
      · have hk' : g k x = f x := indicator_of_mem hk f
        exact hk'.symm.le.trans (le_iSup (fun j => g j x) k)
    · have hout (k : ℕ) : x ∉ Dk k := fun hk => hx (hD ▸ mem_iUnion.mpr ⟨k,hk⟩)
      simp [g, indicator_of_notMem, hx, hout]
  have hi : nonnegativeRegionIntegral μ D f = ⨆ k, nonnegativeRegionIntegral μ (Dk k) f := by
    calc
      _ = ∫⁻ x, D.indicator f x ∂μ := (lintegral_indicator hmeas f).symm
      _ = ⨆ k, ∫⁻ x, g k x ∂μ := by rw [← hsup, lintegral_iSup hgm hgmono]
      _ = _ := by
        congr with k
        exact lintegral_indicator (hm k) f
  rw [hi]
  exact tendsto_atTop_iSup (fun i j hij => lintegral_mono_set (hmono hij))

end Ch13
