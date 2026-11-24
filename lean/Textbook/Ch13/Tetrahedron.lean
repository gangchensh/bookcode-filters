import Textbook.Ch13.Audit

namespace Ch13
open Set MeasureTheory Filter
open scoped Interval

def unitTetrahedron : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1+p.2.1+p.2.2 ≤ 1}

theorem tetrahedron_slice_bounds (x y z : ℝ) :
    (x,y,z) ∈ unitTetrahedron ↔ x ∈ Icc 0 1 ∧ y ∈ Icc 0 (1-x) ∧ z ∈ Icc 0 (1-x-y) := by
  change (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x+y+z ≤ 1) ↔ _
  constructor
  · rintro ⟨hx,hy,hz,h⟩
    exact ⟨⟨hx,by linarith⟩,⟨hy,by linarith⟩,⟨hz,by linarith⟩⟩
  · rintro ⟨hx,hy,hz⟩
    exact ⟨hx.1,hy.1,hz.1,by linarith [hz.2]⟩

private theorem tetrahedron_compact : IsCompact unitTetrahedron := by
  have hc : IsClosed unitTetrahedron := by
    change IsClosed ({p : ℝ × ℝ × ℝ | 0 ≤ p.1} ∩
      ({p | 0 ≤ p.2.1} ∩ ({p | 0 ≤ p.2.2} ∩ {p | p.1+p.2.1+p.2.2 ≤ 1})))
    repeat' apply IsClosed.inter
    all_goals apply isClosed_le <;> fun_prop
  have hbox : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  apply hbox.of_isClosed_subset hc
  intro p hp
  obtain ⟨hx,hy,hz⟩ := (tetrahedron_slice_bounds p.1 p.2.1 p.2.2).1 hp
  exact ⟨hx,⟨hy.1,by linarith [hx.1,hy.2]⟩,⟨hz.1,by linarith [hx.1,hy.1,hz.2]⟩⟩

/-- Integrate the zero extension in the surrounding product space and read off the slices. -/
theorem tetrahedron_iterated_integral (f : ℝ × ℝ × ℝ → ℝ)
    (hf : ContinuousOn f unitTetrahedron) :
    (∫ p in unitTetrahedron, f p ∂volume.prod (volume.prod volume)) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1-x), ∫ z in (0 : ℝ)..(1-x-y), f (x,y,z) := by
  let D := unitTetrahedron
  let g := D.indicator f
  have hm : MeasurableSet D := tetrahedron_compact.isClosed.measurableSet
  have hi : Integrable g (volume.prod (volume.prod volume)) :=
    (integrable_indicator_iff hm).2 (hf.integrableOn_compact tetrahedron_compact)
  rw [← integral_indicator hm]
  change (∫ p, g p ∂volume.prod (volume.prod volume)) = _
  rw [integral_prod g hi]
  calc
    _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, g (x,y,z) := by
      apply integral_congr_ae
      filter_upwards [hi.prod_right_ae] with x hx
      exact integral_prod _ hx
    _ = _ := by
      rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,
        ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      by_cases hx : x ∈ Icc 0 1
      · rw [indicator_of_mem hx,intervalIntegral.integral_of_le (sub_nonneg.mpr hx.2),
          ← integral_Icc_eq_integral_Ioc,← integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        apply ae_of_all
        intro y
        by_cases hy : y ∈ Icc 0 (1-x)
        · have hxy : 0 ≤ 1-x-y := sub_nonneg.mpr hy.2
          change (∫ z : ℝ, g (x,y,z)) =
            (Icc 0 (1-x)).indicator (fun t => ∫ z in (0 : ℝ)..(1-x-t), f (x,t,z)) y
          rw [indicator_of_mem hy,intervalIntegral.integral_of_le hxy,
            ← integral_Icc_eq_integral_Ioc,← integral_indicator measurableSet_Icc]
          apply integral_congr_ae
          apply ae_of_all
          intro z
          change D.indicator f (x,y,z) = (Icc 0 (1-x-y)).indicator (fun t => f (x,y,t)) z
          by_cases hz : z ∈ Icc 0 (1-x-y)
          · rw [indicator_of_mem ((tetrahedron_slice_bounds x y z).2 ⟨hx,hy,hz⟩),
              indicator_of_mem hz]
          · rw [indicator_of_notMem (fun h => hz ((tetrahedron_slice_bounds x y z).1 h).2.2),
              indicator_of_notMem hz]
        · have hz (z : ℝ) : g (x,y,z) = 0 :=
            indicator_of_notMem (fun h => hy ((tetrahedron_slice_bounds x y z).1 h).2.1) _
          simp [hz,indicator_of_notMem hy]
      · have hz (y z : ℝ) : g (x,y,z) = 0 :=
          indicator_of_notMem (fun h => hx ((tetrahedron_slice_bounds x y z).1 h).1) _
        simp [hz,indicator_of_notMem hx]

private theorem tetra_slice_constant (k s : ℝ) :
    (∫ y in (0 : ℝ)..s, ∫ _z in (0 : ℝ)..(s-y), k) = k*(s^2/2) := by
  simp only [intervalIntegral.integral_const,smul_eq_mul,sub_zero]
  have he : (fun y : ℝ => (s-y)*k) = fun y => k*(s-y) := by
    funext y
    ring
  rw [he,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t) s,sub_self,sub_zero,integral_id]
  ring

private theorem tetra_slice_y (s : ℝ) :
    (∫ y in (0 : ℝ)..s, ∫ _z in (0 : ℝ)..(s-y), y) = s^3/6 := by
  simp only [intervalIntegral.integral_const,smul_eq_mul,sub_zero]
  have he : (fun y : ℝ => (s-y)*y) = fun y => s*y-y^2 := by
    funext y
    ring
  rw [he,intervalIntegral.integral_sub
    (show IntervalIntegrable (fun y : ℝ => s*y) volume 0 s from
      (continuous_const.mul continuous_id).intervalIntegrable _ _)
    (show IntervalIntegrable (fun y : ℝ => y^2) volume 0 s from
      (continuous_id.pow 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,integral_id,integral_pow]
  ring

private theorem tetra_slice_z (s : ℝ) :
    (∫ y in (0 : ℝ)..s, ∫ z in (0 : ℝ)..(s-y), z) = s^3/6 := by
  simp only [integral_id,zero_pow (by norm_num : 2 ≠ 0),sub_zero]
  have he : (fun y : ℝ => (s-y)^2/2) = fun y => (1/2 : ℝ)*(s-y)^2 := by
    funext y
    ring
  rw [he,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t^2) s,sub_self,sub_zero,integral_pow]
  ring

private theorem tetra_outer_power (n : ℕ) :
    (∫ x in (0 : ℝ)..1, (1-x)^n) = 1/(n+1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t^n) 1,
    sub_self,sub_zero,integral_pow]
  simp

theorem tetrahedron_volume_moments :
    (∫ _ in unitTetrahedron, (1 : ℝ) ∂volume.prod (volume.prod volume)) = 1/6 ∧
    (∫ p in unitTetrahedron, p.1 ∂volume.prod (volume.prod volume)) = 1/24 ∧
    (∫ p in unitTetrahedron, p.2.1 ∂volume.prod (volume.prod volume)) = 1/24 ∧
    (∫ p in unitTetrahedron, p.2.2 ∂volume.prod (volume.prod volume)) = 1/24 := by
  constructor
  · rw [tetrahedron_iterated_integral _ continuous_const.continuousOn]
    simp_rw [tetra_slice_constant,one_mul,div_eq_inv_mul]
    -- Factor the constant out of the outer integral.
    rw [intervalIntegral.integral_const_mul,tetra_outer_power]
    norm_num
  constructor
  · rw [tetrahedron_iterated_integral _ continuous_fst.continuousOn]
    change (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1-x), ∫ _z in (0 : ℝ)..(1-x-y), x) = _
    simp_rw [tetra_slice_constant]
    have h : (fun x : ℝ => x*((1-x)^2/2)) =
        fun x => (1/2 : ℝ)*((1-x)^2-(1-x)^3) := by
      funext x
      ring
    rw [h,intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
      (show IntervalIntegrable (fun x : ℝ => (1-x)^2) volume 0 1 from
        (show Continuous (fun x : ℝ => (1-x)^2) by fun_prop).intervalIntegrable _ _)
      (show IntervalIntegrable (fun x : ℝ => (1-x)^3) volume 0 1 from
        (show Continuous (fun x : ℝ => (1-x)^3) by fun_prop).intervalIntegrable _ _),
      tetra_outer_power,tetra_outer_power]
    norm_num
  constructor
  · have hc : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) :=
      continuous_fst.comp continuous_snd
    rw [tetrahedron_iterated_integral _ hc.continuousOn]
    change (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1-x), ∫ _z in (0 : ℝ)..(1-x-y), y) = _
    simp_rw [tetra_slice_y,div_eq_inv_mul]
    rw [intervalIntegral.integral_const_mul,tetra_outer_power]
    norm_num
  · have hc : Continuous (fun p : ℝ × ℝ × ℝ => p.2.2) :=
      continuous_snd.comp continuous_snd
    rw [tetrahedron_iterated_integral _ hc.continuousOn]
    change (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1-x), ∫ z in (0 : ℝ)..(1-x-y), z) = _
    simp_rw [tetra_slice_z,div_eq_inv_mul]
    rw [intervalIntegral.integral_const_mul,tetra_outer_power]
    norm_num

theorem tetrahedron_centroid :
    let μ := volume.prod (volume.prod volume)
    let V := ∫ _ in unitTetrahedron, (1 : ℝ) ∂μ
    ((∫ p in unitTetrahedron, p.1 ∂μ)/V,
      (∫ p in unitTetrahedron, p.2.1 ∂μ)/V,
      (∫ p in unitTetrahedron, p.2.2 ∂μ)/V) = ((1/4 : ℝ),1/4,1/4) := by
  dsimp only
  obtain ⟨hV,hx,hy,hz⟩ := tetrahedron_volume_moments
  rw [hV,hx,hy,hz]
  norm_num

end Ch13
