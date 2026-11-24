import Textbook.Ch13.Applications

namespace Ch13
open MeasureTheory Set
open scoped Matrix Interval

theorem reflection_odd_integral (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (f : ℝ × ℝ → ℝ) (_hf : IntegrableOn f D (volume.prod volume))
    (hs : ∀ p : ℝ × ℝ, (-p.1,p.2) ∈ D ↔ p ∈ D)
    (ho : ∀ p ∈ D, f (-p.1,p.2) = -f p) :
    (∫ p in D, f p ∂volume.prod volume) = 0 := by
  let T := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
  have hT : MeasurePreserving T (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  have hset : T ⁻¹' D = D := Set.ext hs
  have heq := hT.setIntegral_preimage_emb T.measurableEmbedding f D
  rw [hset] at heq
  have hneg : (∫ p in D, f (T p) ∂volume.prod volume) =
      -(∫ p in D, f p ∂volume.prod volume) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun hD ho
  linarith

theorem shear_scale_reflection (k : ℝ) :
    Matrix.det (!![1,k;0,1] : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∧
    Matrix.det (!![2,0;0,3] : Matrix (Fin 2) (Fin 2) ℝ) = 6 ∧
    Matrix.det (!![-1,0;0,1] : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  norm_num [Matrix.det_fin_two]

theorem triangle_slice_bounds (x y : ℝ) :
    (0 ≤ x ∧ 0 ≤ y ∧ x+y ≤ 1) ↔ (0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1-x) := by
  constructor
  · rintro ⟨hx,hy,hxy⟩
    exact ⟨hx, by linarith, hy, by linarith⟩
  · rintro ⟨hx,_,hy,hxy⟩
    exact ⟨hx,hy,by linarith⟩

theorem parabola_slice_bounds (x y : ℝ) :
    (0 ≤ x ∧ x ≤ 1 ∧ x^2 ≤ y ∧ y ≤ x) ↔
      (0 ≤ y ∧ y ≤ 1 ∧ y ≤ x ∧ x ≤ Real.sqrt y) := by
  constructor
  · rintro ⟨hx,hx1,hxy,hyx⟩
    have hy := (sq_nonneg x).trans hxy
    have hs := Real.sq_sqrt hy
    have hroot := Real.sqrt_nonneg y
    exact ⟨hy, hyx.trans hx1, hyx, by
      apply (sq_le_sq₀ hx hroot).mp
      rwa [hs]⟩
  · rintro ⟨hy,hy1,hyx,hxs⟩
    have hx := hy.trans hyx
    have hroot := Real.sqrt_nonneg y
    have hsq := (sq_le_sq₀ hx hroot).mpr hxs
    rw [Real.sq_sqrt hy] at hsq
    refine ⟨hx, ?_, hsq, hyx⟩
    nlinarith

end Ch13
