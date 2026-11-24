import Textbook.Ch13.Bridges

namespace Ch13
open MeasureTheory Set
open scoped Matrix

theorem plane_map_columns {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (ℝ × ℝ) →L[ℝ] V) (x : ℝ × ℝ) :
    L x = x.1 • L (1,0) + x.2 • L (0,1) := by
  have hx : x.1 • ((1,0) : ℝ × ℝ) + x.2 • ((0,1) : ℝ × ℝ) = x := by
    ext <;> simp
  calc
    L x = L (x.1 • ((1,0) : ℝ × ℝ) + x.2 • ((0,1) : ℝ × ℝ)) :=
      congrArg (fun z => L z) hx.symm
    _ = _ := by simp only [map_add, map_smul]

theorem plane_map_det_columns (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    L.det = (L (1,0)).1 * (L (0,1)).2 - (L (0,1)).1 * (L (1,0)).2 := by
  have heq : L = (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
      !![(L (1,0)).1, (L (0,1)).1; (L (1,0)).2, (L (0,1)).2]).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
    calc
      L x = _ := plane_map_columns L x
      _ = _ := by ext <;> simp [mul_comm]
  conv_lhs => rw [heq]
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]

theorem cross_of_composed_columns
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (M : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ)) :
    crossProduct (M.comp L (1,0)) (M.comp L (0,1)) =
      L.det • crossProduct (M (1,0)) (M (0,1)) := by
  have hc (x : ℝ × ℝ) : M.comp L x = (L x).1 • M (1,0) + (L x).2 • M (0,1) := by
    exact plane_map_columns M (L x)
  rw [hc, hc, cross_columns, plane_map_det_columns]

theorem scalar_surface_reparam
    (E D : Set (ℝ × ℝ)) (Φ : (ℝ × ℝ) → ℝ × ℝ)
    (J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (σ : (ℝ × ℝ) → Fin 3 → ℝ)
    (M : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ)) (w : (Fin 3 → ℝ) → ℝ)
    (hE : MeasurableSet E) (hD : Φ '' E = D) (hΦ : InjOn Φ E)
    (hJ : ∀ x ∈ E, HasFDerivAt Φ (J x) x)
    (hM : ∀ x ∈ D, HasFDerivAt σ (M x) x)
    (hf : IntegrableOn (fun x => w (σ x) *
      Real.sqrt (∑ i, (crossProduct (M x (1,0)) (M x (0,1)) i)^2)) D) :
    (∀ x ∈ E, HasFDerivAt (σ ∘ Φ) ((M (Φ x)).comp (J x)) x) ∧
    scalarSurfaceIntegral E (σ ∘ Φ)
      (fun x => (M (Φ x)).comp (J x) (1,0))
      (fun x => (M (Φ x)).comp (J x) (0,1)) w =
      scalarSurfaceIntegral D σ (fun x => M x (1,0)) (fun x => M x (0,1)) w := by
  refine ⟨fun x hx => (hM (Φ x) (hD ▸ mem_image_of_mem Φ hx)).comp x (hJ x hx), ?_⟩
  have hc (x z : ℝ × ℝ) :
      (M (Φ x)).comp (J x) z =
        (J x z).1 • M (Φ x) (1,0) + (J x z).2 • M (Φ x) (0,1) := by
    exact plane_map_columns (M (Φ x)) (J x z)
  simp_rw [hc]
  exact surface_pullback E D Φ J σ (fun x => M x (1,0)) (fun x => M x (0,1)) w
    (fun x => (J x (1,0)).1) (fun x => (J x (0,1)).1)
    (fun x => (J x (1,0)).2) (fun x => (J x (0,1)).2)
    hE hD hΦ (fun x hx => (hJ x hx).hasFDerivWithinAt)
    (fun x _ => plane_map_det_columns (J x)) hf

end Ch13
