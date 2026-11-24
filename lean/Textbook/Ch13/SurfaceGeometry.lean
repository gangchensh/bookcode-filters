import Textbook.Ch13.Applications

namespace Ch13

open MeasureTheory Set
open scoped Matrix Interval

noncomputable def surfacePartial (σ : (ℝ × ℝ) → (Fin 3 → ℝ))
    (d p : ℝ × ℝ) : Fin 3 → ℝ := fderiv ℝ σ p d

theorem surfacePartial_u {σ : (ℝ × ℝ) → (Fin 3 → ℝ)} {p : ℝ × ℝ} {v : Fin 3 → ℝ}
    (hσ : DifferentiableAt ℝ σ p)
    (hv : HasDerivAt (fun t => σ (t, p.2)) v p.1) :
    surfacePartial σ (1, 0) p = v := by
  exact (hσ.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).unique hv

theorem surfacePartial_v {σ : (ℝ × ℝ) → (Fin 3 → ℝ)} {p : ℝ × ℝ} {v : Fin 3 → ℝ}
    (hσ : DifferentiableAt ℝ σ p)
    (hv : HasDerivAt (fun t => σ (p.1, t)) v p.2) :
    surfacePartial σ (0, 1) p = v := by
  exact (hσ.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).unique hv

/-- Regularity on the interior, with a smooth extension across the boundary. -/
def RegularSurface (D : Set (ℝ × ℝ)) (σ : (ℝ × ℝ) → (Fin 3 → ℝ)) : Prop :=
  (∃ U, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ 1 σ U) ∧
    InjOn σ (interior D) ∧
    ∀ p ∈ interior D, crossProduct (surfacePartial σ (1, 0) p)
      (surfacePartial σ (0, 1) p) ≠ 0

noncomputable def surfaceAreaFactor (p q : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (∑ i, (crossProduct p q i)^2)

theorem surface_gram_factor (p q : Fin 3 → ℝ) :
    surfaceAreaFactor p q =
      Real.sqrt ((∑ i, (p i)^2) * (∑ i, (q i)^2) - (∑ i, p i * q i)^2) := by
  unfold surfaceAreaFactor
  congr 1
  simp [Fin.sum_univ_three, cross_apply]
  ring

noncomputable def cylinderSide (R : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![R * Real.cos p.1, R * Real.sin p.1, p.2]

noncomputable def cylinderTheta (R : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![-R * Real.sin p.1, R * Real.cos p.1, 0]

def cylinderZ (_p : ℝ × ℝ) : Fin 3 → ℝ := ![0, 0, 1]

def horizontalRadial (p : Fin 3 → ℝ) : Fin 3 → ℝ := ![p 0, p 1, 0]

theorem cylinder_side_partials (R : ℝ) (p : ℝ × ℝ) :
    surfacePartial (cylinderSide R) (1,0) p = cylinderTheta R p ∧
      surfacePartial (cylinderSide R) (0,1) p = cylinderZ p := by
  have hσ : DifferentiableAt ℝ (cylinderSide R) p := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [cylinderSide] <;> fun_prop
  constructor
  · apply surfacePartial_u hσ
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [cylinderSide, cylinderTheta, mul_neg, neg_mul] using
        (Real.hasDerivAt_cos p.1).const_mul R
    · simpa [cylinderSide, cylinderTheta] using (Real.hasDerivAt_sin p.1).const_mul R
    · simpa [cylinderSide, cylinderTheta] using hasDerivAt_const p.1 p.2
  · apply surfacePartial_v hσ
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [cylinderSide, cylinderZ] using hasDerivAt_const p.2 (R * Real.cos p.1)
    · simpa [cylinderSide, cylinderZ] using hasDerivAt_const p.2 (R * Real.sin p.1)
    · simpa [cylinderSide, cylinderZ] using hasDerivAt_id' p.2

theorem cylinder_side_cross (R : ℝ) (p : ℝ × ℝ) :
    crossProduct (cylinderTheta R p) (cylinderZ p) =
      horizontalRadial (cylinderSide R p) := by
  ext i
  fin_cases i <;> simp [cylinderTheta, cylinderZ, horizontalRadial, cylinderSide, cross_apply]

theorem cylinder_side_flux (R H : ℝ) (hH : 0 ≤ H) :
    surfaceFlux (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) H)
      (cylinderSide R) (cylinderTheta R) cylinderZ horizontalRadial =
      2 * Real.pi * R^2 * H := by
  unfold surfaceFlux
  have h (p : ℝ × ℝ) :
      (∑ i, horizontalRadial (cylinderSide R p) i *
        crossProduct (cylinderTheta R p) (cylinderZ p) i) = R^2 := by
    rw [cylinder_side_cross]
    rw [Fin.sum_univ_three]
    change (R * Real.cos p.1) * (R * Real.cos p.1) +
      (R * Real.sin p.1) * (R * Real.sin p.1) + 0 * 0 = R^2
    nlinarith [congrArg (fun x : ℝ => R^2 * x) (Real.sin_sq_add_cos_sq p.1)]
  simp_rw [h]
  rw [setIntegral_const, Measure.real_def, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc, ENNReal.toReal_mul, sub_zero, sub_zero,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), ENNReal.toReal_ofReal hH]
  simp only [smul_eq_mul]
  ring

end Ch13
