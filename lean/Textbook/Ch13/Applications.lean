import Textbook.Ch13.MultipleIntegrals

namespace Ch13

open MeasureTheory Set
open scoped Interval Matrix

noncomputable def laminaMass (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in D, ρ x

noncomputable def laminaMoment (D : Set (ℝ × ℝ))
    (ρ : ℝ × ℝ → ℝ) (coord : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in D, coord x * ρ x

noncomputable def laminaCentroid (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ :=
  (laminaMoment D ρ Prod.fst / laminaMass D ρ,
    laminaMoment D ρ Prod.snd / laminaMass D ρ)

noncomputable def laminaInertiaX (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  laminaMoment D ρ (fun x => x.2^2)

noncomputable def laminaInertiaY (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  laminaMoment D ρ (fun x => x.1^2)

noncomputable def laminaInertiaOrigin (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  laminaMoment D ρ (fun x => x.1^2+x.2^2)

theorem inertia_origin_add (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ)
    (hx : IntegrableOn (fun x => x.2^2 * ρ x) D)
    (hy : IntegrableOn (fun x => x.1^2 * ρ x) D) :
    laminaInertiaOrigin D ρ = laminaInertiaX D ρ + laminaInertiaY D ρ := by
  unfold laminaInertiaOrigin laminaInertiaX laminaInertiaY laminaMoment
  simp only [add_mul]
  rw [integral_add hy hx, add_comm]

theorem density_error (D : Set (ℝ × ℝ)) (ρ σ : ℝ × ℝ → ℝ) (η : ℝ)
    (hD : volume D < ⊤) (hρ : IntegrableOn ρ D) (hσ : IntegrableOn σ D)
    (hη : ∀ x ∈ D, |σ x - ρ x| ≤ η) :
    |laminaMass D σ - laminaMass D ρ| ≤ volume.real D * η := by
  unfold laminaMass
  rw [← integral_sub hσ hρ, ← Real.norm_eq_abs, mul_comm]
  exact norm_setIntegral_le_of_norm_le_const hD (fun x hx => by
    simpa only [Real.norm_eq_abs] using hη x hx)

theorem constant_rectangle_mass :
    (∫ _x : ℝ in (0 : ℝ)..2, ∫ _y : ℝ in (0 : ℝ)..3, (5 : ℝ)) = 30 := by
  norm_num [intervalIntegral.integral_const, smul_eq_mul]

theorem polar_full_derivative (p : ℝ × ℝ) :
    HasFDerivAt polarCoord.symm (fderivPolarCoordSymm p) p :=
  hasFDerivAt_polarCoord_symm p

noncomputable def scalarLineIntegral {E : Type*} [NormedAddCommGroup E]
    (γ velocity : ℝ → E) (w : E → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, w (γ t) * ‖velocity t‖

noncomputable def lineWork {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ velocity : ℝ → E) (F : E → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, inner ℝ (F (γ t)) (velocity t)

theorem scalar_line_reverse {E : Type*} [NormedAddCommGroup E]
    (γ velocity : ℝ → E) (w : E → ℝ) (a b : ℝ) :
    scalarLineIntegral (fun t => γ (a+b-t)) (fun t => -velocity (a+b-t)) w a b =
      scalarLineIntegral γ velocity w a b := by
  unfold scalarLineIntegral
  simp only [norm_neg]
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun t => w (γ t) * ‖velocity t‖) (a := a) (b := b) (a+b)
  simpa only [show a+b-b = a by ring, show a+b-a = b by ring] using h

theorem line_work_reverse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ velocity : ℝ → E) (F : E → E) (a b : ℝ) :
    lineWork (fun t => γ (a+b-t)) (fun t => -velocity (a+b-t)) F a b =
      -lineWork γ velocity F a b := by
  unfold lineWork
  simp only [inner_neg_right]
  rw [intervalIntegral.integral_neg]
  have h := intervalIntegral.integral_comp_sub_left
    (f := fun t => inner ℝ (F (γ t)) (velocity t)) (a := a) (b := b) (a+b)
  simpa only [show a+b-b = a by ring, show a+b-a = b by ring] using congrArg Neg.neg h

noncomputable def scalarSurfaceIntegral (D : Set (ℝ × ℝ))
    (σ du dv : (ℝ × ℝ) → Fin 3 → ℝ) (w : (Fin 3 → ℝ) → ℝ) : ℝ :=
  ∫ p in D, w (σ p) * Real.sqrt (∑ i, (crossProduct (du p) (dv p) i)^2)

noncomputable def surfaceFlux (D : Set (ℝ × ℝ))
    (σ du dv : (ℝ × ℝ) → Fin 3 → ℝ) (F : (Fin 3 → ℝ) → Fin 3 → ℝ) : ℝ :=
  ∫ p in D, ∑ i, F (σ p) i * crossProduct (du p) (dv p) i

theorem polar_disk_second_moment (R : ℝ) :
    (∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi), ∫ r : ℝ in (0 : ℝ)..R, r^3) =
      Real.pi / 2 * R^4 := by
  simp_rw [integral_pow]
  rw [intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  ring

theorem linear_area_factor (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Real.sqrt
      ((A 0 0 ^ 2 + A 1 0 ^ 2) * (A 0 1 ^ 2 + A 1 1 ^ 2) -
        (A 0 0 * A 0 1 + A 1 0 * A 1 1) ^ 2) = |A.det| := by
  have h :
      (A 0 0 ^ 2 + A 1 0 ^ 2) * (A 0 1 ^ 2 + A 1 1 ^ 2) -
        (A 0 0 * A 0 1 + A 1 0 * A 1 1) ^ 2 = A.det ^ 2 := by
    rw [Matrix.det_fin_two]
    ring
  rw [h, Real.sqrt_sq_eq_abs]

theorem disk_iterated_values (R : ℝ) :
    (∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi), ∫ r : ℝ in (0 : ℝ)..R, r) =
      Real.pi * R^2 ∧
    (∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi), ∫ r : ℝ in (0 : ℝ)..R, r^3) =
      Real.pi / 2 * R^4 := by
  exact ⟨polar_disk_area R, polar_disk_second_moment R⟩

end Ch13
