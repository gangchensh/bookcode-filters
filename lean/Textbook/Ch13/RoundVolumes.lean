import Textbook.Ch13.Applications
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace Ch13

open MeasureTheory
open scoped Interval

/-- The two radial powers give the mass and axial moment of the cylinder. -/
theorem cylinder_iterated_values (R H ρ : ℝ) :
    (ρ * ∫ _z : ℝ in (0 : ℝ)..H,
      ∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi), ∫ r : ℝ in (0 : ℝ)..R, r) =
      ρ * Real.pi * R^2 * H ∧
    (ρ * ∫ _z : ℝ in (0 : ℝ)..H,
      ∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi), ∫ r : ℝ in (0 : ℝ)..R, r^3) =
      ρ * Real.pi * H * R^4 / 2 := by
  constructor
  · simp_rw [polar_disk_area, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · simp_rw [polar_disk_second_moment, intervalIntegral.integral_const, smul_eq_mul]
    ring

/-- The spherical iterated integral agrees with the volume of the actual ball. -/
theorem ball_spherical_volume (R : ℝ) (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) =
      (∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi),
        ∫ φ : ℝ in (0 : ℝ)..Real.pi,
          ∫ r : ℝ in (0 : ℝ)..R, r^2 * Real.sin φ) ∧
    (∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi),
      ∫ φ : ℝ in (0 : ℝ)..Real.pi,
        ∫ r : ℝ in (0 : ℝ)..R, r^2 * Real.sin φ) = 4 / 3 * Real.pi * R^3 := by
  have h :
      (∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi),
        ∫ φ : ℝ in (0 : ℝ)..Real.pi,
          ∫ r : ℝ in (0 : ℝ)..R, r^2 * Real.sin φ) = 4 / 3 * Real.pi * R^3 := by
    simp_rw [intervalIntegral.integral_mul_const, integral_pow]
    simp_rw [show (R^3 - (0:ℝ)^3) / (↑(2:ℕ) + 1) = R^3/3 by norm_num]
    simp_rw [intervalIntegral.integral_const_mul, integral_sin, Real.cos_zero, Real.cos_pi,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  refine ⟨?_, h⟩
  rw [h, Measure.real_def, EuclideanSpace.volume_closedBall_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

end Ch13
