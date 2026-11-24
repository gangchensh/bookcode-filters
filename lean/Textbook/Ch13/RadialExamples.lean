import Textbook.Ch13.PolarApplications
import Textbook.Ch13.RoundVolumes

namespace Ch13

open MeasureTheory Set
open scoped Interval

def solidCylinder (R H : ℝ) : Set ((ℝ × ℝ) × ℝ) := roundDisk R ×ˢ Icc 0 H

/-- Evaluate both integrals on the solid, with Cartesian weight in the axial moment. -/
theorem solidCylinder_mass_moment (R H ρ : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) :
    (∫ p in solidCylinder R H, ρ) = ρ * Real.pi * R^2 * H ∧
    (∫ p in solidCylinder R H, ρ * (p.1.1^2+p.1.2^2)) = ρ * Real.pi * H * R^4 / 2 := by
  have hd := roundDisk_polar R hR (fun _ => (1 : ℝ)) continuous_const.continuousOn
  simp only [mul_one, polar_disk_area] at hd
  have hm := roundDisk_polar R hR (fun p => p.1^2 + p.2^2)
    (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => p.1^2 + p.2^2) (roundDisk R))
  simp_rw [polar_radius_sq, show ∀ r : ℝ, r * r^2 = r^3 by intro r; ring,
    polar_disk_second_moment] at hm
  have hz : (∫ _z in Icc (0 : ℝ) H, (1 : ℝ)) = H := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hH]
    simp
  constructor
  · have hprod := setIntegral_prod_mul (μ := (volume : Measure (ℝ × ℝ)))
        (ν := (volume : Measure ℝ)) (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
        (roundDisk R) (Icc (0:ℝ) H)
    simp only [mul_one] at hprod
    rw [solidCylinder, ← show ρ * (1:ℝ) = ρ by ring, integral_const_mul,
      Measure.volume_eq_prod, hprod, hd, hz]
    ring
  · have hprod := setIntegral_prod_mul (μ := (volume : Measure (ℝ × ℝ)))
        (ν := (volume : Measure ℝ)) (fun p => p.1^2+p.2^2) (fun _ => (1:ℝ))
        (roundDisk R) (Icc (0:ℝ) H)
    simp only [mul_one] at hprod
    rw [solidCylinder, integral_const_mul, Measure.volume_eq_prod, hprod,
      hm, hz]
    ring

noncomputable def radialGaussian (p : ℝ × ℝ) : ℝ := Real.exp (-(p.1^2+p.2^2))

theorem radial_gaussian_plane :
    Integrable radialGaussian ∧ (∫ p, radialGaussian p) = Real.pi := by
  have h : radialGaussian = fun p => Real.exp (-(p.1^2)) * Real.exp (-(p.2^2)) := by
    funext p
    unfold radialGaussian
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h, Measure.volume_eq_prod]
  refine ⟨gaussian_integrable.mul_prod gaussian_integrable, ?_⟩
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-(x^2))) (fun x : ℝ => Real.exp (-(x^2))),
    gaussian_integral, ← pow_two, Real.sq_sqrt Real.pi_pos.le]

theorem radial_gaussian_disk (R : ℝ) (hR : 0 ≤ R) :
    (∫ p in roundDisk R, radialGaussian p) = Real.pi * (1 - Real.exp (-R^2)) := by
  rw [roundDisk_polar R hR radialGaussian (by unfold radialGaussian; fun_prop)]
  have hanti (r : ℝ) :
      HasDerivAt (fun t : ℝ => (-1/2) * Real.exp (-(t^2)))
        (r * Real.exp (-(r^2))) r := by
    convert (((hasDerivAt_pow 2 r).neg.exp).const_mul (-1/2)) using 1 <;> dsimp <;> push_cast <;> ring
  have hI :
      (∫ r : ℝ in (0 : ℝ)..R, r * Real.exp (-(r^2))) =
        (1 - Real.exp (-R^2))/2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hanti r)
      ((by fun_prop : Continuous (fun r : ℝ => r * Real.exp (-(r^2)))).intervalIntegrable _ _)]
    simp only [zero_pow (by decide : 2 ≠ 0), neg_zero, Real.exp_zero, mul_one]
    ring
  simp_rw [radialGaussian, polar_radius_sq, hI, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  ring

theorem radial_gaussian_tail (R : ℝ) (hR : 0 ≤ R) :
    (∫ p in (roundDisk R)ᶜ, radialGaussian p) = Real.pi * Real.exp (-R^2) := by
  have h := integral_add_compl (roundDisk_measurable R) radial_gaussian_plane.1
  rw [radial_gaussian_disk R hR, radial_gaussian_plane.2] at h
  linarith

theorem radial_gaussian_cutoff (R ε : ℝ) (hε : 0 < ε) (hεπ : ε < Real.pi)
    (hR : Real.sqrt (Real.log (Real.pi/ε)) ≤ R) :
    (∫ p in (roundDisk R)ᶜ, radialGaussian p) ≤ ε := by
  have hlog : 0 ≤ Real.log (Real.pi/ε) :=
    Real.log_nonneg ((le_div_iff₀ hε).mpr (by simpa using hεπ.le))
  have hR₀ := (Real.sqrt_nonneg _).trans hR
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hR₀).mpr hR
  rw [Real.sq_sqrt hlog] at hs
  rw [radial_gaussian_tail R hR₀]
  calc
    _ ≤ Real.pi * Real.exp (-Real.log (Real.pi/ε)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hs)) Real.pi_pos.le
    _ = _ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp

end Ch13
