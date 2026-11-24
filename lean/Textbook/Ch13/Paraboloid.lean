import Textbook.Ch13.PolarApplications
import Textbook.Ch13.SurfaceGeometry

namespace Ch13

open MeasureTheory
open scoped Interval Matrix

def paraboloid (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1, p.2, p.1^2+p.2^2]

def paraboloidU (p : ℝ × ℝ) : Fin 3 → ℝ := ![1, 0, 2*p.1]
def paraboloidV (p : ℝ × ℝ) : Fin 3 → ℝ := ![0, 1, 2*p.2]

theorem paraboloid_partials (p : ℝ × ℝ) :
    surfacePartial paraboloid (1,0) p = paraboloidU p ∧
      surfacePartial paraboloid (0,1) p = paraboloidV p := by
  have hσ : DifferentiableAt ℝ paraboloid p := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [paraboloid] <;> fun_prop
  constructor
  · apply surfacePartial_u hσ
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [paraboloid, paraboloidU] using hasDerivAt_id' p.1
    · simpa [paraboloid, paraboloidU] using hasDerivAt_const p.1 p.2
    · simpa [paraboloid, paraboloidU] using
        (hasDerivAt_pow 2 p.1).add_const (p.2^2)
  · apply surfacePartial_v hσ
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [paraboloid, paraboloidV] using hasDerivAt_const p.2 p.1
    · simpa [paraboloid, paraboloidV] using hasDerivAt_id' p.2
    · simpa [paraboloid, paraboloidV] using
        (hasDerivAt_pow 2 p.2).const_add (p.1^2)

theorem paraboloid_cross (p : ℝ × ℝ) :
    crossProduct (paraboloidU p) (paraboloidV p) = ![-2*p.1, -2*p.2, 1] := by
  ext i
  fin_cases i <;> simp [paraboloidU, paraboloidV, cross_apply]

theorem paraboloid_area (R : ℝ) (hR : 0 ≤ R) :
    scalarSurfaceIntegral (roundDisk R) paraboloid paraboloidU paraboloidV (fun _ => 1) =
      Real.pi/6 * ((1+4*R^2) ^ (3/2 : ℝ) - 1) := by
  unfold scalarSurfaceIntegral
  have hf (p : ℝ × ℝ) :
      (1:ℝ) * Real.sqrt (∑ i, (crossProduct (paraboloidU p) (paraboloidV p) i)^2) =
        Real.sqrt (1 + 4 * (p.1^2 + p.2^2)) := by
    rw [one_mul, paraboloid_cross, Fin.sum_univ_three]
    congr 1
    change (-2*p.1)^2+(-2*p.2)^2+(1:ℝ)^2 = _
    ring
  simp_rw [hf]
  rw [roundDisk_polar R hR _ (by fun_prop)]
  simp_rw [polar_radius_sq]
  have hanti (r : ℝ) :
      HasDerivAt (fun t : ℝ => (1+4*t^2) ^ (3/2 : ℝ) / 12)
        (r * Real.sqrt (1+4*r^2)) r := by
    have hbase : HasDerivAt (fun t : ℝ => 1 + 4*t^2) (8*r) r := by
      convert (((hasDerivAt_pow 2 r).const_mul 4).const_add 1) using 1 <;> push_cast <;> ring
    convert (hbase.rpow_const (p := (3/2 : ℝ)) (Or.inl (by positivity))).div_const 12 using 1
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ)-1 = 1/2 by norm_num]
    ring
  rw [show (∫ r : ℝ in (0 : ℝ)..R, r * Real.sqrt (1+4*r^2)) =
      ((1+4*R^2) ^ (3/2 : ℝ) - 1)/12 by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hanti r)
      ((by fun_prop : Continuous (fun r : ℝ => r * Real.sqrt (1+4*r^2))).intervalIntegrable _ _)]
    simp
    ring]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem paraboloid_upward_flux (R : ℝ) (hR : 0 ≤ R) :
    surfaceFlux (roundDisk R) paraboloid paraboloidU paraboloidV (fun _ => ![0,0,1]) =
      Real.pi * R^2 := by
  unfold surfaceFlux
  have h (p : ℝ × ℝ) :
      (∑ i, (![0,0,1] : Fin 3 → ℝ) i * crossProduct (paraboloidU p) (paraboloidV p) i) = 1 := by
    rw [paraboloid_cross, Fin.sum_univ_three]
    change 0 * (-2*p.1) + 0 * (-2*p.2) + 1 * (1:ℝ) = 1
    ring
  simp_rw [h]
  rw [roundDisk_polar R hR (fun _ => 1) continuous_const.continuousOn]
  simpa only [mul_one] using polar_disk_area R

end Ch13
