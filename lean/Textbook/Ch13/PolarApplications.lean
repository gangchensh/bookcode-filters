import Textbook.Ch13.Applications
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace Ch13

open MeasureTheory Set
open scoped Interval

def roundDisk (R : ℝ) : Set (ℝ × ℝ) := {p | p.1^2 + p.2^2 ≤ R^2}

theorem roundDisk_measurable (R : ℝ) : MeasurableSet (roundDisk R) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem polar_radius_sq (r θ : ℝ) :
    (r * Real.cos θ)^2 + (r * Real.sin θ)^2 = r^2 := by
  nlinarith [congrArg (fun x : ℝ => r^2 * x) (Real.sin_sq_add_cos_sq θ)]

/-- Convert the polar chart to an iterated integral, then shift the full angular period. -/
theorem roundDisk_polar (R : ℝ) (hR : 0 ≤ R) (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (roundDisk R)) :
    (∫ p in roundDisk R, f p) =
      ∫ θ : ℝ in (0 : ℝ)..(2*Real.pi),
        ∫ r : ℝ in (0 : ℝ)..R, r * f (r * Real.cos θ, r * Real.sin θ) := by
  let g (p : ℝ × ℝ) := p.2 * f (p.2 * Real.cos p.1, p.2 * Real.sin p.1)
  have hg : IntegrableOn g (Icc (-Real.pi) Real.pi ×ˢ Icc 0 R) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply continuous_snd.continuousOn.mul
    apply hf.comp (by fun_prop)
    intro p hp
    change (p.2 * Real.cos p.1)^2 + (p.2 * Real.sin p.1)^2 ≤ R^2
    rw [polar_radius_sq]
    exact (sq_le_sq₀ hp.2.1 hR).2 hp.2.2
  have hprod : polarCoord.target ∩ {p : ℝ × ℝ | p.1 ≤ R} =
      Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    change ((0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi) ∧ p.1 ≤ R) ↔
      (0 < p.1 ∧ p.1 ≤ R) ∧ (-Real.pi < p.2 ∧ p.2 < Real.pi)
    tauto
  have hperiod : Function.Periodic (fun θ =>
      ∫ r : ℝ in (0 : ℝ)..R, g (θ,r)) (2 * Real.pi) := by
    intro θ
    simp [g, Real.sin_add_two_pi, Real.cos_add_two_pi]
  rw [roundDisk, disk_region_polar R hR]
  change (∫ p in polarCoord.target,
      ({p : ℝ × ℝ | p.1 ≤ R}).indicator (fun p => g p.swap) p) = _
  rw [setIntegral_indicator (isClosed_le continuous_fst continuous_const).measurableSet,
    hprod]
  rw [Measure.volume_eq_prod, setIntegral_prod_swap]
  rw [← Measure.volume_eq_prod]
  have hg' : IntegrableOn g (Ioo (-Real.pi) Real.pi ×ˢ Ioc 0 R) :=
    hg.mono_set (prod_mono Ioo_subset_Icc_self Ioc_subset_Icc_self)
  rw [Measure.volume_eq_prod, setIntegral_prod g hg']
  simp only [← intervalIntegral.integral_of_le hR,
    ← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  simpa [g, show -Real.pi + 2 * Real.pi = Real.pi by ring] using
    hperiod.intervalIntegral_add_eq (-Real.pi) 0

end Ch13
