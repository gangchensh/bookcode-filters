import Textbook.Ch10.PowerCriteria

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

private theorem rpow_half_inverse (x : ℝ) (hx : 0 < x) :
    x ^ (-(1/2:ℝ)) = 1/Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hx.le]
  simp [one_div]

theorem square_root_singularity :
    ImproperEndpointLeft (fun x => 1/Real.sqrt x) 0 1 2 := by
  have hp := power_two_and_half.2.2.1
  refine ⟨fun c hc hc₁ => ?_,?_⟩
  · apply ContinuousOn.intervalIntegrable_of_Icc hc₁
    apply continuousOn_const.div Real.continuous_sqrt.continuousOn
    intro x hx
    exact (Real.sqrt_pos_of_pos (hc.trans_le hx.1)).ne'
  · apply hp.2.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (min c 1) (max c 1) := hx
    exact rpow_half_inverse x ((lt_min hc zero_lt_one).trans_le hx'.1)

theorem square_root_truncation {c : ℝ} (hc : 0 < c) :
    (∫ x in c..(1:ℝ), 1/Real.sqrt x) = 2-2*Real.sqrt c := by
  have h : (∫ x in c..(1:ℝ), 1/Real.sqrt x) =
      ∫ x in c..(1:ℝ), x ^ (-(1/2:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (min c 1) (max c 1) := hx
    have hx₀ := (lt_min hc zero_lt_one).trans_le hx'.1
    exact (rpow_half_inverse x hx₀).symm
  rw [h,origin_power_truncation (by norm_num) hc, Real.sqrt_eq_rpow]
  norm_num <;> ring

theorem square_root_tail_cutoff {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hcut : c ≤ ε^2/4) :
    2 - (∫ x in c..(1:ℝ), 1/Real.sqrt x) ≤ ε := by
  rw [square_root_truncation hc]
  have h : Real.sqrt c ≤ ε/2 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> nlinarith
  linarith

theorem square_change_truncation {c : ℝ} (hc : 0 < c) (hc₁ : c < 1) :
    (∫ x in c..(1:ℝ), 1/Real.sqrt x) =
      ∫ t in Real.sqrt c..(1:ℝ), (2*t)/t := by
  have hroot : Real.sqrt c ≤ 1 := (Real.sqrt_le_iff).2 ⟨zero_le_one,by simpa using hc₁.le⟩
  have he : (∫ t in Real.sqrt c..(1:ℝ), (2*t)/t) = ∫ _ in Real.sqrt c..(1:ℝ), (2:ℝ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hroot]
    intro t ht
    exact mul_div_cancel_right₀ 2 (((Real.sqrt_pos_of_pos hc).trans_le ht.1).ne')
  rw [square_root_truncation hc,he,Ch09.integral_constant]
  ring

end Ch10
