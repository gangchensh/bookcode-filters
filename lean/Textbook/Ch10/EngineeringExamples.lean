import Textbook.Ch10.Audit
import Textbook.Ch09.Applications

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem exponential_first_moment_truncation (T : ℝ) :
    (∫ x in (0:ℝ)..T, x * Real.exp (-x)) = 1-(T+1)*Real.exp (-T) := by
  have hd (t : ℝ) : HasDerivAt (fun x => -(x+1)*Real.exp (-x)) (t*Real.exp (-t)) t := by
    have ha := ((hasDerivAt_id' t).add_const 1).neg
    have hb := (hasDerivAt_id' t).neg.exp
    convert ha.mul hb using 1
    dsimp
    ring
  have hi : IntervalIntegrable (fun x : ℝ => x*Real.exp (-x)) volume 0 T :=
    (by fun_prop : Continuous (fun x : ℝ => x*Real.exp (-x))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  simp
  ring

theorem exponential_first_moment :
    ImproperRight (fun x => x*Real.exp (-x)) 0 1 := by
  have he : Tendsto (fun T : ℝ => T*Real.exp (-T)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1:ℝ) zero_lt_one
  have hs : Tendsto (fun T : ℝ => (T+1)*Real.exp (-T)) atTop (𝓝 0) := by
    simpa only [add_mul,one_mul,add_zero] using he.add Real.tendsto_exp_neg_atTop_nhds_zero
  refine ⟨fun T _ => (by fun_prop : Continuous (fun x : ℝ => x*Real.exp (-x))).intervalIntegrable _ _,?_⟩
  simp_rw [exponential_first_moment_truncation]
  simpa using hs.const_sub (1:ℝ)

theorem centroid_inside {ρ : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hρ : IntervalIntegrable ρ volume 0 L)
    (hxρ : IntervalIntegrable (fun x => x*ρ x) volume 0 L)
    (hn : ∀ x ∈ Icc 0 L, 0 ≤ ρ x) (hm : 0 < mass ρ 0 L) :
    0 ≤ firstMoment ρ 0 L / mass ρ 0 L ∧ firstMoment ρ 0 L / mass ρ 0 L ≤ L := by
  have hq : 0 ≤ ∫ x in (0:ℝ)..L, x*ρ x :=
    intervalIntegral.integral_nonneg hL.le (fun x hx => mul_nonneg hx.1 (hn x hx))
  have hQ := intervalIntegral.integral_mono_on hL.le hxρ (hρ.const_mul L)
    (fun x hx => mul_le_mul_of_nonneg_right hx.2 (hn x hx))
  rw [intervalIntegral.integral_const_mul] at hQ
  exact ⟨div_nonneg hq hm.le,(div_le_iff₀ hm).2 hQ⟩

end Ch10
