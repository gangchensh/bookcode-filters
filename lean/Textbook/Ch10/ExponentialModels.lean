import Textbook.Ch10.EngineeringExamples
import Textbook.Ch09.Quadrature

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem exponential_density_truncation {k : ℝ} (hk : 0 < k) (T : ℝ) :
    (∫ x in (0:ℝ)..T, k*Real.exp (-k*x)) = 1-Real.exp (-k*T) := by
  rw [scaled_decay_truncation hk.ne',div_self hk.ne',one_mul]

theorem exponential_density_mean {k : ℝ} (hk : 0 < k) :
    ImproperRight (fun x => k*Real.exp (-k*x)) 0 1 ∧
    ImproperRight (fun x => x*(k*Real.exp (-k*x))) 0 (1/k) := by
  refine ⟨normalized_exponential hk,?_⟩
  have htr (T : ℝ) : (∫ x in (0:ℝ)..T, x*(k*Real.exp (-k*x))) =
      1/k-(T+1/k)*Real.exp (-k*T) := by
    have hd (t : ℝ) : HasDerivAt (fun x => -(x+1/k)*Real.exp (-k*x))
        (t*(k*Real.exp (-k*t))) t := by
      convert (((hasDerivAt_id' t).add_const (1/k)).neg).mul
        (((hasDerivAt_id' t).const_mul (-k)).exp) using 1
      dsimp
      field_simp
      <;> ring
    have hi : IntervalIntegrable (fun x : ℝ => x*(k*Real.exp (-k*x))) volume 0 T :=
      (by fun_prop : Continuous (fun x : ℝ => x*(k*Real.exp (-k*x)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
    simp
    ring
  have ht : Tendsto (fun T : ℝ => k*T) atTop atTop := tendsto_id.const_mul_atTop hk
  have he : Tendsto (fun T : ℝ => Real.exp (-k*T)) atTop (𝓝 0) := by
    have he' : Tendsto (fun T : ℝ => Real.exp (-(k * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
    simpa only [neg_mul] using he'
  have hpoly : Tendsto (fun T : ℝ => T*Real.exp (-k*T)) atTop (𝓝 0) := by
    simpa [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) k hk
  have hs : Tendsto (fun T : ℝ => (T+1/k)*Real.exp (-k*T)) atTop (𝓝 0) := by
    simpa only [add_mul,mul_zero,add_zero] using hpoly.add (he.const_mul (1/k))
  refine ⟨fun T _ => (by fun_prop : Continuous (fun x : ℝ => x*(k*Real.exp (-k*x)))).intervalIntegrable _ _,?_⟩
  simp_rw [htr]
  simpa using hs.const_sub (1/k)

theorem exponential_tagged_error_budget {T ε : ℝ} (hT : 0 < T)
    (P : Ch09.TaggedPartition 0 T) (htail : Real.exp (-T) ≤ ε/2)
    (hmesh : P.mesh ≤ ε/(2*T)) :
    |1 - P.riemannSum (fun x => Real.exp (-x))| ≤ ε := by
  have hLip (x : ℝ) (hx : x ∈ Icc 0 T) (y : ℝ) (hy : y ∈ Icc 0 T) :
      |Real.exp (-x)-Real.exp (-y)| ≤ 1*|x-y| := by
    have hd (z : ℝ) : HasDerivAt (fun w => Real.exp (-w)) (-Real.exp (-z)) z := by
      convert (hasDerivAt_id' z).neg.exp using 1 <;> simp
    have hh : LipschitzOnWith 1 (fun w : ℝ => Real.exp (-w)) (Icc 0 T) := by
      apply (convex_Icc (0:ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun z _ => (hd z).hasDerivWithinAt)
      intro z hz
      change ‖-Real.exp (-z)‖ ≤ (1:ℝ)
      rw [norm_neg,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      simpa using (Real.exp_le_exp.mpr (neg_nonpos.mpr hz.1))
    simpa [Real.dist_eq] using hh.dist_le_mul x hx y hy
  have hq := Ch09.lipschitz_tagged_sum_error zero_le_one (fun x => Real.exp (-x)) hLip P
  have ht := decay_tail_error T
  have h := abs_sub_le (1:ℝ) (∫ x in (0:ℝ)..T, Real.exp (-x)) (P.riemannSum fun x => Real.exp (-x))
  rw [abs_sub_comm (∫ x in (0:ℝ)..T, Real.exp (-x))] at h
  have hm := (le_div_iff₀ (by positivity : 0 < 2*T)).1 hmesh
  rw [ht] at h
  nlinarith

theorem energy_cutoff_iff {P α ε T : ℝ} (hP : 0 < P) (hα : 0 < α) (hε : 0 < ε) :
    |P/(2*α) - (∫ t in (0:ℝ)..T, P*Real.exp (-(2*α)*t))| ≤ ε ↔
      Real.log (P/(2*α*ε))/(2*α) ≤ T := by
  have hk : 0 < 2*α := by positivity
  have hP' : 0 < P/(2*α) := by positivity
  rw [scaled_decay_error hk hP.le]
  rw [mul_comm,← le_div_iff₀ hP',← Real.exp_log (div_pos hε hP'),Real.exp_le_exp,
    div_le_iff₀ hk]
  have he : ε/(P/(2*α)) = (P/(2*α*ε))⁻¹ := by field_simp
  rw [he,Real.log_inv]
  constructor <;> intro h <;> linarith

theorem uniform_energy_tail {P Pmax α αmin T : ℝ}
    (hP : 0 < P) (hPm : P ≤ Pmax) (hα : 0 < αmin) (hαm : αmin ≤ α) (hT : 0 ≤ T) :
    P/(2*α)*Real.exp (-(2*α)*T) ≤ Pmax/(2*αmin)*Real.exp (-(2*αmin)*T) := by
  have ha : 0 < α := hα.trans_le hαm
  have hb : 0 < Pmax := hP.trans_le hPm
  apply mul_le_mul
  · apply div_le_div₀ hb.le hPm (by positivity)
    linarith
  · apply Real.exp_le_exp.2
    nlinarith
  · positivity
  · positivity

end Ch10

