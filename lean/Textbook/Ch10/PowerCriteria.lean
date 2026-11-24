import Textbook.Ch10.Audit

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem power_diverges_at_infinity {p : ℝ} (hp : p ≤ 1) :
    Tendsto (fun T : ℝ => ∫ x in (1 : ℝ)..T, x ^ (-p)) atTop atTop := by
  rcases lt_or_eq_of_le hp with h | rfl
  · have hpow := tendsto_rpow_atTop (sub_pos.mpr h)
    have hlim := (tendsto_atTop_add_const_right _ (-1 : ℝ) hpow).atTop_div_const
      (sub_pos.mpr h)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [power_truncation h.ne hT]
    rfl
  · apply Real.tendsto_log_atTop.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simp_rw [Real.rpow_neg_one]
    rw [integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hT), div_one]

theorem power_diverges_at_zero {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), x ^ (-p)) (𝓝[>] 0) atTop := by
  rcases lt_or_eq_of_le hp with h | h
  · have hpow := tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr h)
    have hlim := (tendsto_atTop_add_const_right _ (-1 : ℝ) hpow).atTop_div_const
      (sub_pos.mpr h)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [origin_power_truncation h.ne' hc]
    have hd : 1-p = -(p-1) := by ring
    rw [hd, div_neg]
    ring
  · subst p
    apply (tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero).congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    simp_rw [Real.rpow_neg_one]
    rw [integral_inv_of_pos hc zero_lt_one, one_div, Real.log_inv]

theorem power_infinity_criterion (p : ℝ) :
    (∃ I, ImproperRight (fun x : ℝ => x ^ (-p)) 1 I) ↔ 1 < p := by
  constructor
  · rintro ⟨I,hI⟩
    by_contra! hp
    exact not_tendsto_nhds_of_tendsto_atTop (power_diverges_at_infinity hp) I hI.2
  · intro hp
    exact ⟨_,power_improper_converges hp⟩

theorem power_origin_criterion (p : ℝ) :
    (∃ I, ImproperEndpointLeft (fun x : ℝ => x ^ (-p)) 0 1 I) ↔ p < 1 := by
  constructor
  · rintro ⟨I,hI⟩
    by_contra! hp
    exact not_tendsto_nhds_of_tendsto_atTop (power_diverges_at_zero hp) I hI.2
  · intro hp
    exact ⟨_,origin_power_converges hp⟩

theorem power_cannot_converge_at_both (p : ℝ) :
    ¬ ((∃ I, ImproperRight (fun x : ℝ => x ^ (-p)) 1 I) ∧
      (∃ J, ImproperEndpointLeft (fun x : ℝ => x ^ (-p)) 0 1 J)) := by
  rw [power_infinity_criterion,power_origin_criterion]
  exact fun h => (lt_asymm h.1 h.2)

theorem power_two_and_half :
    ImproperRight (fun x : ℝ => x ^ (-(2 : ℝ))) 1 1 ∧
      Tendsto (fun c : ℝ => ∫ x in c..(1 : ℝ), x ^ (-(2 : ℝ))) (𝓝[>] 0) atTop ∧
      ImproperEndpointLeft (fun x : ℝ => x ^ (-(1/2 : ℝ))) 0 1 2 ∧
      Tendsto (fun T : ℝ => ∫ x in (1 : ℝ)..T, x ^ (-(1/2 : ℝ))) atTop atTop := by
  exact ⟨by convert power_improper_converges (by norm_num : (1 : ℝ) < 2) using 1 <;> norm_num,
    power_diverges_at_zero (by norm_num),
    by convert origin_power_converges (by norm_num : (1/2 : ℝ) < 1) using 1 <;> norm_num,
    power_diverges_at_infinity (by norm_num)⟩

end Ch10
