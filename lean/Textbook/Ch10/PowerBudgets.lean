import Textbook.Ch10.PowerCriteria

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem power_tail_cutoff {p T ε : ℝ} (hp : 1 < p) (hε : 0 < ε)
    (hT : max 1 ((1/((p-1)*ε)) ^ (1/(p-1))) ≤ T) :
    1/(p-1) - (∫ x in (1:ℝ)..T, x ^ (-p)) ≤ ε := by
  have hT₁ := (le_max_left _ _).trans hT
  rw [power_tail_identity hp hT₁]
  have hq := sub_pos.mpr hp
  have hT₀ : 0 < T := zero_lt_one.trans_le hT₁
  have hh : 1/((p-1)*ε) ≤ T ^ (p-1) := by
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) hT₀.le hq).1
    simpa only [one_div] using (le_max_right _ _).trans hT
  rw [show 1-p = -(p-1) by ring,Real.rpow_neg hT₀.le,div_le_iff₀ hq,
    ← one_div,div_le_iff₀ (Real.rpow_pos_of_pos hT₀ _)]
  have he := (div_le_iff₀ (mul_pos hq hε)).1 hh
  nlinarith

theorem origin_power_tail_cutoff {p c ε : ℝ} (hp : p < 1) (hε : 0 < ε)
    (hc : 0 < c) (hcut : c ≤ min 1 ((ε*(1-p)) ^ (1/(1-p)))) :
    1/(1-p) - (∫ x in c..(1:ℝ), x ^ (-p)) ≤ ε := by
  rw [origin_power_tail_identity hp hc,div_le_iff₀ (sub_pos.mpr hp)]
  apply (Real.le_rpow_inv_iff_of_pos hc.le (by positivity) (sub_pos.mpr hp)).1
  simpa only [one_div] using hcut.trans (min_le_right _ _)

theorem harmonic_zero_value_irrelevant (v : ℝ) :
    Tendsto (fun c : ℝ => ∫ x in c..(1:ℝ),
      Function.update (fun y : ℝ => 1/y) 0 v x) (𝓝[>] 0) atTop := by
  apply (power_diverges_at_zero (p := 1) le_rfl).congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (min c 1) (max c 1) := hx
  have hp := (lt_min hc zero_lt_one).trans_le hx'.1
  rw [Function.update_of_ne hp.ne']
  change x ^ (-(1:ℝ)) = 1/x
  rw [Real.rpow_neg_one,one_div]

theorem square_and_fourth_power_cutoff {T : ℝ} :
    (1000 ≤ T → 1 - (∫ x in (1:ℝ)..T, x ^ (-(2:ℝ))) ≤ 1/1000) ∧
    (10 ≤ T → 1/3 - (∫ x in (1:ℝ)..T, x ^ (-(4:ℝ))) ≤ 1/1000) := by
  constructor
  · intro hT
    have he := power_tail_identity (by norm_num : (1:ℝ) < 2) (by linarith : 1 ≤ T)
    norm_num [Real.rpow_neg_one] at he
    norm_num
    have hb := (inv_le_inv₀ (by positivity : 0 < T) (by norm_num : 0 < (1000:ℝ))).2 hT
    linarith
  · intro hT
    have he := power_tail_identity (by norm_num : (1:ℝ) < 4) (by linarith : 1 ≤ T)
    norm_num at he
    norm_num
    have hpow : (10:ℝ)^3 ≤ T^3 := pow_le_pow_left₀ (by norm_num) hT 3
    have hb := (inv_le_inv₀ (by positivity : 0 < T^3) (by norm_num : 0 < (10:ℝ)^3)).2 hpow
    norm_num at hb
    linarith

theorem origin_half_quarter_resolution {c : ℝ} (hc : 0 < c) :
    (c ≤ 1/40000 → 1/(1-(1/2:ℝ))-(∫ x in c..(1:ℝ), x ^ (-(1/2:ℝ))) ≤ 1/100) ∧
    (c ≤ 1/25600000000 → 1/(1-(3/4:ℝ))-(∫ x in c..(1:ℝ), x ^ (-(3/4:ℝ))) ≤ 1/100) := by
  constructor
  · intro h
    rw [origin_power_tail_identity (by norm_num) hc,div_le_iff₀ (by norm_num)]
    norm_num
    have hp : c ^ (1/2:ℝ) ≤ (1/200:ℝ) := by
      have he := Real.rpow_le_rpow hc.le h (by norm_num : 0 ≤ (1/2:ℝ))
      rwa [show (1/40000:ℝ) = (1/200:ℝ) ^ (2:ℝ) by rw [Real.rpow_two]; norm_num,
        ← Real.rpow_mul (by norm_num), show (2:ℝ)*(1/2)=1 by norm_num, Real.rpow_one] at he
    exact hp
  · intro h
    rw [origin_power_tail_identity (by norm_num) hc,div_le_iff₀ (by norm_num)]
    norm_num
    have hp : c ^ (1/4:ℝ) ≤ (1/400:ℝ) := by
      have he := Real.rpow_le_rpow hc.le h (by norm_num : 0 ≤ (1/4:ℝ))
      rwa [show (1/25600000000:ℝ) = (1/400:ℝ) ^ (4:ℝ) by rw [Real.rpow_ofNat]; norm_num,
        ← Real.rpow_mul (by norm_num), show (4:ℝ)*(1/4)=1 by norm_num, Real.rpow_one] at he
    exact hp

theorem inverse_square_density_infinite_mean :
    ImproperRight (fun x : ℝ => 1/x^2) 1 1 ∧
      Tendsto (fun T : ℝ => ∫ x in (1:ℝ)..T, x*(1/x^2)) atTop atTop := by
  constructor
  · simpa [one_div] using power_two_and_half.1
  · apply (power_diverges_at_infinity (p := 1) le_rfl).congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hT]
    intro x hx
    have hne := (zero_lt_one.trans_le hx.1).ne'
    change x ^ (-(1:ℝ)) = x*(1/x^2)
    rw [Real.rpow_neg_one]
    field_simp

end Ch10
