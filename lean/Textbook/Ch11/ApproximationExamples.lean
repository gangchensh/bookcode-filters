import Textbook.Ch11.Audit
import Mathlib.Analysis.Complex.AbelLimit

namespace Ch11

open Filter Set
open scoped Topology

theorem logarithm_series {x : ℝ} (hx : |x| < 1) :
    SeriesHasSum (fun n : ℕ => x^(n+1)/(n+1:ℝ)) (-Real.log (1-x)) :=
  (Real.hasSum_pow_div_log_of_abs_lt_one hx).tendsto_sum_nat

theorem alternating_harmonic :
    SeriesHasSum (fun n : ℕ => (-1:ℝ)^n/(n+1:ℝ)) (Real.log 2) ∧
    ConditionallyConvergent (fun n : ℕ => (-1:ℝ)^n/(n+1:ℝ)) ∧
    ∀ N, |seriesRemainder (fun n : ℕ => (-1:ℝ)^n/(n+1:ℝ)) (Real.log 2) N|
      ≤ 1/(N+1:ℝ) := by
  let b := fun n : ℕ => 1/(n+1:ℝ)
  let d := fun n : ℕ => (-1:ℝ)^n/(n+1:ℝ)
  have hm : Antitone b := fun n m hnm => one_div_le_one_div_of_le (by positivity)
    (add_le_add_left (by exact_mod_cast hnm) 1)
  have hz : Tendsto b atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)
    simpa [b,one_div] using ht
  have he : (fun n => (-1:ℝ)^n*b n) = d := by funext n; simp [b,d,div_eq_mul_inv]
  obtain ⟨s,hs,hbound⟩ := alternating_criterion (b := b) (fun _ => by dsimp [b]; positivity) hm hz
  rw [he] at hs hbound
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hs
  have ht : Tendsto (fun t : ℝ => t) (𝓝[<] (1:ℝ)) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hprod := ht.mul hab
  have hlog : Tendsto (fun t : ℝ => Real.log (1+t)) (𝓝[<] (1:ℝ)) (𝓝 (Real.log 2)) := by
    have hl : ContinuousAt (fun t : ℝ => Real.log (1+t)) 1 := by
      apply ContinuousAt.log (by fun_prop)
      norm_num
    have h := hl.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1:ℝ)))
    change Tendsto _ _ (𝓝 (Real.log (1+1))) at h
    norm_num at h ⊢
    exact h
  have hprod' : Tendsto (fun t : ℝ => Real.log (1+t)) (𝓝[<] (1:ℝ)) (𝓝 s) := by
    rw [one_mul] at hprod
    apply hprod.congr'
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0:ℝ) < 1)] with t ht
    have h := Real.hasSum_pow_div_log_of_abs_lt_one
      (show |-t| < 1 by rw [abs_neg,abs_of_nonneg ht.1.le]; exact ht.2)
    have hf : (fun n : ℕ => (-1:ℝ) * ((-t)^(n+1)/(n+1:ℝ))) =
        fun n : ℕ => t*(d n*t^n) := by
      funext n
      dsimp [d]
      rw [show -t = (-1:ℝ)*t by ring,mul_pow,pow_succ (-1:ℝ),pow_succ t]
      ring
    have hh := h.mul_left (-1:ℝ)
    rw [hf] at hh
    rw [← tsum_mul_left, hh.tsum_eq]
    simp
  have hL : s = Real.log 2 := tendsto_nhds_unique hprod' hlog
  subst s
  have hn : ¬ AbsolutelyConvergent d := by
    have hh : (fun n => |d n|) = b := by
      funext n
      dsimp [d,b]
      rw [abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1)]
    unfold AbsolutelyConvergent
    rw [hh]
    simpa [b,Nat.cast_add] using harmonic_counterexample.2
  exact ⟨hs,⟨⟨_,hs⟩,hn⟩,fun N => (hbound N).1⟩

theorem square_denominator_endpoint :
    TendstoUniformlyOn
      (fun N x => partialSum (fun n : ℕ => x^(n+1)/(n+1:ℝ)^2) N)
      (fun x => ∑' n : ℕ, x^(n+1)/(n+1:ℝ)^2) atTop (Icc (-1:ℝ) 1) ∧
    ¬ SeriesConverges (fun n : ℕ => 1/(n+1:ℝ)) := by
  have hm : SeriesConverges (fun n : ℕ => 1/(n+1:ℝ)^2) := by
    simpa only [Nat.cast_add,Nat.cast_one,Real.rpow_two] using (p_series_criterion 2).2 (by norm_num)
  refine ⟨(weierstrass_test (M := fun n : ℕ => 1/(n+1:ℝ)^2) (fun _ => by positivity) hm ?_).2,?_⟩
  · intro n x hx
    rw [abs_div,abs_pow,abs_of_nonneg (sq_nonneg (n+1:ℝ))]
    exact div_le_div_of_nonneg_right
      (by simpa using pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) (n+1)) (sq_nonneg _)
  · simpa [Nat.cast_add] using harmonic_counterexample.2

theorem exponential_rational_certificate :
    0 ≤ Real.exp (1/10) - (265241/240000 : ℝ) ∧
    Real.exp (1/10) - (265241/240000 : ℝ) ≤ 1/10800000 := by
  let x : ℝ := 1/10
  let a := fun n : ℕ => x^n/(n.factorial:ℝ)
  have hs := Real.summable_pow_div_factorial x
  have hval : (∑' n, a n) = Real.exp x :=
    tendsto_nhds_unique hs.hasSum.tendsto_sum_nat (exp_series x)
  have hbound (n : ℕ) : a n ≤ x^n := by
    apply div_le_self (by dsimp [x]; positivity)
    exact_mod_cast Nat.factorial_pos n
  have hg := hasSum_geometric_of_norm_lt_one (show ‖x‖ < 1 by norm_num [x])
  have hu := hs.tsum_le_tsum hbound hg.summable
  rw [hval,hg.tsum_eq] at hu
  have hupper : Real.exp x ≤ 10/9 := by
    calc
      _ ≤ (1-x)⁻¹ := hu
      _ = _ := by norm_num [x]
  have hP : partialSum a 5 = (265241/240000:ℝ) := by
    norm_num [partialSum,a,x,Finset.sum_range_succ,Nat.factorial]
  have hl : partialSum a 5 ≤ Real.exp x := by
    rw [← hval]
    exact hs.sum_le_tsum _ (fun n _ => by dsimp [a,x]; positivity)
  have ht := exp_compact_remainder (x := x) (r := x)
    (by norm_num [x] : |x| ≤ x) 4
  change |Real.exp x - partialSum a 5| ≤ Real.exp x * x^5/(Nat.factorial 5:ℝ) at ht
  rw [abs_of_nonneg (sub_nonneg.mpr hl),hP] at ht
  rw [hP] at hl
  refine ⟨sub_nonneg.mpr hl,ht.trans ?_⟩
  calc
    _ ≤ (10/9:ℝ)*x^5/(Nat.factorial 5:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hupper (by norm_num [x])) (by positivity)
    _ = _ := by norm_num [x,Nat.factorial]

end Ch11
