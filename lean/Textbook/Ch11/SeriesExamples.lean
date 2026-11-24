import Textbook.Ch11.Audit
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace Ch11

open Filter Set
open scoped Topology

theorem geometric_nonconvergence {q : ℝ} (hq : 1 ≤ |q|) :
    ¬ SeriesConverges (fun n => q^n) := by
  rintro ⟨s,hs⟩
  have h := (term_tendsto_zero hs).abs
  have h' : ∀ᶠ n in atTop, |q^n| < (1:ℝ) :=
    h.eventually (Iio_mem_nhds (by norm_num : |(0:ℝ)| < 1))
  obtain ⟨n,hn⟩ := h'.exists
  rw [abs_pow] at hn
  exact (not_lt_of_ge (one_le_pow₀ hq)) hn

theorem geometric_one_partial_sum (N : ℕ) :
    partialSum (fun n => (1:ℝ)^n) N = N := by simp [partialSum]

theorem rational_series_comparison :
    SeriesConverges (fun n => 1/(((n+1:ℕ):ℝ)^2+3*(n+1:ℝ))) := by
  have hs := (p_series_criterion 2).2 (by norm_num)
  apply (positive_series_summable (fun _ => by positivity)).2
  apply Summable.of_nonneg_of_le (fun _ => by positivity) ?_
    ((positive_series_summable (fun _ => by positivity)).1 hs)
  intro n
  push_cast
  rw [Real.rpow_two]
  exact one_div_le_one_div_of_le (by positivity) (by linarith [show (0:ℝ) ≤ n by positivity])

theorem oscillating_series_absolute :
    AbsolutelyConvergent (fun n => Real.sin (((n+1:ℕ):ℝ)^2)/((n+1:ℕ):ℝ)^2) := by
  have hs := (p_series_criterion 2).2 (by norm_num)
  apply (positive_series_summable (fun _ => abs_nonneg _)).2
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_
    ((positive_series_summable (fun _ => by positivity)).1 hs)
  intro n
  rw [Real.rpow_two, abs_div, abs_of_nonneg (sq_nonneg (((n+1:ℕ):ℝ)))]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (sq_nonneg _)

theorem ratio_tail_bound {a : ℕ → ℝ} {q : ℝ} {N₀ : ℕ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (h : ∀ n ≥ N₀, |a (n+1)| ≤ q * |a n|) :
    AbsolutelyConvergent a ∧ ∀ N ≥ N₀,
      (∑' j : ℕ, |a (N+j)|) ≤ |a N|/(1-q) := by
  have hg := hasSum_geometric_of_norm_lt_one (show ‖q‖ < 1 by
    simpa [Real.norm_eq_abs,abs_of_nonneg hq₀] using hq)
  have hb (N : ℕ) (hN : N₀ ≤ N) (j : ℕ) : |a (N+j)| ≤ |a N| * q^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        |a (N+(j+1))| ≤ q * |a (N+j)| := h _ (hN.trans (Nat.le_add_right _ _))
        _ ≤ q * (|a N| * q^j) := mul_le_mul_of_nonneg_left ih hq₀
        _ = _ := by rw [pow_succ]; ring
  have hs (N : ℕ) (hN : N₀ ≤ N) : Summable (fun j => |a (N+j)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hb N hN) (hg.summable.mul_left _)
  refine ⟨(positive_series_summable (fun _ => abs_nonneg _)).2
    ((summable_nat_add_iff N₀).1 (by simpa [Nat.add_comm] using hs N₀ le_rfl)),?_⟩
  intro N hN
  have hle := (hs N hN).tsum_le_tsum (hb N hN) (hg.summable.mul_left (|a N|))
  simpa [hg.summable.tsum_mul_left, hg.tsum_eq, div_eq_mul_inv] using hle

theorem cauchy_product {a b : ℕ → ℝ} {A B : ℝ}
    (ha : AbsolutelyConvergent a) (hb : AbsolutelyConvergent b)
    (hA : SeriesHasSum a A) (hB : SeriesHasSum b B) :
    AbsolutelyConvergent (fun n => ∑ k ∈ Finset.range (n+1), a k * b (n-k)) ∧
    SeriesHasSum (fun n => ∑ k ∈ Finset.range (n+1), a k * b (n-k)) (A*B) := by
  have ha' : Summable (fun n => ‖a n‖) := by
    simpa [Real.norm_eq_abs] using (positive_series_summable (fun n => abs_nonneg (a n))).1 ha
  have hb' : Summable (fun n => ‖b n‖) := by
    simpa [Real.norm_eq_abs] using (positive_series_summable (fun n => abs_nonneg (b n))).1 hb
  have hsa : Summable a := ha'.of_norm
  have hsb : Summable b := hb'.of_norm
  have hta : (∑' n, a n) = A := tendsto_nhds_unique hsa.hasSum.tendsto_sum_nat hA
  have htb : (∑' n, b n) = B := tendsto_nhds_unique hsb.hasSum.tendsto_sum_nat hB
  have hc : Summable (fun n => |∑ k ∈ Finset.range (n+1), a k * b (n-k)|) := by
    simpa only [Real.norm_eq_abs] using summable_norm_sum_mul_range_of_summable_norm ha' hb'
  refine ⟨(positive_series_summable (fun _ => abs_nonneg _)).2 hc,?_⟩
  have he := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha' hb'
  rw [hta,htb] at he
  rw [he]
  exact (Summable.of_abs hc).hasSum.tendsto_sum_nat

end Ch11
