import Textbook.Ch11.Audit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace Ch11

open Filter
open scoped Topology

private theorem sine_polynomial (m : ℕ) (x : ℝ) :
    Ch08.bookTaylor Real.sin (2*m) 0 x =
      ∑ k ∈ Finset.range m, (-1:ℝ)^k*x^(2*k+1)/((2*k+1).factorial:ℝ) := by
  induction m with
  | zero => simp [Ch08.bookTaylor]
  | succ m ih =>
    unfold Ch08.bookTaylor at ih ⊢
    rw [show 2*(m+1)+1 = (2*m+1)+1+1 by omega,
      Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ]
    rw [show 2*m+1+1 = 2*(m+1) by omega,Real.iteratedDeriv_even_sin,Real.iteratedDeriv_odd_sin]
    simp [Pi.mul_apply,mul_comm,mul_left_comm,mul_assoc,div_eq_mul_inv]

theorem sine_taylor_bound (m : ℕ) (x : ℝ) :
    |Real.sin x - (∑ k ∈ Finset.range m, (-1:ℝ)^k*x^(2*k+1)/((2*k+1).factorial:ℝ))| ≤
      |x|^(2*m+1)/((2*m+1).factorial:ℝ) := by
  have h := Ch08.book_lagrange_bound (f := Real.sin) (n := 2*m) (a := 0) (x := x)
    (fun _ _ => Real.contDiff_sin.contDiffAt) (fun t _ => Real.abs_iteratedDeriv_sin_le_one _ t)
  rw [sine_polynomial] at h
  simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h

theorem sine_small_interval {x : ℝ} (hx : |x| ≤ 1/10) :
    |Real.sin x-(x-x^3/6+x^5/120)| < 2/100000000000 := by
  have h := sine_taylor_bound 3 x
  have he : (∑ k ∈ Finset.range 3, (-1:ℝ)^k*x^(2*k+1)/((2*k+1).factorial:ℝ)) =
      x-x^3/6+x^5/120 := by
    norm_num [Finset.sum_range_succ,Nat.factorial]
    ring
  rw [he] at h
  refine h.trans_lt ((div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg x) hx 7) (by positivity)).trans_lt ?_)
  norm_num [Nat.factorial]

theorem sine_series (x : ℝ) :
    SeriesHasSum (fun n : ℕ => (-1:ℝ)^n*x^(2*n+1)/((2*n+1).factorial:ℝ)) (Real.sin x) :=
  (Real.hasSum_sin x).tendsto_sum_nat

end Ch11
