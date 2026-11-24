import Textbook.Ch11.ApproximationExamples
import Mathlib.Analysis.Complex.AbelLimit

namespace Ch11

open Filter Set
open scoped Topology

theorem abel_endpoint {c : ℕ → ℝ} {a R L : ℝ} (hR : 0 < R)
    (hL : SeriesHasSum (fun n => c n * R^n) L) :
    Tendsto (fun x => ∑' n, powerSeriesTerm c a x n) (𝓝[<] (a+R)) (𝓝 L) := by
  have hm : Tendsto (fun x : ℝ => (x-a)/R) (𝓝[<] (a+R)) (𝓝[<] (1:ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : Continuous (fun x : ℝ => (x-a)/R) := by fun_prop
      have ht := (hc.continuousAt (x := a+R)).continuousWithinAt (s := Iio (a+R))
      change Tendsto _ _ (𝓝 ((a+R-a)/R)) at ht
      rwa [show a+R-a = R by ring, div_self hR.ne'] at ht
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change (x-a)/R < 1
      exact (div_lt_one hR).2 (by linarith [show x < a+R from hx])
  have ht := (Real.tendsto_tsum_powerSeries_nhdsWithin_lt hL).comp hm
  apply ht.congr
  intro x
  change (∑' n, c n * R^n * ((x-a)/R)^n) = ∑' n, powerSeriesTerm c a x n
  congr 1
  funext n
  rw [powerSeriesTerm, mul_assoc, ← mul_pow]
  congr 2
  field_simp

theorem geometric_half_precision :
    SeriesHasSum (fun n => (1/2:ℝ)^n) 2 ∧
    (∀ N, seriesRemainder (fun n => (1/2:ℝ)^n) 2 N = 2*(1/2:ℝ)^N) ∧
    |seriesRemainder (fun n => (1/2:ℝ)^n) 2 21| < (1/1000000:ℝ) := by
  have h := geometric_sum_and_tail (q := 1/2) (by norm_num)
  have hl : (1:ℝ)/(1-1/2) = 2 := by norm_num
  rw [hl] at h
  have ht (N : ℕ) := (h.2 N).1
  refine ⟨h.1,fun N => ?_,?_⟩
  · rw [ht]
    ring
  · rw [ht]
    norm_num

theorem alternating_harmonic_precision :
    |seriesRemainder (fun n : ℕ => (-1:ℝ)^n/(n+1:ℝ)) (Real.log 2) 1000000| ≤
      (1/1000000:ℝ) := by
  exact (alternating_harmonic.2.2 1000000).trans (by norm_num)

theorem weighted_geometric {x : ℝ} (hx : |x| < 1) :
    SeriesHasSum (fun n : ℕ => (n+1:ℝ)*x^n) (1/(1-x)^2) := by
  have hn : ‖x‖ < 1 := by simpa [Real.norm_eq_abs] using hx
  have hg := hasSum_geometric_of_norm_lt_one hn
  have hw := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h := hw.add hg
  have he : x/(1-x)^2+(1-x)⁻¹ = 1/(1-x)^2 := by
    have hne : 1-x ≠ 0 := (sub_pos.mpr ((le_abs_self x).trans_lt hx)).ne'
    field_simp
    <;> ring
  rw [he] at h
  have hf : (fun n : ℕ => (n:ℝ)*x^n + x^n) = fun n : ℕ => (n+1:ℝ)*x^n := by
    funext n
    ring
  rw [hf] at h
  exact h.tendsto_sum_nat

theorem uniform_derivative_counterexample :
    TendstoUniformlyOn (fun (N : ℕ) (x : ℝ) => Real.sin ((N:ℝ)*x)/(N:ℝ))
      (fun _ => 0) atTop (Icc (-1:ℝ) 1) ∧
    (∀ (N : ℕ), 1 ≤ N → ∀ x,
      HasDerivAt (fun t : ℝ => Real.sin ((N:ℝ)*t)/(N:ℝ)) (Real.cos ((N:ℝ)*x)) x) ∧
    HasDerivAt (fun _ : ℝ => (0:ℝ)) 0 0 := by
  refine ⟨?_,?_,hasDerivAt_const 0 0⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have ht : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (Iio_mem_nhds hε),eventually_ge_atTop (1:ℕ)] with n hlt hn x _
    have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [Real.dist_eq,abs_sub_comm,sub_zero,abs_div,abs_of_pos hn']
    exact (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hn'.le).trans_lt (by simpa [one_div] using hlt)
  · intro n hn x
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h := ((((hasDerivAt_id x).const_mul (n:ℝ)).sin).div_const (n:ℝ))
    simpa [id_eq, mul_div_cancel_right₀ _ hn'] using h

end Ch11
