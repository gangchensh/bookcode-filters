import Textbook.Ch11.Audit
import Mathlib.Analysis.Calculus.SmoothSeries

namespace Ch11

open Filter Set
open scoped Topology

noncomputable def endpointStep (x : ℝ) : ℝ := if x = 1 then 1 else 0

theorem powers_pointwise :
    PointwiseOn (fun n (x : ℝ) => x^n) endpointStep (Icc 0 1) := by
  intro x hx
  by_cases he : x = 1
  · subst x
    simpa [endpointStep] using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ)))
  · simpa [endpointStep,he] using
      tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 (lt_of_le_of_ne hx.2 he)

theorem powers_not_uniform :
    ¬ TendstoUniformlyOn (fun n (x : ℝ) => x^n) endpointStep atTop (Icc 0 1) := by
  intro hu
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hu) (1/2) (by norm_num))
  have hc : Continuous (fun x : ℝ => x^N) := by fun_prop
  have hlim : Tendsto (fun x : ℝ => x^N) (𝓝[<] (1:ℝ)) (𝓝 1) := by
    have h := (hc.continuousAt (x := (1:ℝ))).continuousWithinAt (s := Iio 1)
    change Tendsto _ _ (𝓝 ((1:ℝ)^N)) at h
    simpa only [one_pow] using h
  have he : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), (1/2:ℝ) < x^N :=
    hlim.eventually (Ioi_mem_nhds (by norm_num))
  have hmem : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), x ∈ Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨x,hx,hpow⟩ := (hmem.and he).exists
  have hb := hN N le_rfl x ⟨hx.1.le,hx.2.le⟩
  rw [Real.dist_eq,abs_sub_comm,endpointStep,ite_eq_right hx.2.ne,sub_zero,
    abs_of_nonneg (pow_nonneg hx.1.le _)] at hb
  exact (not_lt_of_ge hpow.le) hb

theorem powers_limit_discontinuous : ¬ ContinuousOn endpointStep (Icc 0 1) := by
  intro h
  have hz : Tendsto endpointStep (𝓝[<] (1:ℝ)) (𝓝 0) := by
    apply (tendsto_const_nhds (x := (0:ℝ))).congr'
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0:ℝ) < 1)] with x hx
    simp [endpointStep,hx.2.ne]
  have ho : Tendsto endpointStep (𝓝[<] (1:ℝ)) (𝓝 1) := by
    have hh := h 1 (by simp)
    have hm : (𝓝[<] (1:ℝ)) ≤ 𝓝[Icc 0 1] (1:ℝ) := by
      apply le_inf nhdsWithin_le_nhds
      apply le_principal_iff.mpr
      exact mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) Ioo_subset_Icc_self
    simpa [endpointStep] using hh.tendsto.mono_left hm
  exact zero_ne_one (tendsto_nhds_unique hz ho)

theorem geometric_uniform_on_closed {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) :
    TendstoUniformlyOn (fun N (x : ℝ) => partialSum (fun n => x^n) N)
      (fun x => 1/(1-x)) atTop {x | |x| ≤ r} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr).div_const (1-r)
  have hz : Tendsto (fun N : ℕ => r^N/(1-r)) atTop (𝓝 0) := by simpa using h
  filter_upwards [hz.eventually (Iio_mem_nhds hε)] with N hN x hx
  rw [Real.dist_eq,abs_sub_comm]
  exact (geometric_uniform_bound r x hr₀ hr hx N).trans_lt hN

theorem geometric_not_uniform_on_open :
    ¬ TendstoUniformlyOn (fun N (x : ℝ) => partialSum (fun n => x^n) N)
      (fun x => 1/(1-x)) atTop (Ioo (-1:ℝ) 1) := by
  intro hu
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hu) 1 zero_lt_one)
  have hc : Continuous (fun x : ℝ => x^N) := by fun_prop
  have hp : Tendsto (fun x : ℝ => x^N) (𝓝[<] (1:ℝ)) (𝓝 1) := by
    have h := (hc.continuousAt (x := (1:ℝ))).continuousWithinAt (s := Iio 1)
    change Tendsto _ _ (𝓝 ((1:ℝ)^N)) at h
    simpa only [one_pow] using h
  have he : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), (1/2:ℝ) < x^N :=
    hp.eventually (Ioi_mem_nhds (by norm_num))
  have hmem : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), x ∈ Ioo (1/2) 1 := Ioo_mem_nhdsLT (by norm_num)
  obtain ⟨x,hx,hpow⟩ := (hmem.and he).exists
  have h := hN N le_rfl x (show x ∈ Ioo (-1:ℝ) 1 from ⟨by linarith [hx.1],hx.2⟩)
  rw [Real.dist_eq,geometric_remainder x hx.2.ne N,abs_of_pos (div_pos
    ((by norm_num : (0:ℝ) < 1/2).trans hpow) (sub_pos.mpr hx.2))] at h
  have hh := (div_lt_iff₀ (sub_pos.mpr hx.2)).mp h
  linarith [hx.1]

theorem sine_series_uniform_and_derivative :
    TendstoUniformlyOn
      (fun N x => partialSum (fun n : ℕ => Real.sin ((n:ℝ)*x)*(1/2:ℝ)^n) N)
      (fun x => ∑' n : ℕ, Real.sin ((n:ℝ)*x)*(1/2:ℝ)^n) atTop univ ∧
    ∀ x, HasDerivAt (fun t => ∑' n : ℕ, Real.sin ((n:ℝ)*t)*(1/2:ℝ)^n)
      (∑' n : ℕ, (n:ℝ)*Real.cos ((n:ℝ)*x)*(1/2:ℝ)^n) x := by
  have hq : ‖(1/2:ℝ)‖ < 1 := by norm_num
  have hs := summable_geometric_of_norm_lt_one hq
  refine ⟨?_,fun x => ?_⟩
  · exact (weierstrass_test (M := fun n => (1/2:ℝ)^n) (fun _ => by positivity)
      ⟨_, hs.hasSum.tendsto_sum_nat⟩ (fun n x _ => by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)]
        exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one _))).2
  have hu : Summable (fun n : ℕ => (n:ℝ)*(1/2:ℝ)^n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hq
  exact hasDerivAt_tsum hu (y₀ := (0:ℝ))
    (g := fun (n : ℕ) (t : ℝ) => Real.sin ((n:ℝ)*t)*(1/2:ℝ)^n)
    (g' := fun (n : ℕ) (t : ℝ) => (n:ℝ)*Real.cos ((n:ℝ)*t)*(1/2:ℝ)^n)
    (fun n t => by
    have h := (((hasDerivAt_id t).const_mul (n:ℝ)).sin).mul_const ((1/2:ℝ)^n)
    simpa [id_eq,mul_comm,mul_left_comm,mul_assoc] using h)
    (fun n t => by
      change ‖(n:ℝ)*Real.cos ((n:ℝ)*t)*(1/2:ℝ)^n‖ ≤ (n:ℝ)*(1/2:ℝ)^n
      simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
        abs_of_nonneg (pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) n)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (Nat.cast_nonneg (α := ℝ) n)
        (Real.abs_cos_le_one _)) (by positivity))
    (by simp) x

private theorem geometric_weighted_tail (N : ℕ) :
    (∑' j : ℕ, (1/2:ℝ)^(j+N+1)) = (1/2:ℝ)^N ∧
    (∑' j : ℕ, (j+N+1:ℝ)*(1/2:ℝ)^(j+N+1)) = (N+2:ℝ)*(1/2:ℝ)^N := by
  let q : ℝ := 1/2
  have hq : ‖q‖ < 1 := by norm_num [q]
  have hg : HasSum (fun j : ℕ => q^j) 2 := by
    have h := hasSum_geometric_of_norm_lt_one hq
    norm_num [q] at h ⊢
    exact h
  have hw : HasSum (fun j : ℕ => (j:ℝ)*q^j) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one hq
    norm_num [q] at h ⊢
    exact h
  have h1 := hg.mul_left (q^(N+1))
  have h2 := (hw.add (hg.mul_left (N+1:ℝ))).mul_left (q^(N+1))
  have e1 : (fun j : ℕ => q^(N+1)*q^j) = fun j : ℕ => q^(j+N+1) := by
    funext j
    rw [← pow_add]
    congr 1
    omega
  have e2 : (fun j : ℕ => q^(N+1)*((j:ℝ)*q^j+(N+1:ℝ)*q^j)) =
      fun j : ℕ => (j+N+1:ℝ)*q^(j+N+1) := by
    funext j
    rw [show j+N+1 = (N+1)+j by omega,pow_add]
    ring
  rw [e1] at h1
  rw [e2] at h2
  have hv : q*2 = 1 := by norm_num [q]
  constructor
  · rw [h1.tsum_eq,pow_succ]
    linear_combination q^N*hv
  · rw [h2.tsum_eq,pow_succ]
    linear_combination (q^N*(N+2))*hv

set_option maxHeartbeats 600000 in
theorem sine_series_tail_bounds (x : ℝ) (N : ℕ) :
    |(∑' n : ℕ, Real.sin ((n:ℝ)*x)*(1/2:ℝ)^n) -
      partialSum (fun n : ℕ => Real.sin ((n:ℝ)*x)*(1/2:ℝ)^n) (N+1)| ≤ (1/2:ℝ)^N ∧
    |(∑' n : ℕ, (n:ℝ)*Real.cos ((n:ℝ)*x)*(1/2:ℝ)^n) -
      partialSum (fun n : ℕ => (n:ℝ)*Real.cos ((n:ℝ)*x)*(1/2:ℝ)^n) (N+1)| ≤
        (N+2:ℝ)*(1/2:ℝ)^N := by
  have tail {f m : ℕ → ℝ} (hm : Summable m) (hf : ∀ n, |f n| ≤ m n) :
      |(∑' n, f n) - partialSum f (N+1)| ≤ ∑' j : ℕ, m (j+N+1) := by
    have ha : Summable (fun n => |f n|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hf hm
    have hs := ha.of_abs
    obtain ⟨L,hL,hB⟩ := absolute_tail_bound ((positive_series_summable (fun n => abs_nonneg (f n))).2 ha)
    have he : L = ∑' n, f n := tendsto_nhds_unique hL hs.hasSum.tendsto_sum_nat
    rw [he] at hB
    exact (hB (N+1)).trans (by
      have hsa : Summable (fun j => |f (j+(N+1))|) := (summable_nat_add_iff (N+1)).2 ha
      have hsm : Summable (fun j => m (j+(N+1))) := (summable_nat_add_iff (N+1)).2 hm
      simpa only [Nat.add_assoc] using hsa.tsum_le_tsum (fun j => hf (j+(N+1))) hsm)
  have hq : ‖(1/2:ℝ)‖ < 1 := by norm_num
  have ht := geometric_weighted_tail N
  constructor
  · rw [← ht.1]
    apply tail (summable_geometric_of_norm_lt_one hq)
    intro n
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one _)
  · rw [← ht.2]
    have hs : Summable (fun n : ℕ => (n:ℝ)*(1/2:ℝ)^n) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hq
    have h := tail (f := fun n : ℕ => (n:ℝ)*Real.cos ((n:ℝ)*x)*(1/2:ℝ)^n) hs
      (fun n => by
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
          abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (Nat.cast_nonneg n) (Real.abs_cos_le_one _)) (by positivity))
    simpa only [Nat.cast_add,Nat.cast_one] using h

end Ch11
