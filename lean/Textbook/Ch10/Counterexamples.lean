import Textbook.Ch10.LimitExchange
import Textbook.Ch09.DarbouxCriterion
import Textbook.Ch09.MeasureBridge

namespace Ch10

open Filter MeasureTheory Set
open scoped Topology Interval

noncomputable def movingSpike (n : ℕ) (x : ℝ) : ℝ :=
  (Ioo 0 (1/(n:ℝ))).indicator (fun _ => (n:ℝ)) x

theorem moving_spike_tagged {n : ℕ} (hn : 1 ≤ n) :
    Ch09.HasTaggedIntegral (movingSpike n) 0 1 1 := by
  classical
  have hn₀ : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  by_cases h : n = 1
  · subst n
    have hcell : Ch09.HasTaggedIntegral ((Icc 0 1).indicator (fun _ => (1:ℝ))) 0 1 1 := by
      apply (Ch09.tagged_integral_iff _ _ _ _).2
      intro ε hε
      refine ⟨1,one_pos,fun P _ => ?_⟩
      have hsum : P.riemannSum ((Icc 0 1).indicator (fun _ => (1:ℝ))) =
          P.riemannSum (fun _ => 1) := by
        unfold Ch09.TaggedPartition.riemannSum
        apply Finset.sum_congr rfl
        intro i _
        have ht : P.tag i ∈ Icc 0 1 :=
          ⟨(P.first.ge.trans (P.increasing.monotone (Fin.zero_le _))).trans (P.tag_mem i).1,
            (P.tag_mem i).2.trans ((P.increasing.monotone (Fin.le_last _)).trans P.last.le)⟩
        simp [ht]
      simpa [hsum,Ch09.tagged_constant_sum] using hε
    apply Ch09.tagged_integral_finite_change hcell {0,1}
    intro x hx
    have hx' : x ≠ 0 ∧ x ≠ 1 := by simpa using hx
    have he : x ∈ Ioo (0:ℝ) 1 ↔ x ∈ Icc (0:ℝ) 1 := by
      simp only [mem_Ioo,mem_Icc,lt_iff_le_and_ne]
      tauto
    simpa only [movingSpike,Nat.cast_one,div_one] using
      (show (Ioo (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x =
        (Icc 0 1).indicator (fun _ => 1) x by
          by_cases hx : x ∈ Ioo (0:ℝ) 1 <;> simp [hx,← he])
  · have hn₁ : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hw : 0 < 1/(n:ℝ) := one_div_pos.mpr hn₀
    have hw₁ : 1/(n:ℝ) < 1 := (div_lt_iff₀ hn₀).2 (by simpa using hn₁)
    have hs := (Ch09.tagged_step_example hw hw₁).1
    have hv : (n:ℝ) * (1/(n:ℝ)) = 1 := by field_simp
    have hs' : Ch09.HasTaggedIntegral
        ((Icc 0 (1/(n:ℝ))).indicator (fun _ => (n:ℝ))) 0 1 1 := by
      convert Ch09.tagged_integral_linear hs hs (n:ℝ) 0 using 1
      · funext x
        change ((Icc 0 (1/(n:ℝ))).indicator (fun _ => (n:ℝ))) x =
          (n:ℝ)*((Icc 0 (1/(n:ℝ))).indicator (fun _ => (1:ℝ))) x +
            0*((Icc 0 (1/(n:ℝ))).indicator (fun _ => (1:ℝ))) x
        by_cases hx : x ∈ Icc 0 (1/(n:ℝ))
        · simp only [indicator_of_mem hx,mul_one,zero_mul,add_zero]
        · simp only [indicator_of_notMem hx,mul_zero,add_zero]
      · simpa using hv.symm
    apply Ch09.tagged_integral_finite_change hs' {0, 1/(n:ℝ)}
    intro x hx
    have hx' : x ≠ 0 ∧ x ≠ 1/(n:ℝ) := by simpa using hx
    have he : x ∈ Ioo 0 (1/(n:ℝ)) ↔ x ∈ Icc 0 (1/(n:ℝ)) := by
      simp only [mem_Ioo,mem_Icc,lt_iff_le_and_ne]
      tauto
    unfold movingSpike
    by_cases hx : x ∈ Ioo 0 (1/(n:ℝ))
    · rw [indicator_of_mem hx,indicator_of_mem (he.mp hx)]
    · rw [indicator_of_notMem hx,indicator_of_notMem (he.not.mp hx)]

theorem moving_spike_pointwise (x : ℝ) :
    Tendsto (fun n => movingSpike n x) atTop (𝓝 0) := by
  apply (tendsto_const_nhds (x := (0:ℝ))).congr'
  by_cases hx : 0 < x
  · obtain ⟨N,hN⟩ := exists_nat_gt (1/x)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlt : 1/x < (n:ℝ) := hN.trans_le (by exact_mod_cast hn)
    have hn₀ : 0 < (n:ℝ) := (one_div_pos.mpr hx).trans hlt
    have h : 1/(n:ℝ) < x := (div_lt_iff₀ hn₀).2 (by
      have := (div_lt_iff₀ hx).1 hlt
      simpa [mul_comm] using this)
    unfold movingSpike
    rw [indicator_of_notMem (show x ∉ Ioo 0 (1/(n:ℝ)) from
      fun hx' => (not_lt_of_ge h.le) hx'.2)]
  · exact Eventually.of_forall fun n => by
      change 0 = (Ioo 0 (1/(n:ℝ))).indicator (fun _ => (n:ℝ)) x
      rw [indicator_of_notMem (show x ∉ Ioo 0 (1/(n:ℝ)) from
        fun hx' => hx hx'.1)]

theorem moving_spike_exchange_failure :
    (∀ x, Tendsto (fun n => movingSpike n x) atTop (𝓝 0)) ∧
    Tendsto (fun n => ∫ x in (0:ℝ)..1, movingSpike n x) atTop (𝓝 1) ∧
    (∫ _ in (0:ℝ)..1, (0:ℝ)) = 0 := by
  refine ⟨moving_spike_pointwise,?_,by simp⟩
  apply (tendsto_const_nhds (x := (1:ℝ))).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact (Ch09.tagged_measure_agreement zero_lt_one (moving_spike_tagged hn)).2.symm

theorem parts_divergent_terms :
    (∀ T ≥ (1:ℝ), T-1 = T * Real.log T - ∫ x in (1:ℝ)..T, Real.log x) ∧
    Tendsto (fun T : ℝ => T * Real.log T) atTop atTop ∧
    Tendsto (fun T : ℝ => ∫ x in (1:ℝ)..T, Real.log x) atTop atTop := by
  refine ⟨fun T _ => ?_,?_,?_⟩
  · rw [integral_log,Real.log_one]
    ring
  · apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (max 0 B),
      Filter.Tendsto.eventually Real.tendsto_log_atTop (eventually_ge_atTop 2)] with T hT hlog
    have h₀ : 0 ≤ T := (le_max_left _ _).trans hT
    have hB : B ≤ T := (le_max_right _ _).trans hT
    nlinarith
  · apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (max 0 B),
      Filter.Tendsto.eventually Real.tendsto_log_atTop (eventually_ge_atTop 2)] with T hT hlog
    have h₀ : 0 ≤ T := (le_max_left _ _).trans hT
    have hB : B ≤ T := (le_max_right _ _).trans hT
    change B ≤ ∫ x in (1:ℝ)..T, Real.log x
    rw [integral_log,Real.log_one]
    nlinarith

theorem independent_endpoints_counterexample :
    (∀ T : ℝ, (∫ x in (-T)..T, Real.sin x) = 0) ∧
    ¬ ∃ L : ℝ, Tendsto (fun ab : ℝ × ℝ => ∫ x in ab.1..ab.2, Real.sin x)
      ((atBot : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 L) := by
  refine ⟨fun T => by rw [integral_sin,Real.cos_neg,sub_self],?_⟩
  rintro ⟨L,hL⟩
  have hn : Tendsto (fun n : ℕ => (n:ℝ)*(2*Real.pi)) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos (by positivity : 0 < 2*Real.pi)).2 tendsto_natCast_atTop_atTop
  have hn' : Tendsto (fun n : ℕ => -((n:ℝ)*(2*Real.pi))) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hn
  have hm : Tendsto (fun n : ℕ => (n:ℝ)*(2*Real.pi) + Real.pi) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_atTop.1 hn b] with n h
    linarith [Real.pi_pos]
  have hz : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 L) :=
    (hL.comp (hn'.prodMk hn)).congr fun n => by
      change (∫ x in (-((n:ℝ)*(2*Real.pi)))..((n:ℝ)*(2*Real.pi)), Real.sin x) = 0
      rw [integral_sin,Real.cos_neg,sub_self]
  have ht : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 L) :=
    (hL.comp (hn'.prodMk hm)).congr fun n => by
      change (∫ x in (-((n:ℝ)*(2*Real.pi)))..((n:ℝ)*(2*Real.pi)+Real.pi), Real.sin x) = 2
      rw [integral_sin,Real.cos_neg,Real.cos_nat_mul_two_pi,Real.cos_nat_mul_two_pi_add_pi]
      norm_num
  have h₀ := tendsto_nhds_unique hz tendsto_const_nhds
  have h₂ := tendsto_nhds_unique ht tendsto_const_nhds
  linarith

end Ch10
