import Textbook.Ch10.Comparison

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem absolute_improper_tail_bound {f : ℝ → ℝ} {a H : ℝ}
    (hi : LocallyIntervalIntegrable f a)
    (habs : ImproperRight (fun x => |f x|) a H) :
    ∃ L, ImproperRight f a L ∧ ∀ T ≥ a,
      |L - (∫ x in a..T, f x)| ≤ H - ∫ x in a..T, |f x| := by
  obtain ⟨L,hL⟩ : ∃ L, ImproperRight f a L := by
    apply (improper_cauchy hi).2
    intro ε hε
    obtain ⟨B,hB,h⟩ := (improper_cauchy habs.1).1 ⟨H,habs⟩ ε hε
    refine ⟨B,hB,fun T hT U hU => ?_⟩
    have bound (s t : ℝ) (hs : B ≤ s) (ht : B ≤ t) (hst : s ≤ t) :
        |∫ x in s..t, f x| < ε :=
      (Ch09.integral_abs_bound hst).trans_lt
        ((le_abs_self _).trans_lt (h s hs t ht))
    rcases le_total T U with hTU | hUT
    · exact bound T U hT hU hTU
    · rw [intervalIntegral.integral_symm U T,abs_neg]
      exact bound U T hU hT hUT
  refine ⟨L,hL,fun T hT => ?_⟩
  apply le_of_tendsto_of_tendsto ((hL.2.sub_const _).abs) (habs.2.sub_const _)
  filter_upwards [eventually_ge_atTop T] with U hU
  rw [intervalIntegral.integral_interval_sub_left (hi U (hT.trans hU)) (hi T hT),
    intervalIntegral.integral_interval_sub_left (habs.1 U (hT.trans hU)) (habs.1 T hT)]
  exact Ch09.integral_abs_bound hU

theorem dominated_improper {f g : ℝ → ℝ} {a G : ℝ}
    (hf : LocallyIntervalIntegrable f a) (hg : ImproperRight g a G)
    (hb : ∀ x ≥ a, |f x| ≤ g x) :
    AbsolutelyImproperRight f a ∧ ∃ L, ImproperRight f a L ∧ ∀ T ≥ a,
      |L - (∫ x in a..T, f x)| ≤ G - ∫ x in a..T, g x := by
  have ha : LocallyIntervalIntegrable (fun x => |f x|) a :=
    fun T hT => (hf T hT).norm
  obtain ⟨H,hH⟩ := (improper_comparison le_rfl ha hg.1
    (fun x hx => ⟨abs_nonneg _,hb x hx⟩)).1 ⟨G,hg⟩
  obtain ⟨L,hL,ht⟩ := absolute_improper_tail_bound hf hH
  refine ⟨⟨hf,H,hH⟩,L,hL,fun T hT => (ht T hT).trans ?_⟩
  apply le_of_tendsto_of_tendsto (hH.2.sub_const _) (hg.2.sub_const _)
  filter_upwards [eventually_ge_atTop T] with U hU
  rw [intervalIntegral.integral_interval_sub_left (ha U (hT.trans hU)) (ha T hT),
    intervalIntegral.integral_interval_sub_left (hg.1 U (hT.trans hU)) (hg.1 T hT)]
  exact intervalIntegral.integral_mono_on hU
    ((ha T hT).symm.trans (ha U (hT.trans hU)))
    ((hg.1 T hT).symm.trans (hg.1 U (hT.trans hU))) (fun x hx => hb x (hT.trans hx.1))

/-- A uniform distance bound on the fixed interval controls the integrals. -/
theorem uniform_interval_exchange {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ n, IntervalIntegrable (F n) volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hu : TendstoUniformlyOn F f atTop (Icc a b)) :
    Tendsto (fun n => ∫ x in a..b, F n x) atTop (𝓝 (∫ x in a..b, f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d := ε/(b-a+1)
  have hd : 0 < d := div_pos hε (by linarith)
  have hs := (Metric.tendstoUniformlyOn_iff.mp hu) d hd
  filter_upwards [hs] with n hn
  rw [Real.dist_eq, ← intervalIntegral.integral_sub (hF n) hf]
  have hbound : ∀ x ∈ Ι a b, ‖F n x - f x‖ ≤ d := by
    rw [uIoc_of_le hab]
    intro x hx
    rw [Real.norm_eq_abs]
    exact (by simpa [Real.dist_eq, abs_sub_comm] using (hn x (Ioc_subset_Icc_self hx)).le)
  have he := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hmul : d*(b-a+1) = ε := div_mul_cancel₀ _ (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hab), Real.norm_eq_abs] at he
  exact he.trans_lt (by linarith)

/-- Fix a cutoff for the common tail before applying uniform convergence. -/
theorem common_tail_exchange {F : ℕ → ℝ → ℝ} {f g : ℝ → ℝ} {a G : ℝ}
    (hF : ∀ n, LocallyIntervalIntegrable (F n) a)
    (hf : LocallyIntervalIntegrable f a) (hg : ImproperRight g a G)
    (hu : ∀ T ≥ a, TendstoUniformlyOn F f atTop (Icc a T))
    (hb : ∀ n x, a ≤ x → |F n x| ≤ g x) :
    (∀ n, AbsolutelyImproperRight (F n) a) ∧ AbsolutelyImproperRight f a ∧
      ∃ (L : ℝ) (I : ℕ → ℝ), ImproperRight f a L ∧
        (∀ n, ImproperRight (F n) a (I n)) ∧ Tendsto I atTop (𝓝 L) := by
  have hb' (x : ℝ) (hx : a ≤ x) : |f x| ≤ g x := by
    have ht := (hu x hx).tendsto_at ⟨hx,le_rfl⟩
    exact le_of_tendsto' ht.abs (fun n => hb n x hx)
  have h := fun n => dominated_improper (hF n) hg (fun x hx => hb n x hx)
  obtain ⟨hfabs,L,hL,hLt⟩ := dominated_improper hf hg hb'
  choose I hI hIt using fun n => (h n).2
  refine ⟨fun n => (h n).1,hfabs,L,I,hL,hI,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨B,hB,hcut⟩ := ((improper_right_epsilon_iff _ _ _).1 hg).2 (ε/4) (by positivity)
  have htail : G - (∫ x in a..B, g x) < ε/4 := by
    linarith [(abs_lt.mp (hcut B le_rfl)).1]
  have hlim := uniform_interval_exchange hB (fun n => hF n B hB) (hf B hB) (hu B hB)
  filter_upwards [(Metric.tendsto_nhds.mp hlim) (ε/2) (by positivity)] with n hn
  rw [Real.dist_eq] at hn ⊢
  let A := ∫ x in a..B, F n x
  let C := ∫ x in a..B, f x
  have h₁ := abs_sub_le (I n) A L
  have h₂ := abs_sub_le A C L
  rw [abs_sub_comm C L] at h₂
  linarith [hIt n B hB,hLt B hB]

theorem interval_exchange_of_distance_bound {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {r : ℕ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ n, IntervalIntegrable (F n) volume a b) (hf : IntervalIntegrable f volume a b)
    (hr : Tendsto r atTop (𝓝 0)) (hb : ∀ n x, x ∈ Icc a b → |F n x - f x| ≤ r n) :
    Tendsto (fun n => ∫ x in a..b, F n x) atTop (𝓝 (∫ x in a..b, f x)) := by
  apply uniform_interval_exchange hab hF hf
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hr.eventually (Iio_mem_nhds hε)] with n hn x hx
  simpa [Real.dist_eq,abs_sub_comm] using (hb n x hx).trans_lt hn

theorem sine_inverse_square_tail :
    AbsolutelyImproperRight (fun x : ℝ => Real.sin x/x^2) 1 ∧
      ∃ L, ImproperRight (fun x : ℝ => Real.sin x/x^2) 1 L ∧ ∀ T ≥ 1,
        |L - (∫ x in (1:ℝ)..T, Real.sin x/x^2)| ≤ 1/T := by
  have hg : ImproperRight (fun x : ℝ => x ^ (-(2:ℝ))) 1 1 := by
    convert power_improper_converges (by norm_num : (1:ℝ) < 2) using 1 <;> norm_num
  have hf : LocallyIntervalIntegrable (fun x : ℝ => Real.sin x/x^2) 1 := by
    intro T hT
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact Real.continuous_sin.continuousOn.div (by fun_prop) (fun x hx => by
      have hx₀ : 0 < x := zero_lt_one.trans_le hx.1
      positivity)
  have hb (x : ℝ) (hx : 1 ≤ x) : |Real.sin x/x^2| ≤ x ^ (-(2:ℝ)) := by
    rw [abs_div, abs_of_nonneg (sq_nonneg x),
      Real.rpow_neg (zero_le_one.trans hx), Real.rpow_two, ← one_div]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (sq_nonneg x)
  obtain ⟨ha,L,hL,h⟩ := dominated_improper hf hg hb
  refine ⟨ha,L,hL,fun T hT => (h T hT).trans ?_⟩
  have he := power_tail_identity (by norm_num : (1:ℝ) < 2) hT
  norm_num [Real.rpow_neg_one,one_div] at he ⊢
  linarith

end Ch10
