import Textbook.Ch11.Series
import Textbook.Ch09.Tagged
import Textbook.Ch08.Audit

namespace Ch11
open Filter MeasureTheory Set
open scoped Topology Interval BigOperators Uniformity

def SeriesConverges (a : ℕ → ℝ) : Prop := ∃ s, SeriesHasSum a s
def AbsolutelyConvergent (a : ℕ → ℝ) : Prop := SeriesConverges (fun n => |a n|)
def ConditionallyConvergent (a : ℕ → ℝ) : Prop :=
  SeriesConverges a ∧ ¬ AbsolutelyConvergent a

def seriesRemainder (a : ℕ → ℝ) (s : ℝ) (N : ℕ) : ℝ := s - partialSum a N

def PointwiseOn {α : Type*} (F : ℕ → α → ℝ) (f : α → ℝ) (E : Set α) : Prop :=
  ∀ x ∈ E, Tendsto (fun N => F N x) atTop (𝓝 (f x))

theorem pointwise_on_iff {α : Type*} (F : ℕ → α → ℝ) (f : α → ℝ) (E : Set α) :
    PointwiseOn F f E ↔
      ∀ x ∈ E, ∀ ε > 0, ∃ K, ∀ N ≥ K, |F N x-f x| < ε := by
  simp only [PointwiseOn, Metric.tendsto_atTop, Real.dist_eq]

theorem finite_geometric (q : ℝ) (hq : q ≠ 1) (N : ℕ) :
    partialSum (fun n => q^n) N = (1-q^N)/(1-q) := by
  have he := geometric_remainder q hq N
  rw [sub_div]
  linarith

theorem positive_criterion {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    SeriesConverges a ↔ ∃ B : ℝ, ∀ N, partialSum a N ≤ B := by
  have hm : Monotone (partialSum a) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [partialSum_succ]
    exact le_add_of_nonneg_right (ha n)
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, fun n => hm.ge_of_tendsto hs n⟩
  · rintro ⟨B,hB⟩
    have hb : BddAbove (range (partialSum a)) := ⟨B, fun _ ⟨n,hn⟩ => hn ▸ hB n⟩
    exact ⟨_, tendsto_atTop_ciSup hm hb⟩

theorem positive_series_summable {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    SeriesConverges a ↔ Summable a := by
  constructor
  · rintro ⟨s,hs⟩
    exact ((hasSum_iff_tendsto_nat_of_nonneg ha s).2 hs).summable
  · intro h
    exact ⟨_, h.hasSum.tendsto_sum_nat⟩

theorem p_series_criterion (p : ℝ) :
    SeriesConverges (fun n => 1 / ((n+1 : ℕ) : ℝ)^p) ↔ 1 < p := by
  rw [positive_series_summable (fun n => by positivity)]
  exact (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^p) 1).trans
    Real.summable_one_div_nat_rpow

theorem harmonic_counterexample :
    Tendsto (fun n : ℕ => 1 / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) ∧
      ¬ SeriesConverges (fun n => 1 / ((n+1 : ℕ) : ℝ)) := by
  constructor
  · simpa [one_div, Function.comp_def] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  · simpa using (p_series_criterion 1).not

theorem cauchy_tail_criterion (a : ℕ → ℝ) :
    SeriesConverges a ↔ ∀ ε > 0, ∃ K, ∀ N ≥ K, ∀ M > N,
      |∑ k ∈ Finset.Ico N M, a k| < ε := by
  rw [SeriesConverges, series_cauchy_iff, Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    obtain ⟨K,hK⟩ := h ε hε
    refine ⟨K,fun N hN M hM => ?_⟩
    rw [Finset.sum_Ico_eq_sub _ hM.le]
    exact hK M (hN.trans hM.le) N hN
  · intro h ε hε
    obtain ⟨K,hK⟩ := h ε hε
    refine ⟨K,fun N hN M hM => ?_⟩
    rcases lt_trichotomy N M with hlt | rfl | hgt
    · rw [dist_comm, Real.dist_eq]
      simpa only [partialSum, Finset.sum_Ico_eq_sub _ hlt.le] using hK N hN M hlt
    · simpa using hε
    · rw [Real.dist_eq]
      simpa only [partialSum, Finset.sum_Ico_eq_sub _ hgt.le] using hK M hM N hgt

theorem uniform_continuous_limit {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {f : α → ℝ} {E : Set α}
    (hF : ∀ N, ContinuousOn (F N) E) (h : TendstoUniformlyOn F f atTop E) :
    ContinuousOn f E :=
  h.continuousOn (Eventually.of_forall hF).frequently

/-- The closed-interval result, with an explicit tagged-integral witness for every term
and for the limiting function. -/
theorem termwise_tagged_integral {u : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ∀ n, ContinuousOn (u n) (Icc a b))
    (h : TendstoUniformlyOn (fun N x => partialSum (fun n => u n x) N)
      f atTop (Icc a b)) :
    ∃ I : ℕ → ℝ, ∃ L : ℝ,
      (∀ n, Ch09.HasTaggedIntegral (u n) a b (I n)) ∧
      ContinuousOn f (Icc a b) ∧ Ch09.HasTaggedIntegral f a b L ∧
      SeriesHasSum I L := by
  let F := fun N x => partialSum (fun n => u n x) N
  have hF (N : ℕ) : ContinuousOn (F N) (Icc a b) := by
    induction N with
    | zero => simpa [F, partialSum] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0:ℝ)) (Icc a b))
    | succ N ih =>
      have he : F (N+1) = fun x => F N x + u N x := by
        funext x
        exact partialSum_succ (fun n => u n x) N
      rw [he]
      exact ih.add (hu N)
  have hf := uniform_continuous_limit hF h
  let I := fun n => ∫ x in a..b, u n x
  let L := ∫ x in a..b, f x
  refine ⟨I,L,fun n => Ch09.continuous_tagged_integral hab (hu n), hf,
    Ch09.continuous_tagged_integral hab hf, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (2*(b-a))
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨K,hK⟩ := (uniform_on_iff F f (Icc a b)).1 h η hη
  refine ⟨K,fun N hN => ?_⟩
  have hsum : (∫ x in a..b, F N x) = partialSum I N := by
    exact intervalIntegral.integral_finsetSum (fun n _ => (hu n).intervalIntegrable_of_Icc hab.le)
  have hdiff := intervalIntegral.integral_sub (μ := volume) ((hF N).intervalIntegrable_of_Icc hab.le)
    (hf.intervalIntegrable_of_Icc hab.le)
  have hbound : ∀ x ∈ Ι a b, ‖F N x-f x‖ ≤ η := by
    rw [uIoc_of_le hab.le]
    intro x hx
    rw [Real.norm_eq_abs]
    exact (hK N hN x (Ioc_subset_Icc_self hx)).le
  have he := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hdiff, hsum, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at he
  rw [Real.dist_eq]
  have he' : η*(2*(b-a)) = ε := div_mul_cancel₀ _ (by linarith)
  exact he.trans_lt (by linarith)

theorem absolute_tail_bound {a : ℕ → ℝ} (ha : AbsolutelyConvergent a) :
    ∃ s, SeriesHasSum a s ∧
      ∀ N, |seriesRemainder a s N| ≤ ∑' k : ℕ, |a (k+N)| := by
  have h := (positive_series_summable (fun n => abs_nonneg (a n))).1 ha
  have hs : Summable a := summable_norm_iff.mp (by simpa [Real.norm_eq_abs] using h)
  refine ⟨_,hs.hasSum.tendsto_sum_nat,fun N => ?_⟩
  have he := hs.sum_add_tsum_nat_add N
  have ht : seriesRemainder a (∑' k, a k) N = ∑' k, a (k+N) := by
    unfold seriesRemainder partialSum
    linarith
  rw [ht]
  simpa [Real.norm_eq_abs] using
    (norm_tsum_le_tsum_norm (f := fun k : ℕ => a (k+N))
      (by simpa [Real.norm_eq_abs] using (summable_nat_add_iff N).2 h))

theorem alternating_criterion {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hm : Antitone b) (h0 : Tendsto b atTop (𝓝 0)) :
    ∃ s, SeriesHasSum (fun n => (-1:ℝ)^n*b n) s ∧
      ∀ N, |seriesRemainder (fun n => (-1:ℝ)^n*b n) s N| ≤ b N ∧
        0 ≤ (-1:ℝ)^N * seriesRemainder (fun n => (-1:ℝ)^n*b n) s N := by
  obtain ⟨s,hs⟩ := hm.tendsto_alternating_series_of_tendsto_zero h0
  refine ⟨s,hs,fun N => ?_⟩
  have lower := hm.alternating_series_le_tendsto hs
  have upper := hm.tendsto_le_alternating_series hs
  obtain hN | hN := Nat.even_or_odd N
  · obtain ⟨n,rfl⟩ := even_iff_exists_two_mul.mp hN
    specialize lower n
    specialize upper n
    simp only [Finset.sum_range_succ, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul] at upper
    simp only [seriesRemainder, partialSum, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul]
    exact ⟨abs_le.mpr ⟨by linarith [hb (2*n)], by linarith⟩, by linarith⟩
  · obtain ⟨n,rfl⟩ := odd_iff_exists_bit1.mp hN
    specialize lower (n+1)
    specialize upper n
    have hlow : (∑ i ∈ Finset.range (2*n+1), (-1:ℝ)^i*b i)-b (2*n+1) ≤ s := by
      simpa [Nat.mul_add, Finset.sum_range_succ, pow_add] using lower
    simp only [seriesRemainder, partialSum, pow_add, even_two, Even.mul_right,
      Even.neg_pow, one_pow, pow_one, one_mul, neg_one_mul]
    exact ⟨abs_le.mpr ⟨by linarith, by linarith [hb (2*n+1)]⟩, by linarith⟩

def powerSeriesTerm (c : ℕ → ℝ) (a x : ℝ) (n : ℕ) : ℝ := c n * (x-a)^n

def radiusSet (c : ℕ → ℝ) : Set ℝ :=
  {r | 0 ≤ r ∧ SeriesConverges (fun n => |c n| * r^n)}

noncomputable def convergenceRadius (c : ℕ → ℝ) : WithTop ℝ := by
  classical
  exact if BddAbove (radiusSet c) then (sSup (radiusSet c) : ℝ) else ⊤

noncomputable def fourierCos (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1/Real.pi) * (∫ x in -Real.pi..Real.pi, f x * Real.cos (n*x))

noncomputable def fourierSin (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1/Real.pi) * (∫ x in -Real.pi..Real.pi, f x * Real.sin (n*x))

noncomputable def fourierPartialSum (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  fourierCos f 0 / 2 + ∑ n ∈ Finset.Icc 1 N,
    (fourierCos f n * Real.cos (n*x) + fourierSin f n * Real.sin (n*x))

theorem weierstrass_test {α : Type*} {u : ℕ → α → ℝ} {E : Set α} {M : ℕ → ℝ}
    (hM : ∀ n, 0 ≤ M n) (hs : SeriesConverges M)
    (hb : ∀ n, ∀ x ∈ E, |u n x| ≤ M n) :
    (∀ x ∈ E, AbsolutelyConvergent (fun n => u n x)) ∧
    TendstoUniformlyOn (fun N x => partialSum (fun n => u n x) N)
      (fun x => ∑' n, u n x) atTop E := by
  have h := (positive_series_summable hM).1 hs
  refine ⟨fun x hx => (positive_series_summable (fun n => abs_nonneg (u n x))).2 ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun n => abs_nonneg (u n x)) (fun n => hb n x hx) h
  · exact tendstoUniformlyOn_tsum_nat h (fun n x hx => by simpa [Real.norm_eq_abs] using hb n x hx)

theorem absolute_rearrangement {a : ℕ → ℝ} {s : ℝ}
    (ha : AbsolutelyConvergent a) (hs : SeriesHasSum a s) (σ : ℕ ≃ ℕ) :
    SeriesHasSum (a ∘ σ) s := by
  have h := (positive_series_summable (fun n => abs_nonneg (a n))).1 ha
  have hsumm : Summable a := summable_norm_iff.mp (by simpa [Real.norm_eq_abs] using h)
  have he : (∑' n, a n) = s := tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat hs
  have hsum : HasSum a s := he ▸ hsumm.hasSum
  exact (σ.hasSum_iff.mpr hsum).tendsto_sum_nat

theorem positive_comparison {a b : ℕ → ℝ} {N : ℕ}
    (h : ∀ n ≥ N, 0 ≤ a n ∧ a n ≤ b n) :
    SeriesConverges b → SeriesConverges a := by
  rintro ⟨s,hs⟩
  let A := fun n => a (n+N)
  let B := fun n => b (n+N)
  have hsum (c : ℕ → ℝ) (n : ℕ) :
      partialSum (fun k => c (k+N)) n = partialSum c (n+N) - partialSum c N := by
    induction n with
    | zero => simp [partialSum]
    | succ n ih =>
      rw [partialSum_succ, ih, show n+1+N = (n+N)+1 by omega, partialSum_succ]
      ring
  have ht : SeriesHasSum B (s-partialSum b N) := by
    apply ((hs.comp (tendsto_add_atTop_nat N)).sub_const (partialSum b N)).congr
    exact fun n => (hsum b n).symm
  have hB := (positive_series_summable (a := B) (fun n =>
    (h (n+N) (by omega)).1.trans (h (n+N) (by omega)).2)).1 ⟨_,ht⟩
  have hA : Summable A := Summable.of_nonneg_of_le (fun n => (h (n+N) (by omega)).1)
    (fun n => (h (n+N) (by omega)).2) hB
  have ha : Summable a := (summable_nat_add_iff N).1 hA
  exact ⟨_, ha.hasSum.tendsto_sum_nat⟩


theorem uniform_absolute_product {α : Type*} (F : ℕ → α → ℝ)
    (f : α → ℝ) (E : Set α) :
    Tendsto (fun p : ℕ × α => |F p.1 p.2-f p.2|)
      (atTop ×ˢ 𝓟 E) (𝓝 0) ↔ TendstoUniformlyOn F f atTop E := by
  rw [Metric.tendsto_nhds, uniform_on_iff]
  simp only [Real.dist_eq, sub_zero, abs_abs, eventually_prod_principal_iff, eventually_atTop]

theorem uniform_supremum_iff {α : Type*} {F : ℕ → α → ℝ} {f : α → ℝ}
    {E : Set α} (hE : E.Nonempty)
    (hb : ∀ N, BddAbove ((fun x => |F N x-f x|) '' E)) :
    TendstoUniformlyOn F f atTop E ↔
      Tendsto (fun N => sSup ((fun x => |F N x-f x|) '' E)) atTop (𝓝 0) := by
  let d := fun N => sSup ((fun x => |F N x-f x|) '' E)
  have point_le (N : ℕ) (x : α) (hx : x ∈ E) : |F N x-f x| ≤ d N :=
    le_csSup (hb N) ⟨x,hx,rfl⟩
  constructor
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨K,hK⟩ := (uniform_on_iff F f E).1 h (ε/2) (half_pos hε)
    refine ⟨K,fun N hN => ?_⟩
    have hd : d N ≤ ε/2 :=
      csSup_le (hE.image _) (by rintro _ ⟨x,hx,rfl⟩; exact (hK N hN x hx).le)
    obtain ⟨x,hx⟩ := hE
    have hnon := (abs_nonneg (F N x-f x)).trans (point_le N x hx)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon]
    exact hd.trans_lt (half_lt_self hε)
  · intro h
    exact uniform_of_error_bound h point_le

theorem uniform_cauchy_criterion {α : Type*} (F : ℕ → α → ℝ) (E : Set α) :
    (∃ f, TendstoUniformlyOn F f atTop E) ↔
    ∀ ε > 0, ∃ K, ∀ M ≥ K, ∀ N ≥ K, ∀ x ∈ E, |F M x-F N x| < ε := by
  classical
  constructor
  · rintro ⟨f,h⟩ ε hε
    obtain ⟨K,hK⟩ := (uniform_on_iff F f E).1 h (ε/2) (half_pos hε)
    refine ⟨K,fun M hM N hN x hx => ?_⟩
    have ht := abs_sub_le (F M x) (f x) (F N x)
    rw [abs_sub_comm (f x)] at ht
    linarith [hK M hM x hx,hK N hN x hx]
  · intro h
    have hc : UniformCauchySeqOn F atTop E := by
      apply Metric.uniformCauchySeqOn_iff.2
      simpa [Real.dist_eq] using h
    have hpoint (x : α) (hx : x ∈ E) : ∃ l, Tendsto (fun N => F N x) atTop (𝓝 l) := by
      apply cauchySeq_tendsto_of_complete
      apply Metric.cauchySeq_iff.2
      intro ε hε
      obtain ⟨K,hK⟩ := h ε hε
      exact ⟨K, fun M hM N hN => by simpa [Real.dist_eq] using hK M hM N hN x hx⟩
    let f := fun x => if hx : x ∈ E then (hpoint x hx).choose else 0
    refine ⟨f,hc.tendstoUniformlyOn_of_tendsto ?_⟩
    intro x hx
    simpa [f,hx] using (hpoint x hx).choose_spec

theorem integral_test_finite_bounds {f : ℝ → ℝ} {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hf : AntitoneOn f (Ici 1)) :
    (∫ x in (N:ℝ)..(M:ℝ), f x) ≤ ∑ n ∈ Finset.Ico N M, f n ∧
    (∑ n ∈ Finset.Ico N M, f (n+1 : ℕ)) ≤ ∫ x in (N:ℝ)..(M:ℝ), f x := by
  have hsub : Icc (N:ℝ) (M:ℝ) ⊆ Ici 1 := by
    intro x hx
    exact (show (1:ℝ) ≤ N by exact_mod_cast hN).trans hx.1
  exact ⟨(hf.mono hsub).integral_le_sum_Ico hNM, (hf.mono hsub).sum_le_integral_Ico hNM⟩

theorem geometric_sum_and_tail {q : ℝ} (hq : |q| < 1) :
    SeriesHasSum (fun n => q^n) (1/(1-q)) ∧
      ∀ N, seriesRemainder (fun n => q^n) (1/(1-q)) N = q^N/(1-q) ∧
        |seriesRemainder (fun n => q^n) (1/(1-q)) N| = |q|^N/|1-q| := by
  have hne : q ≠ 1 := by intro h; subst q; norm_num at hq
  refine ⟨by simpa [one_div] using geometric_series q hq, fun N => ?_⟩
  have he := geometric_remainder q hne N
  refine ⟨he,?_⟩
  rw [seriesRemainder, he, abs_div, abs_pow]

theorem exp_compact_remainder {x r : ℝ} (hx : |x| ≤ r) (n : ℕ) :
    |Real.exp x - partialSum (fun k => x^k / (k.factorial : ℝ)) (n+1)| ≤
      Real.exp r * r^(n+1)/((n+1).factorial : ℝ) := by
  have hb := Ch08.book_lagrange_bound (n := n) (a := 0) (x := x)
    (fun t _ => Real.contDiff_exp.contDiffAt)
    (fun t ht => by
      rw [Ch08.exp_iteratedDeriv, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_max_iff.mp ht.2).elim (fun h0 => h0.trans ((abs_nonneg x).trans hx))
        (fun h1 => h1.trans ((le_abs_self x).trans hx)))
  have he : Ch08.bookTaylor Real.exp n 0 x =
      partialSum (fun k => x^k / (k.factorial : ℝ)) (n+1) := by
    unfold Ch08.bookTaylor partialSum
    apply Finset.sum_congr rfl
    intro k _
    rw [Ch08.exp_iteratedDeriv, Real.exp_zero, sub_zero]
    ring
  rw [he, sub_zero] at hb
  refine hb.trans ?_
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hx _) (Real.exp_pos _).le)
    (by positivity)

theorem exp_series_and_bound (x : ℝ) :
    SeriesHasSum (fun n => x^n/(n.factorial : ℝ)) (Real.exp x) ∧
      ∀ r, |x| ≤ r → ∀ n : ℕ,
        |Real.exp x - partialSum (fun k => x^k/(k.factorial : ℝ)) (n+1)| ≤
          Real.exp r * r^(n+1)/((n+1).factorial : ℝ) :=
  ⟨exp_series x, fun _ hx n => exp_compact_remainder hx n⟩

end Ch11
