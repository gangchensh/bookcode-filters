import Textbook.Ch05.Sequences

namespace Ch11
open Filter
open scoped Topology BigOperators Uniformity

-- BEGIN definition
def partialSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, a k                          -- 前N项，下标为0到N-1

def SeriesHasSum (a : ℕ → ℝ) (s : ℝ) : Prop :=
  Tendsto (partialSum a) atTop (𝓝 s)                  -- 部分和沿自然数上尾趋于s

theorem partialSum_succ (a : ℕ → ℝ) (N : ℕ) :
    partialSum a (N+1) = partialSum a N + a N := by
  exact Finset.sum_range_succ a N                   -- 新增的第N项与旧部分和分开
-- END definition

theorem series_epsilon_iff (a : ℕ → ℝ) (s : ℝ) :
    SeriesHasSum a s ↔ ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, |partialSum a N - s| < ε :=
  (Ch05.converges_mathlib (partialSum a) s).symm.trans
    (Ch05.converges_iff (partialSum a) s)

-- BEGIN conditional
theorem ordered_mathlib_iff (a : ℕ → ℝ) (s : ℝ) :
    SeriesHasSum a s ↔ HasSum a s (SummationFilter.conditional ℕ) := by
  unfold SeriesHasSum partialSum HasSum
  rw [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl                                               -- 两边都是前N项部分和的极限
-- END conditional

-- BEGIN necessary
theorem term_tendsto_zero {a : ℕ → ℝ} {s : ℝ} (h : SeriesHasSum a s) :
    Tendsto a atTop (𝓝 0) := by
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  have hdiff := hshift.sub h                         -- 相邻部分和之差趋于s-s
  have heq : (fun N => partialSum a (N+1) - partialSum a N) = a := by
    funext N
    rw [partialSum_succ]
    ring
  simpa only [Function.comp_def, heq, sub_self] using hdiff
-- END necessary

-- BEGIN cauchy
theorem series_cauchy_iff (a : ℕ → ℝ) :
    (∃ s, SeriesHasSum a s) ↔ CauchySeq (partialSum a) := by
  constructor
  · rintro ⟨s, hs⟩
    exact hs.cauchySeq
  · intro h
    exact cauchySeq_tendsto_of_complete h             -- 完备性把部分和Cauchy性转成存在性
-- END cauchy

-- BEGIN geometric
theorem geometric_series (q : ℝ) (hq : |q| < 1) :
    SeriesHasSum (fun n => q^n) (1-q)⁻¹ := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs] using hq
  exact (hasSum_geometric_of_norm_lt_one hnorm).tendsto_sum_nat

theorem geometric_remainder (q : ℝ) (hq : q ≠ 1) (N : ℕ) :
    1/(1-q) - partialSum (fun n => q^n) N = q^N/(1-q) := by
  rw [partialSum, geom_sum_eq hq N]                   -- 先使用有限几何恒等式
  have hden : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  field_simp [hden]
  <;> ring
-- END geometric

-- BEGIN uniform
theorem geometric_uniform_bound (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx : |x| ≤ r) (N : ℕ) :
    |partialSum (fun n => x^n) N - 1/(1-x)| ≤ r^N/(1-r) := by
  have hxlt : x < 1 := lt_of_le_of_lt ((le_abs_self x).trans hx) hr1
  have hden : 0 < 1-x := sub_pos.mpr hxlt
  have hpower : |x|^N ≤ r^N := pow_le_pow_left₀ (abs_nonneg x) hx N
  calc
    |partialSum (fun n => x^n) N - 1/(1-x)| = |x|^N/(1-x) := by
      rw [abs_sub_comm, geometric_remainder x (ne_of_lt hxlt) N,
        abs_div, abs_pow, abs_of_pos hden]
    _ ≤ r^N/(1-x) := div_le_div_of_nonneg_right hpower (le_of_lt hden)
    _ ≤ r^N/(1-r) := by
      apply (div_le_div_iff₀ hden (sub_pos.mpr hr1)).2
      nlinarith [pow_nonneg hr0 N, (le_abs_self x).trans hx]
-- END uniform

-- BEGIN exponential
theorem exp_series (x : ℝ) :
    SeriesHasSum (fun n => x^n/(Nat.factorial n : ℝ)) (Real.exp x) := by
  have h : HasSum (fun n => x^n/(Nat.factorial n : ℝ)) (Real.exp x) := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp x)
  exact h.tendsto_sum_nat                            -- 绝对收敛的库级数也按自然顺序收敛
-- END exponential


-- BEGIN uniform_bridge
theorem uniform_on_iff {α : Type*} (F : ℕ → α → ℝ) (f : α → ℝ) (E : Set α) :
    TendstoUniformlyOn F f atTop E ↔
      ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ x ∈ E, |F N x - f x| < ε := by
  rw [Metric.tendstoUniformlyOn_iff]
  simp only [Real.dist_eq, abs_sub_comm, eventually_atTop] -- 同一个阈值控制全部x

theorem uniform_of_error_bound {α : Type*} {F : ℕ → α → ℝ}
    {f : α → ℝ} {E : Set α} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ N, ∀ x ∈ E, |F N x - f x| ≤ r N) :
    TendstoUniformlyOn F f atTop E := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  have he : ∀ᶠ N in atTop, r N < ε := hr.eventually (gt_mem_nhds hε)
  filter_upwards [he] with N hN x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (hbound N x hx).trans_lt hN                  -- 误差先不超过r_N，再小于ε
-- END uniform_bridge

-- BEGIN product_bridge
theorem uniform_product_iff {α : Type*} (F : ℕ → α → ℝ) (f : α → ℝ)
    (E : Set α) :
    TendstoUniformlyOn F f atTop E ↔
      Tendsto (fun p : ℕ × α => (f p.2, F p.1 p.2))
        (atTop ×ˢ 𝓟 E) (𝓤 ℝ) := by
  exact tendstoUniformlyOn_iff_tendsto              -- 积源要求N充分大且x位于E
-- END product_bridge

end Ch11

