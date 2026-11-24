import Textbook.Ch03.LimitRules

open scoped Topology

namespace Ch05
open Ch02 Ch03Approach

def Converges (u : ℕ → ℝ) (l : ℝ) : Prop :=           -- 复用第3章的滤子数列极限
  Approaches u tailFilter (neighborhoodFilter l)

def BoundedSeq (u : ℕ → ℝ) : Prop :=                  -- 一个共同常数控制全部数列项
  ∃ M : ℝ, ∀ n : ℕ, |u n| ≤ M

def CauchySequence (u : ℕ → ℝ) : Prop :=              -- 充分靠后的任意两项彼此接近
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |u m-u n| < ε

theorem converges_iff (u : ℕ → ℝ) (l : ℝ) :           -- 调用已有ε-N判定，不重新定义极限
    Converges u l ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n-l| < ε :=
  sequence_iff u l

theorem converges_mathlib (u : ℕ → ℝ) (l : ℝ) :       -- 本书收敛与Mathlib Tendsto对应
    Converges u l ↔ Filter.Tendsto u Filter.atTop (nhds l) := by
  unfold Converges
  rw [approaches_mathlib_iff, toMathlib_tail, toMathlib_neighborhood]

theorem finite_prefix_bound (u : ℕ → ℝ) (N : ℕ) :     -- 有限个初始项具有共同的非负界
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n < N, |u n| ≤ M := by
  induction N with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ N ih =>
    rcases ih with ⟨M, hM, hbound⟩
    refine ⟨M+|u N|, by positivity, ?_⟩             -- 把第N项的绝对值加入旧界
    intro n hn
    by_cases h : n < N
    · exact le_trans (hbound n h) (le_add_of_nonneg_right (abs_nonneg _))
    · have : n = N := by omega
      subst n
      linarith

theorem bounded_of_eventual_bound {u : ℕ → ℝ} {C : ℝ}
    (h : ∃ N, ∀ n ≥ N, |u n| ≤ C) : BoundedSeq u := by  -- 将最终有界补成整体有界
  rcases h with ⟨N, htail⟩
  rcases finite_prefix_bound u N with ⟨M, hM, hprefix⟩
  refine ⟨max M C, ?_⟩                               -- 同时覆盖有限前段与无限尾部
  intro n
  by_cases hn : n < N
  · exact (hprefix n hn).trans (le_max_left _ _)
  · exact (htail n (by omega)).trans (le_max_right _ _)

theorem convergent_bounded {u : ℕ → ℝ} {l : ℝ}
    (hu : Converges u l) : BoundedSeq u := by          -- 收敛数列的全部项有界
  rcases (converges_iff u l).1 hu 1 zero_lt_one with ⟨N, hN⟩
  apply bounded_of_eventual_bound (C := 1 + |l|)
  refine ⟨N, ?_⟩
  intro n hn
  have hdist := hN n hn
  calc
    |u n| = |(u n-l)+l| := by rw [sub_add_cancel]
    _ ≤ |u n-l|+|l| := abs_add_le _ _
    _ ≤ 1+|l| := by linarith                         -- 取ε=1控制整个尾部

theorem eventually_positive {u : ℕ → ℝ} {l : ℝ}
    (hu : Converges u l) (hl : 0 < l) :
    Eventually tailFilter (fun n => 0 < u n) := by     -- 正极限使数列最终为正
  rcases (converges_iff u l).1 hu (l/2) (half_pos hl) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h := (abs_lt.mp (hN n hn)).1                  -- -l/2<u_n-l
  change 0 < u n
  linarith

theorem index_ge {φ : ℕ → ℕ} (hφ : StrictMono φ) :    -- 严格递增自然数索引满足n≤φ(n)
    ∀ n, n ≤ φ n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))

theorem subsequence_index {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Approaches φ tailFilter tailFilter := by          -- 子列索引把充分大传到充分大
  rintro V ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact hN (φ n) (hn.trans (index_ge hφ n))

theorem converges_subsequence {u : ℕ → ℝ} {l : ℝ} {φ : ℕ → ℕ}
    (hu : Converges u l) (hφ : StrictMono φ) :
    Converges (fun n => u (φ n)) l :=                 -- 复合两个趋近关系得到子列收敛
  Ch03Rules.approaches_comp (subsequence_index hφ) hu

theorem monotone_limit_of_isLUB {u : ℕ → ℝ} {l : ℝ}
    (hu : Monotone u) (hl : IsLUB (Set.range u) l) :
    Converges u l := by                              -- 单调数列收敛到值域的上确界
  apply (converges_iff u l).2
  intro ε hε
  have hnear : ∃ N, l-ε < u N := by
    by_contra h
    push Not at h
    have hle : l ≤ l-ε := hl.2 (by rintro y ⟨n, rfl⟩; exact h n)
    linarith                                         -- l-ε不能仍是上界
  rcases hnear with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hupper : u n ≤ l := hl.1 (Set.mem_range_self n)
  have hlower : u N ≤ u n := hu hn
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]          -- |u_n-l|=l-u_n
  linarith

theorem monotone_bounded_converges {u : ℕ → ℝ}
    (hu : Monotone u) (hb : BddAbove (Set.range u)) :
    Converges u (sSup (Set.range u)) :=               -- 在此调用实数的上确界性质
  monotone_limit_of_isLUB hu (isLUB_csSup (Set.range_nonempty u) hb)

theorem convergent_cauchy {u : ℕ → ℝ} {l : ℝ}
    (hu : Converges u l) : CauchySequence u := by      -- 收敛推出Cauchy不需要再次调用完备性
  intro ε hε
  rcases (converges_iff u l).1 hu (ε/2) (half_pos hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  calc
    |u m-u n| = |(u m-l)+(l-u n)| := by congr 1; ring
    _ ≤ |u m-l|+|l-u n| := abs_add_le _ _
    _ = |u m-l|+|u n-l| := by rw [abs_sub_comm l (u n)]
    _ < ε := by linarith [hN m hm, hN n hn]

theorem cauchy_mathlib (u : ℕ → ℝ) :                 -- 与库的CauchySeq核对量词及距离
    CauchySequence u ↔ CauchySeq u := by
  simpa only [CauchySequence, Real.dist_eq] using
    (Metric.cauchySeq_iff (u := u)).symm

theorem bounded_subsequence {u : ℕ → ℝ} (hu : BoundedSeq u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l, Converges (fun n => u (φ n)) l := by
  rcases hu with ⟨M, hM⟩                             -- 值域包含于闭区间[-M,M]
  have hmem : ∀ n, u n ∈ Set.Icc (-M) M := fun n => abs_le.mp (hM n)
  rcases tendsto_subseq_of_bounded (Metric.isBounded_Icc (-M) M) hmem with
    ⟨l, hl, φ, hφ, hlim⟩                             -- 复用库中有界数列的子列定理
  exact ⟨φ, hφ, l, (converges_mathlib _ _).2 hlim⟩

theorem cauchy_bounded {u : ℕ → ℝ} (hu : CauchySequence u) :
    BoundedSeq u := by                               -- 固定一个尾项控制全部尾部
  rcases hu 1 zero_lt_one with ⟨N, hN⟩
  apply bounded_of_eventual_bound (C := 1 + |u N|)
  refine ⟨N, ?_⟩
  intro n hn
  calc
    |u n| = |(u n-u N)+u N| := by rw [sub_add_cancel]
    _ ≤ |u n-u N|+|u N| := abs_add_le _ _
    _ ≤ 1+|u N| := by linarith [hN n hn N le_rfl]

theorem cauchy_subsequence_limit {u : ℕ → ℝ} {l : ℝ} {φ : ℕ → ℕ}
    (hu : CauchySequence u) (hφ : StrictMono φ)
    (hsub : Converges (fun k => u (φ k)) l) : Converges u l := by
  apply (converges_iff u l).2                         -- Cauchy数列的一个收敛子列确定全列极限
  intro ε hε
  rcases hu (ε/2) (half_pos hε) with ⟨N, hN⟩
  rcases (converges_iff _ l).1 hsub (ε/2) (half_pos hε) with ⟨K, hK⟩
  let k := max N K
  have hkN : N ≤ φ k := (le_max_left N K).trans (index_ge hφ k)
  have hkK : K ≤ k := le_max_right N K
  refine ⟨N, ?_⟩                                    -- 全列阈值仍取N
  intro n hn
  calc
    |u n-l| = |(u n-u (φ k))+(u (φ k)-l)| := by congr 1; ring
    _ ≤ |u n-u (φ k)|+|u (φ k)-l| := abs_add_le _ _
    _ < ε := by linarith [hN n hn (φ k) hkN, hK k hkK]

theorem cauchy_converges {u : ℕ → ℝ} (hu : CauchySequence u) :
    ∃ l, Converges u l := by                         -- 按有界、选子列、恢复全列的路线证明
  rcases bounded_subsequence (cauchy_bounded hu) with ⟨φ, hφ, l, hl⟩
  exact ⟨l, cauchy_subsequence_limit hu hφ hl⟩

theorem cauchy_converges_library {u : ℕ → ℝ} (hu : CauchySequence u) :
    ∃ l, Converges u l := by                         -- 另一写法直接调用完备空间接口
  rcases cauchySeq_tendsto_of_complete ((cauchy_mathlib u).1 hu) with ⟨l, hl⟩
  exact ⟨l, (converges_mathlib u l).2 hl⟩

theorem cauchy_iff_convergent (u : ℕ → ℝ) :           -- 实数数列的Cauchy判据
    CauchySequence u ↔ ∃ l, Converges u l := by
  constructor
  · exact cauchy_converges
  · rintro ⟨l, hl⟩
    exact convergent_cauchy hl

theorem nested_interval_point (a b : ℕ → ℝ)
    (hab : ∀ n, a n ≤ b n) (ha : Monotone a) (hb : Antitone b) :
    ∃ c : ℝ, ∀ n, a n ≤ c ∧ c ≤ b n := by           -- 嵌套非空有界闭区间有公共点
  have hcross : ∀ m n, a m ≤ b n := by
    intro m n
    rcases le_total m n with h | h                   -- 固定右端点，比较任意左端点
    · exact (ha h).trans (hab n)
    · exact (hab m).trans (hb h)
  have hbound : BddAbove (Set.range a) := by
    refine ⟨b 0, ?_⟩                                -- b_0是全部左端点的共同上界
    rintro y ⟨m, rfl⟩
    exact hcross m 0
  have hsup := isLUB_csSup (Set.range_nonempty a) hbound
  refine ⟨sSup (Set.range a), ?_⟩                    -- 公共点取左端点值域的上确界
  intro n
  constructor
  · exact hsup.1 (Set.mem_range_self n)              -- a_n≤sup(range a)
  · apply hsup.2                                    -- 每个b_n都是同一值域的上界
    rintro y ⟨m, rfl⟩
    exact hcross m n

theorem nested_interval_unique (a b : ℕ → ℝ) (c d : ℝ)
    (hc : ∀ n, a n ≤ c ∧ c ≤ b n) (hd : ∀ n, a n ≤ d ∧ d ≤ b n)
    (hwidth : Converges (fun n => b n-a n) 0) : c = d := by
  by_contra hne                                     -- 两个不同公共点的距离为正
  have hpos : 0 < |c-d| := abs_pos.mpr (sub_ne_zero.mpr hne)
  rcases (converges_iff _ 0).1 hwidth (|c-d|/2) (half_pos hpos) with ⟨N, hN⟩
  have hlen := hN N le_rfl
  simp only [sub_zero] at hlen
  have hdist : |c-d| ≤ b N-a N := by
    apply abs_le.mpr
    constructor <;> linarith [(hc N).1, (hc N).2, (hd N).1, (hd N).2]
  have hsmall := lt_of_le_of_lt (le_abs_self (b N-a N)) hlen
  linarith                                           -- 距离≤区间长度<距离/2，矛盾

end Ch05
