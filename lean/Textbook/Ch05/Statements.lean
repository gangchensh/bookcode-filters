import Textbook.Ch05.Sequences
import Textbook.Ch04.Examples
import Textbook.Ch03.WorkedLimits

namespace Ch05Statements
open Ch05 Ch02 Ch03 Ch03Approach Ch03Rules Ch04

theorem quotient_converges_one : Converges (fun n => (n : ℝ)/(n+1)) 1 :=
  Ch03WorkedLimits.quotient_sequence

theorem alternating_bounded_not_convergent :
    BoundedSeq Ch04Examples.alternating ∧ ¬ ∃ l, Converges Ch04Examples.alternating l := by
  refine ⟨⟨1, fun n => ?_⟩, Ch04Examples.alternating_abs_limit.2⟩
  simp [Ch04Examples.alternating, abs_pow]

theorem eventually_half_positive {u : ℕ → ℝ} {l : ℝ} (hu : Converges u l) (hl : 0 < l) :
    ∃ N, ∀ n ≥ N, l/2 < u n := by
  obtain ⟨N,hN⟩ := (converges_iff u l).1 hu (l/2) (half_pos hl)
  exact ⟨N, fun n hn => by linarith [(abs_lt.mp (hN n hn)).1]⟩

theorem lower_bound_limit {u : ℕ → ℝ} {l c : ℝ} (hu : Converges u l)
    (h : Eventually tailFilter (fun n => c ≤ u n)) : c ≤ l :=
  limit_le tailFilter_proper (const_limit tailFilter c) hu h

theorem upper_bound_limit {u : ℕ → ℝ} {l c : ℝ} (hu : Converges u l)
    (h : Eventually tailFilter (fun n => u n ≤ c)) : l ≤ c :=
  limit_le tailFilter_proper hu (const_limit tailFilter c) h

def UpperBound (A : Set ℝ) (b : ℝ) : Prop := ∀ x ∈ A, x ≤ b

def HasUpperBound (A : Set ℝ) : Prop := ∃ b, UpperBound A b

def Supremum (A : Set ℝ) (s : ℝ) : Prop :=
  UpperBound A s ∧ ∀ b, UpperBound A b → s ≤ b

theorem real_supremum (A : Set ℝ) (hne : A.Nonempty) (hb : HasUpperBound A) :
    ∃ s, Supremum A s :=
  ⟨sSup A, isLUB_csSup hne hb⟩

theorem approximate_supremum {A : Set ℝ} {s ε : ℝ} (hs : Supremum A s) (hε : 0 < ε) :
    ∃ x ∈ A, s-ε < x ∧ x ≤ s := by
  by_contra h
  have hle := hs.2 (s-ε) (fun x hx => le_of_not_gt fun hlt => h ⟨x,hx,hlt,hs.1 x hx⟩)
  linarith

theorem quotient_supremum_not_member :
    Supremum (Set.range fun n : ℕ => (n : ℝ)/(n+1)) 1 ∧
      1 ∉ Set.range (fun n : ℕ => (n : ℝ)/(n+1)) := by
  have hlt (n : ℕ) : (n : ℝ)/(n+1) < 1 := (div_lt_iff₀ (by positivity)).2 (by linarith)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨n,rfl⟩
    exact (hlt n).le
  · intro b hb
    exact upper_bound_limit quotient_converges_one (eventually_of_forall fun n => hb _ (Set.mem_range_self n))
  · rintro ⟨n,hn⟩
    exact (ne_of_lt (hlt n)) hn

theorem nat_unbounded (x : ℝ) : ∃ n : ℕ, x < (n : ℝ) := exists_nat_gt x

def Nondecreasing (u : ℕ → ℝ) : Prop := ∀ m n, m ≤ n → u m ≤ u n

def Nonincreasing (u : ℕ → ℝ) : Prop := ∀ m n, m ≤ n → u n ≤ u m

def IsSubsequence (u v : ℕ → ℝ) : Prop := ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, v n = u (φ n)

theorem geometric_zero (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : Converges (fun n => q^n) 0 :=
  (converges_mathlib _ _).2 (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)

theorem nat_sequence_not_convergent : StrictMono (fun n : ℕ => (n : ℝ)) ∧
    ¬ ∃ l, Converges (fun n : ℕ => (n : ℝ)) l := by
  refine ⟨fun m n h => by change (m : ℝ) < (n : ℝ); exact_mod_cast h, ?_⟩
  rintro ⟨l,hl⟩
  obtain ⟨M,hM⟩ := convergent_bounded hl
  obtain ⟨n,hn⟩ := exists_nat_gt M
  exact (not_le_of_gt hn) ((le_abs_self _).trans (hM n))

theorem tail_distance_cauchy {u r : ℕ → ℝ} (hr : Converges r 0)
    (h : ∀ n m, n ≤ m → |u m-u n| ≤ r n) : CauchySequence u ∧ ∃ l, Converges u l := by
  have hc : CauchySequence u := by
    intro ε hε
    obtain ⟨N,hN⟩ := (converges_iff r 0).1 hr ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hs (k) (hk : N ≤ k) : r k < ε := (le_abs_self _).trans_lt (by simpa using hN k hk)
    rcases le_total n m with hnm | hmn
    · exact (h n m hnm).trans_lt (hs n hn)
    · rw [abs_sub_comm]
      exact (h m n hmn).trans_lt (hs m hm)
  exact ⟨hc,cauchy_converges hc⟩

theorem tail_distance_limit {u r : ℕ → ℝ} {l : ℝ} (hu : Converges u l)
    (h : ∀ n m, n ≤ m → |u m-u n| ≤ r n) : ∀ n, |u n-l| ≤ r n := by
  intro n
  rw [abs_sub_comm]
  exact upper_bound_limit (limit_abs (limit_sub hu (const_limit tailFilter (u n))))
    ⟨n, fun m hm => h n m hm⟩

theorem nested_interval {a b : ℕ → ℝ} (hab : ∀ n, a n ≤ b n)
    (h : ∀ n, Set.Icc (a (n+1)) (b (n+1)) ⊆ Set.Icc (a n) (b n))
    (hw : Converges (fun n => b n-a n) 0) : ∃! c, ∀ n, c ∈ Set.Icc (a n) (b n) := by
  have ha : Monotone a := monotone_nat_of_le_succ fun n => (h n ⟨le_rfl,hab (n+1)⟩).1
  have hb : Antitone b := antitone_nat_of_succ_le fun n => (h n ⟨hab (n+1),le_rfl⟩).2
  obtain ⟨c,hc⟩ := nested_interval_point a b hab ha hb
  exact ⟨c,hc,fun d hd => nested_interval_unique a b d c hd hc hw⟩

theorem monotone_subsequence (u : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (Monotone (u ∘ φ) ∨ Antitone (u ∘ φ)) := by
  classical
  let peak (n : ℕ) := ∀ m > n, u m ≤ u n
  by_cases hp : ∀ n, ∃ m > n, peak m
  · let step n := Classical.choose (hp n)
    let φ : ℕ → ℕ := fun n => Nat.rec (step 0) (fun _ k => step k) n
    have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun n => (Classical.choose_spec (hp (φ n))).1
    have hpeak : ∀ n, peak (φ n) := by
      intro n
      cases n with
      | zero => exact (Classical.choose_spec (hp 0)).2
      | succ n => exact (Classical.choose_spec (hp (φ n))).2
    refine ⟨φ,hφ,Or.inr ?_⟩
    intro m n hmn
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · rfl
    · exact hpeak m (φ n) (hφ hlt)
  · push Not at hp
    obtain ⟨N,hN⟩ := hp
    have hs (n : ℕ) : ∃ m > max n (N+1), u (max n (N+1)) < u m := by
      have hn : ¬ peak (max n (N+1)) := hN _ (by omega)
      unfold peak at hn
      push Not at hn
      exact hn
    let step n := Classical.choose (hs n)
    let φ : ℕ → ℕ := fun n => Nat.rec (N+1) (fun _ k => step k) n
    have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun n =>
      (le_max_left (φ n) (N+1)).trans_lt (Classical.choose_spec (hs (φ n))).1
    have hbound (n : ℕ) : N+1 ≤ φ n := hφ.monotone (Nat.zero_le n)
    refine ⟨φ,hφ,Or.inl (monotone_nat_of_le_succ fun n => ?_)⟩
    have hh := (Classical.choose_spec (hs (φ n))).2
    calc
      u (φ n) = u (max (φ n) (N+1)) := congrArg u (max_eq_left (hbound n)).symm
      _ ≤ u (φ (n+1)) := hh.le

theorem geometric_contraction {u : ℕ → ℝ} (C q : ℝ) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, |u (n+1)-u n| ≤ C*q^n) :
    ∃ l, Converges u l ∧ ∀ n, |u n-l| ≤ C*q^n/(1-q) := by
  have hpos : 0 < 1-q := by linarith
  have hb (n k : ℕ) : |u (n+k)-u n| ≤ C*q^n*(1-q^k)/(1-q) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        |u (n+(k+1))-u n| = |(u (n+k+1)-u (n+k))+(u (n+k)-u n)| := by
          change |u (n+k+1)-u n| = |(u (n+k+1)-u (n+k))+(u (n+k)-u n)|
          congr 1; ring
        _ ≤ |u (n+k+1)-u (n+k)| + |u (n+k)-u n| := abs_add_le _ _
        _ ≤ C*q^(n+k) + C*q^n*(1-q^k)/(1-q) := add_le_add (h _) ih
        _ = C*q^n*(1-q^(k+1))/(1-q) := by
          rw [pow_add,pow_succ]
          field_simp [hpos.ne']; ring
  have ht (n m : ℕ) (hnm : n ≤ m) : |u m-u n| ≤ C*q^n/(1-q) := by
    have he := hb n (m-n)
    rw [Nat.add_sub_of_le hnm] at he
    exact he.trans (div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) (by linarith [pow_nonneg hq (m-n)])) hpos.le)
  have hz : Converges (fun n => C*q^n/(1-q)) 0 := by
    have he := limit_const_mul (C/(1-q)) (geometric_zero q hq hq1)
    have hEq (n : ℕ) : C/(1-q)*q^n = C*q^n/(1-q) := by ring
    apply approaches_congr (eventually_of_forall hEq)
    simpa only [mul_zero] using he
  obtain ⟨l,hl⟩ := (tail_distance_cauchy hz ht).2
  exact ⟨l,hl,tail_distance_limit hl ht⟩

end Ch05Statements
