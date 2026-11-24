import Textbook.Ch05.Statements
import Textbook.Ch05.ClosedIntervals
import Textbook.Ch05.Recursion

namespace Ch05Examples
open Ch05 Ch05Statements Ch05ClosedIntervals Ch02 Ch03Approach Ch03Rules Ch04

noncomputable def averageIteration : ℕ → ℝ
  | 0 => 0
  | n+1 => (averageIteration n+2)/2

theorem average_iteration :
    (∀ n, 0 ≤ averageIteration n ∧ averageIteration n ≤ 2) ∧
      Monotone averageIteration ∧ Converges averageIteration 2 := by
  have h (n : ℕ) : 0 ≤ averageIteration n ∧ averageIteration n ≤ 2 := by
    induction n with
    | zero => norm_num [averageIteration]
    | succ n ih =>
      rw [averageIteration]
      exact ⟨by linarith [ih.1],by linarith [ih.2]⟩
  refine ⟨h, monotone_nat_of_le_succ fun n => ?_, ?_⟩
  · rw [averageIteration]
    linarith [(h n).2]
  · have he (n : ℕ) : averageIteration n = 2-2*(1/2:ℝ)^n := by
      induction n with
      | zero => norm_num [averageIteration]
      | succ n ih => rw [averageIteration, ih, pow_succ]; ring
    apply approaches_congr (eventually_of_forall fun n => (he n).symm)
    simpa only [mul_zero, sub_zero] using limit_sub (const_limit tailFilter 2)
      (limit_const_mul 2 (geometric_zero (1/2) (by norm_num) (by norm_num)))

noncomputable def squareRecursion : ℕ → ℝ
  | 0 => 0
  | n+1 => Real.sqrt (2+squareRecursion n)

theorem sqrt_recursion_converges :
    (∀ n, 0 ≤ squareRecursion n ∧ squareRecursion n ≤ 2) ∧
      Monotone squareRecursion ∧ Converges squareRecursion 2 := by
  have hb (n : ℕ) : 0 ≤ squareRecursion n ∧ squareRecursion n ≤ 2 := by
    induction n with
    | zero => norm_num [squareRecursion]
    | succ n ih =>
      rw [squareRecursion]
      exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left (by norm_num)).2 (by linarith [ih.2])⟩
  have hm : Monotone squareRecursion := by
    apply monotone_nat_of_le_succ
    intro n
    induction n with
    | zero => exact (hb 1).1
    | succ n ih =>
      change Real.sqrt (2+squareRecursion n) ≤ Real.sqrt (2+squareRecursion (n+1))
      exact Real.sqrt_le_sqrt (by linarith)
  have hba : BddAbove (Set.range squareRecursion) := ⟨2, by rintro _ ⟨n,rfl⟩; exact (hb n).2⟩
  let l := sSup (Set.range squareRecursion)
  have hl : Converges squareRecursion l := monotone_bounded_converges hm hba
  have hl0 : 0 ≤ l := lower_bound_limit hl (eventually_of_forall fun n => (hb n).1)
  have hs : Converges (fun n => squareRecursion (n+1)) l :=
    converges_subsequence (φ := fun n => n+1) hl (by intro m n h; change m+1 < n+1; omega)
  have ht := Ch04Statements.limit_into_continuous (limit_add (const_limit tailFilter 2) hl)
    ((Ch04Continuity.continuous_mathlib _ _).2 Real.continuous_sqrt.continuousAt)
  have he : l = Real.sqrt (2+l) := real_limit_unique tailFilter_proper hs ht
  have hsq : l^2 = 2+l := by conv_lhs => rw [he]; exact Real.sq_sqrt (by linarith)
  have hfac : (l-2)*(l+1) = 0 := by nlinarith
  have h2 : l = 2 := by rcases mul_eq_zero.mp hfac with hh | hh <;> linarith
  exact ⟨hb,hm,h2 ▸ hl⟩

noncomputable def alternatingSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), (-1/2:ℝ)^k

theorem geometric_partial_sum_limit : Converges alternatingSum (2/3) := by
  have hpow : Converges (fun n : ℕ => (-1/2:ℝ)^(n+1)) 0 := by
    apply (converges_mathlib _ _).2
    exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(-1/2:ℝ)| < 1)).comp
      (show Filter.Tendsto (fun n : ℕ => n+1) Filter.atTop Filter.atTop from
        (Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id))
  have he (n : ℕ) : (0-(-1/2:ℝ)^(n+1) + 1) * (2/3) = alternatingSum n := by
    unfold alternatingSum
    rw [geom_sum_eq (by norm_num : (-1/2:ℝ) ≠ 1)]
    ring
  apply approaches_congr (eventually_of_forall he)
  convert limit_mul (limit_add (limit_sub (const_limit tailFilter 0) hpow) (const_limit tailFilter 1))
    (const_limit tailFilter (2/3)) using 1 <;> norm_num

theorem alternating_subsequences :
    StrictMono (fun n : ℕ => 2*n) ∧ StrictMono (fun n : ℕ => 2*n+1) ∧
    Converges (fun n => Ch04Examples.alternating (2*n)) 1 ∧
    Converges (fun n => Ch04Examples.alternating (2*n+1)) (-1) ∧
    ¬ ∃ l, Converges Ch04Examples.alternating l := by
  refine ⟨by intro m n h; change 2*m < 2*n; omega,
    by intro m n h; change 2*m+1 < 2*n+1; omega, ?_, ?_, alternating_bounded_not_convergent.2⟩
  · exact approaches_congr (eventually_of_forall fun n => by norm_num [Ch04Examples.alternating,pow_mul])
      (const_limit tailFilter 1)
  · exact approaches_congr (eventually_of_forall fun n => by norm_num [Ch04Examples.alternating,pow_add,pow_mul])
      (const_limit tailFilter (-1))

noncomputable def flipIteration : ℕ → ℝ
  | 0 => 0
  | n+1 => 1 - flipIteration n

theorem fixed_point_trap : (∀ l : ℝ, l = 1-l ↔ l = 1/2) ∧
    ¬ ∃ l, Converges flipIteration l := by
  refine ⟨fun l => ⟨fun h => by linarith,fun h => by linarith⟩, ?_⟩
  have hp (n : ℕ) : flipIteration n = (1-Ch04Examples.alternating n)/2 := by
    induction n with
    | zero => norm_num [flipIteration,Ch04Examples.alternating]
    | succ n ih => simp only [flipIteration, ih, Ch04Examples.alternating, pow_succ]; ring
  rintro ⟨l,hl⟩
  apply alternating_bounded_not_convergent.2
  have he (n : ℕ) : 1 - 2 * flipIteration n = Ch04Examples.alternating n := by
    rw [hp]; ring
  exact ⟨1-2*l, approaches_congr (eventually_of_forall he)
    (limit_sub (const_limit tailFilter 1) (limit_const_mul 2 hl))⟩

noncomputable def harmonicSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1/((k:ℝ)+1)

theorem harmonic_adjacent_not_cauchy :
    Converges (fun n => |harmonicSum (n+1)-harmonicSum n|) 0 ∧
      ¬ CauchySequence harmonicSum := by
  constructor
  · apply approaches_congr (eventually_of_forall fun n => ?_) Ch03Approach.reciprocal_sequence
    simp [harmonicSum,Finset.sum_range_succ,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1)]
  · intro hc
    obtain ⟨M,hM⟩ := cauchy_bounded hc
    have htop := (Filter.tendsto_atTop.1 Real.tendsto_sum_range_one_div_nat_succ_atTop) (M+1)
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 htop
    have hlow : M+1 ≤ harmonicSum N := hN N le_rfl
    linarith [(le_abs_self (harmonicSum N)).trans (hM N)]

noncomputable def squareReciprocalSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1/((k:ℝ)+1)^2

theorem square_reciprocal_sum_converges : ∃ l, Converges squareReciprocalSum l := by
  have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have h : Summable (fun n : ℕ => 1/(n:ℝ)^2) := (Real.summable_one_div_nat_pow).2 (by norm_num)
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).2 h
  exact ⟨_,(converges_mathlib _ _).2 hs.hasSum.tendsto_sum_nat⟩

theorem square_uniform_bounded (R : ℝ) (hR : 0 < R) :
    UniformlyContinuous (fun x => x^2) (Set.Icc (-R) R) := by
  intro ε hε
  refine ⟨ε/(2*R), by positivity, fun x hx y hy hxy => ?_⟩
  have hsum : |x+y| ≤ 2*R := abs_le.mpr ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
  rw [show x^2-y^2 = (x-y)*(x+y) by ring, abs_mul]
  exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans_lt ((lt_div_iff₀ (by positivity)).1 hxy)

theorem square_not_uniform : ¬ UniformlyContinuous (fun x => x^2) Set.univ := by
  intro h
  obtain ⟨δ,hδ,h⟩ := h 2 (by norm_num)
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (1/δ))
  have hn0 : 0 < (n:ℝ) := by linarith [(le_max_left 1 (1/δ)).trans_lt hn]
  have hr : 1/(n:ℝ) < δ := (one_div_lt hn0 hδ).2 ((le_max_right 1 (1/δ)).trans_lt hn)
  have hx : |(n:ℝ)-((n:ℝ)+1/n)| < δ := by
    rw [show (n:ℝ)-((n:ℝ)+1/n) = -(1/n) by ring, abs_neg, abs_of_pos (one_div_pos.mpr hn0)]
    exact hr
  have hbad := h n (Set.mem_univ _) ((n:ℝ)+1/n) (Set.mem_univ _) hx
  have he : ((n:ℝ)+1/n)^2-(n:ℝ)^2 = 2+(1/(n:ℝ))^2 := by field_simp [hn0.ne']; ring
  linarith [(abs_lt.mp hbad).1,sq_nonneg (1/(n:ℝ))]

noncomputable def newtonSqrt : ℕ → ℝ
  | 0 => 2
  | n+1 => Ch05Recursion.sqrtTwoStep (newtonSqrt n)

theorem newton_sqrt_limit : (∀ n, Real.sqrt 2 ≤ newtonSqrt n) ∧
    Antitone newtonSqrt ∧ Converges newtonSqrt (Real.sqrt 2) := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hb (n : ℕ) : Real.sqrt 2 ≤ newtonSqrt n := by
    induction n with
    | zero => change Real.sqrt 2 ≤ 2; nlinarith
    | succ n ih =>
      have hpos := hs.trans_le ih
      have hres := Ch05Recursion.sqrtTwoStep_residual (newtonSqrt n) hpos.ne'
      have hnonneg : 0 ≤ Ch05Recursion.sqrtTwoStep (newtonSqrt n) := by unfold Ch05Recursion.sqrtTwoStep; positivity
      have hsqge : 2 ≤ (Ch05Recursion.sqrtTwoStep (newtonSqrt n))^2 := by
        linarith [show 0 ≤ (newtonSqrt n ^ 2 - 2)^2/(4*newtonSqrt n^2) by positivity]
      change Real.sqrt 2 ≤ Ch05Recursion.sqrtTwoStep (newtonSqrt n)
      exact (Real.sqrt_le_iff).2 ⟨hnonneg,hsqge⟩
  have hm : Antitone newtonSqrt := antitone_nat_of_succ_le fun n =>
    Ch05Recursion.sqrtTwoStep_le _ (hs.trans_le (hb n))
      (by nlinarith [mul_nonneg (sub_nonneg.mpr (hb n)) (show 0 ≤ newtonSqrt n + Real.sqrt 2 by linarith [hb n])])
  have hneg : Monotone (fun n => -newtonSqrt n) := fun m n hmn => neg_le_neg (hm hmn)
  have hbound : BddAbove (Set.range fun n => -newtonSqrt n) := ⟨-Real.sqrt 2, by
    rintro _ ⟨n,rfl⟩; exact neg_le_neg (hb n)⟩
  let l := -sSup (Set.range fun n => -newtonSqrt n)
  have hl : Converges newtonSqrt l := by
    simpa only [Converges, l, neg_neg] using limit_neg (monotone_bounded_converges hneg hbound)
  have hl0 := hs.trans_le (lower_bound_limit hl (eventually_of_forall hb))
  have hnext : Converges (fun n => newtonSqrt (n+1)) l :=
    converges_subsequence (φ := fun n => n+1) hl (by intro m n h; change m+1 < n+1; omega)
  have ht : Converges (fun n => Ch05Recursion.sqrtTwoStep (newtonSqrt n)) ((l+2/l)/2) :=
    limit_div (limit_add hl (limit_div (const_limit tailFilter 2) hl hl0.ne'))
      (const_limit tailFilter 2) (by norm_num)
  have he := real_limit_unique tailFilter_proper hnext ht
  change l = (l+2/l)/2 at he
  field_simp [hl0.ne'] at he
  have heq : l = Real.sqrt 2 := by
    have hf : (l-Real.sqrt 2)*(l+Real.sqrt 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h <;> linarith
  exact ⟨hb,hm,heq ▸ hl⟩

end Ch05Examples
