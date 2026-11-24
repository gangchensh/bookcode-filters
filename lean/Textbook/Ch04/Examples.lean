import Textbook.Ch04.Statements
import Textbook.Ch03.Examples

namespace Ch04Examples
open Ch02 Ch03 Ch03Approach Ch03Rules Ch04 Ch04Continuity Ch04Statements

private theorem punctured_id (a : ℝ) : FiniteLimit id (punctured a) a :=
  approaches_within_source _ (approaches_id _)

private theorem right_id (a : ℝ) : FiniteLimit id (rightNear a) a :=
  approaches_within_source _ (approaches_id _)

private theorem left_id (a : ℝ) : FiniteLimit id (leftNear a) a :=
  approaches_within_source _ (approaches_id _)

private theorem reciprocal_top : FiniteLimit (fun x : ℝ => 1/x) (upperFilter ℝ) 0 :=
  Ch04Infinity.reciprocal_upper_zero (approaches_id _)

noncomputable abbrev reciprocalSequence (n : ℕ) : ℝ := 1 / ((n : ℝ)+1)

theorem quotient_at_one :
    FiniteLimit (fun x : ℝ => (x^2+1)/(x+2)) (punctured 1) (2/3) ∧
    FiniteLimit (fun x : ℝ => (x^2-1)/(x-1)) (punctured 1) 2 := by
  refine ⟨?_, ?_⟩
  · have hx := punctured_id 1
    simpa [id, FiniteLimit, one_add_one_eq_two, show (1:ℝ)+2 = 3 by norm_num] using
      limit_div (limit_add (limit_pow 2 hx) (const_limit _ 1))
      (limit_add hx (const_limit _ 2)) (by norm_num : (1:ℝ)+2 ≠ 0)
  · simpa using Ch03BasicExamples.quotient_punctured_from_definition 1

theorem right_sqrt_quotient :
    FiniteLimit (fun x : ℝ => (1+Real.sqrt x)/(2+x)) (rightNear 0) (1/2) := by
  have hs := approaches_within_source {x : ℝ | 0 < x} Ch03Statements.sqrt_limits_at_zero.2
  simpa [id, FiniteLimit, rightNear, nearWithin] using limit_div (limit_add (const_limit _ 1) hs)
    (limit_add (const_limit _ 2) (right_id 0)) (by norm_num : (2:ℝ)+0 ≠ 0)

noncomputable def alternating (n : ℕ) : ℝ := (-1 : ℝ)^n

theorem alternating_abs_limit :
    FiniteLimit (fun n => |alternating n|) tailFilter 1 ∧
      ¬ ∃ a, FiniteLimit alternating tailFilter a := by
  refine ⟨approaches_congr (eventually_of_forall fun n => ?_) (const_limit _ 1), ?_⟩
  · simp [alternating, abs_pow]
  · rintro ⟨a,ha⟩
    obtain ⟨N,hN⟩ := (sequence_iff _ _).1 ha 1 zero_lt_one
    have he := hN (2*N) (by omega)
    have ho := hN (2*N+1) (by omega)
    norm_num [alternating, pow_add, pow_mul] at he ho
    linarith [(abs_lt.mp he).2, (abs_lt.mp ho).1]

theorem max_min_sequence (u : ℕ → ℝ) (hu : FiniteLimit u tailFilter 0) :
    FiniteLimit (fun n => max (u n) 0) tailFilter 0 ∧
    FiniteLimit (fun n => min (u n) 0) tailFilter 0 ∧
    (∀ n, u n = max (u n) 0 + min (u n) 0) := by
  refine ⟨by simpa using limit_max hu (const_limit _ 0),
    by simpa using limit_min hu (const_limit _ 0), ?_⟩
  intro n
  by_cases hn : u n ≤ 0
  · simp [max_eq_right hn, min_eq_left hn]
  · have h := le_of_lt (lt_of_not_ge hn)
    simp [max_eq_left h, min_eq_right h]

theorem strict_order_lost :
    (∀ n, 0 < reciprocalSequence n) ∧
      FiniteLimit (fun _ : ℕ => 0) tailFilter 0 ∧ FiniteLimit reciprocalSequence tailFilter 0 :=
  ⟨fun _ => by positivity, const_limit _ 0, reciprocal_sequence⟩

theorem sine_sequence_squeeze :
    FiniteLimit (fun n : ℕ => Real.sin n / ((n : ℝ)+1)) tailFilter 0 := by
  have hr := reciprocal_sequence
  apply limit_squeeze (by simpa only [neg_zero] using limit_neg hr) hr <;> apply eventually_of_forall
  · intro n
    rw [show -(1 / ((n : ℝ)+1)) = -1 / ((n : ℝ)+1) by ring]
    exact div_le_div_of_nonneg_right (Real.neg_one_le_sin _) (by positivity)
  · intro n
    exact div_le_div_of_nonneg_right (Real.sin_le_one _) (by positivity)

theorem cosine_top_squeeze :
    FiniteLimit (fun x : ℝ => Real.cos x / x) (upperFilter ℝ) 0 := by
  apply limit_squeeze (by simpa only [neg_zero] using limit_neg reciprocal_top) reciprocal_top
  · refine ⟨1, fun x hx => ?_⟩
    change -(1/x) ≤ Real.cos x / x
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (Real.neg_one_le_cos _) (by linarith)
  · refine ⟨1, fun x hx => ?_⟩
    exact div_le_div_of_nonneg_right (Real.cos_le_one _) (by linarith)

theorem bounded_oscillation (v w : ℕ → ℝ) (hv : FiniteLimit v tailFilter 0)
    (hw : Eventually tailFilter (fun n => |w n| ≤ 5)) :
    FiniteLimit (fun n => w n * v n) tailFilter 0 :=
  bounded_mul_zero 5 (by norm_num) hw hv

theorem two_bounded_oscillations :
    FiniteLimit (fun n => alternating n * reciprocalSequence n) tailFilter 0 ∧
    FiniteLimit (fun n : ℕ => Real.sin ((n : ℝ)^2) * reciprocalSequence n) tailFilter 0 := by
  refine ⟨bounded_oscillation _ _ reciprocal_sequence (eventually_of_forall fun n => ?_),
    bounded_oscillation _ _ reciprocal_sequence (eventually_of_forall fun n => ?_)⟩
  · norm_num [alternating, abs_pow]
  · exact (Real.abs_sin_le_one _).trans (by norm_num)

theorem unbounded_products :
    (∀ n : ℕ, ((n : ℝ)+1) * reciprocalSequence n = 1) ∧
    FiniteLimit (fun n : ℕ => ((n : ℝ)+1) * (1 / ((n : ℝ)+1)^2)) tailFilter 0 := by
  have hpos (n : ℕ) : 0 < (n : ℝ)+1 := by positivity
  refine ⟨fun n => ?_, approaches_congr (eventually_of_forall fun n => ?_) reciprocal_sequence⟩
  · field_simp [(hpos n).ne']
  · field_simp [(hpos n).ne']

theorem center_discontinuous :
    FiniteLimit Ch03Statements.changedCenter (punctured 0) 0 ∧
      ¬ BookContinuousAt Ch03Statements.changedCenter 0 := by
  refine ⟨Ch03Statements.changed_center_limits.1, fun h => ?_⟩
  have hp := (continuous_punctured_iff _ _).1 h
  have he := real_limit_unique (Ch03Examples.punctured_proper 0)
    Ch03Statements.changed_center_limits.1 hp
  norm_num [Ch03Statements.changedCenter] at he

theorem radical_limit :
    FiniteLimit (fun x : ℝ => (Real.sqrt (1+x)-1)/x) (punctured 0) (1/2) := by
  have hx := punctured_id 0
  have h1x : FiniteLimit (fun x : ℝ => 1+x) (punctured 0) 1 := by
    simpa [id] using limit_add (const_limit _ 1) hx
  have hs := limit_into_continuous h1x ((continuous_mathlib _ _).2 Real.continuous_sqrt.continuousAt)
  have hd : FiniteLimit (fun x : ℝ => Real.sqrt (1+x)+1) (punctured 0) 2 := by
    norm_num at hs ⊢
    convert limit_add hs (const_limit _ 1) using 1; norm_num
  refine approaches_congr ?_ (limit_div (const_limit _ 1) hd (by norm_num))
  refine ⟨1/2, by norm_num, ?_⟩
  intro x hx hn
  change |x-0| < 1/2 at hx
  change x ≠ 0 at hn
  change 1/(Real.sqrt (1+x)+1) = (Real.sqrt (1+x)-1)/x
  have hsq := Real.sq_sqrt (show 0 ≤ 1+x by linarith [(abs_lt.mp hx).1])
  have hd0 : Real.sqrt (1+x)+1 ≠ 0 := by positivity
  apply (div_eq_div_iff hd0 hn).2
  nlinarith

theorem removable_center (b : ℝ) :
    BookContinuousAt (fillCenter (fun x : ℝ => (x^2-1)/(x-1)) 1 b) 1 ↔ b = 2 := by
  rw [continuous_punctured_iff]
  have hlim : FiniteLimit (fillCenter (fun x : ℝ => (x^2-1)/(x-1)) 1 b) (punctured 1) 2 := by
    apply approaches_congr _ quotient_at_one.2
    exact eventually_mono (punctured_ne 1) fun x hx => by simp [fillCenter, hx]
  constructor
  · intro h
    have he := real_limit_unique (Ch03Examples.punctured_proper 1) h hlim
    simpa [fillCenter] using he
  · intro h
    simpa [fillCenter, h] using hlim

theorem rational_at_two_book :
    FiniteLimit (fun x : ℝ => (x^2+3*x-1)/(x+1)) (punctured 2) 3 := by
  have hx := punctured_id 2
  have hn := limit_sub (limit_add (limit_pow 2 hx) (limit_const_mul 3 hx)) (const_limit _ 1)
  have hd := limit_add hx (const_limit _ 1)
  convert limit_div hn hd (by norm_num : (2:ℝ)+1 ≠ 0) using 1 <;> norm_num [id]

theorem squared_damped_sine :
    FiniteLimit (fun x : ℝ => x^2 * Real.sin (1/x)) (punctured 0) 0 := by
  have hpow : FiniteLimit (fun x : ℝ => x^2) (punctured 0) 0 := by
    simpa [id] using limit_pow 2 (punctured_id 0)
  have h := bounded_mul_zero 1 zero_le_one
    (eventually_of_forall (F := punctured 0) fun x => Real.abs_sin_le_one (1/x)) hpow
  simpa only [mul_comm] using h

theorem quadratic_minus_linear_top :
    Approaches (fun x : ℝ => x^2-3*x) (upperFilter ℝ) (upperFilter ℝ) := by
  apply (Ch04Infinity.upper_iff _ _).2
  intro M
  refine ⟨max 6 (2*(|M|+1)), fun x hx => ?_⟩
  have h6 := (le_max_left _ _).trans hx
  have hm := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hprod := mul_nonneg hx0 (show 0 ≤ x-4 by linarith)
  change M ≤ x^2-3*x
  nlinarith [le_abs_self M, abs_nonneg M]

noncomputable def joined (c d x : ℝ) : ℝ := if x < 1 then x^2+1 else if x = 1 then c else 3*x+d

theorem matching_parameter (c d : ℝ) : BookContinuousAt (joined c d) 1 ↔ c = 2 ∧ d = -1 := by
  have hl : FiniteLimit (joined c d) (leftNear 1) 2 := by
    refine approaches_congr (f := fun x : ℝ => x^2+1) ?_ ?_
    · exact ⟨1, zero_lt_one, fun x _ hx => by change x < 1 at hx; simp [joined, hx]⟩
    · simpa [id, one_add_one_eq_two] using limit_add (limit_pow 2 (left_id 1)) (const_limit _ 1)
  have hr : FiniteLimit (joined c d) (rightNear 1) (3+d) := by
    refine approaches_congr (f := fun x : ℝ => 3*x+d) ?_ ?_
    · exact ⟨1, zero_lt_one, fun x _ hx => by
        change 1 < x at hx
        simp [joined, not_lt_of_ge hx.le, ne_of_gt hx]⟩
    · simpa [id] using limit_add (limit_const_mul 3 (right_id 1)) (const_limit _ d)
  rw [continuous_gluing]
  have hc : joined c d 1 = c := by simp [joined]
  rw [hc]
  constructor
  · rintro ⟨hL,hR⟩
    have h2 := real_limit_unique (left_proper 1) hL hl
    have h3 := real_limit_unique (right_proper 1) hR hr
    exact ⟨h2, by linarith⟩
  · rintro ⟨hc,hd⟩
    exact ⟨by simpa [hc] using hl, by simpa [hc,hd, show (3:ℝ)+(-1)=2 by norm_num] using hr⟩

theorem reciprocal_local_not_global :
    (∀ a ∈ Set.Ioo (0 : ℝ) 1, BookContinuousAt (fun x => 1/x) a) ∧
      (∀ M : ℝ, 0 < M → ∃ x ∈ Set.Ioo (0 : ℝ) 1, M < 1/x) := by
  constructor
  · intro a ha
    exact limit_div (const_limit _ 1) (approaches_id _) (ne_of_gt ha.1)
  · intro M hM
    refine ⟨min 1 (1/M) / 2, ⟨by positivity, ?_⟩, ?_⟩
    · linarith [min_le_left (1 : ℝ) (1/M)]
    · have hp : 0 < min 1 (1/M) / 2 := by positivity
      exact (lt_one_div hM hp).2 (by
        have h := min_le_right (1 : ℝ) (1/M)
        have hh : 0 < 1/M := by positivity
        linarith)

theorem infinity_difference_examples :
    Approaches (fun x : ℝ => 2*x-x) (upperFilter ℝ) (upperFilter ℝ) ∧
      FiniteLimit (fun x : ℝ => x-x) (upperFilter ℝ) 0 ∧
      Approaches (fun x : ℝ => x-2*x) (upperFilter ℝ) (lowerFilter ℝ) := by
  refine ⟨?_, by simpa using (const_limit (upperFilter ℝ) 0), ?_⟩
  · exact approaches_congr (eventually_of_forall fun x => by ring) (approaches_id _)
  · apply (Ch04Infinity.neg_upper_iff _ _).1
    exact approaches_congr (eventually_of_forall fun x => by ring) (approaches_id _)

theorem infinity_quotient_examples :
    Approaches (fun x : ℝ => x^2/x) (upperFilter ℝ) (upperFilter ℝ) ∧
      FiniteLimit (fun x : ℝ => x/x) (upperFilter ℝ) 1 ∧
      FiniteLimit (fun x : ℝ => x/x^2) (upperFilter ℝ) 0 := by
  have hp : Eventually (upperFilter ℝ) (fun x => x ≠ 0) :=
    ⟨1, fun x hx => by change x ≠ 0; exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)⟩
  refine ⟨approaches_congr (eventually_mono hp fun x hx => ?_) (approaches_id _),
    approaches_congr (eventually_mono hp fun x hx => ?_) (const_limit _ 1),
    approaches_congr (eventually_mono hp fun x hx => ?_) reciprocal_top⟩
  · field_simp
  · exact (div_self hx).symm
  · field_simp

theorem sign_sequences :
    Ch05.Converges reciprocalSequence 0 ∧
    Ch05.Converges (fun n => -reciprocalSequence n) 0 ∧
    (∀ n, |reciprocalSequence n| / reciprocalSequence n = 1) ∧
    (∀ n, |-reciprocalSequence n| / (-reciprocalSequence n) = -1) := by
  have hneg := limit_neg reciprocal_sequence
  rw [neg_zero] at hneg
  refine ⟨reciprocal_sequence, hneg, ?_, ?_⟩
  · intro n
    have hp : 0 < reciprocalSequence n := by positivity
    rw [abs_of_pos hp, div_self hp.ne']
  · intro n
    have hp : 0 < reciprocalSequence n := by positivity
    rw [abs_neg, abs_of_pos hp, div_neg, div_self hp.ne']

theorem sign_no_punctured_limit : ¬ ∃ b, Ch04Local.DomainLimit (fun x => |x|/x) Set.univ 0 b := by
  rintro ⟨b,hb⟩
  have hp (n : ℕ) : 0 < reciprocalSequence n := by positivity
  have hu := Ch04Local.domain_limit_sequence hb reciprocalSequence sign_sequences.1
    (fun n => ⟨Set.mem_univ _, (hp n).ne'⟩)
  have hv := Ch04Local.domain_limit_sequence hb (fun n => -reciprocalSequence n) sign_sequences.2.1
    (fun n => ⟨Set.mem_univ _, (neg_lt_zero.mpr (hp n)).ne⟩)
  have h1 : Ch05.Converges (fun _ => 1) b := by simpa only [sign_sequences.2.2.1] using hu
  have hn : Ch05.Converges (fun _ => -1) b := by simpa only [sign_sequences.2.2.2] using hv
  have he1 := real_limit_unique tailFilter_proper h1 (const_limit tailFilter 1)
  have hen := real_limit_unique tailFilter_proper hn (const_limit tailFilter (-1))
  linarith

end Ch04Examples
