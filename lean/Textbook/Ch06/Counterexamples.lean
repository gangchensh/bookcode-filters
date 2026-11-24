import Textbook.Ch06.Examples

namespace Ch06
open Ch02 Ch03 Ch03Approach Ch05
open scoped Topology

def DifferentiablePoints (f : ℝ → ℝ) : Set ℝ := {a | ∃ d, HasDerivative f a d}

noncomputable def derivativeFunction (f : ℝ → ℝ) (a : DifferentiablePoints f) : ℝ :=
  deriv f a

theorem derivative_function_spec (f : ℝ → ℝ) (a : DifferentiablePoints f) :
    HasDerivative f a (derivativeFunction f a) := by
  obtain ⟨d, hd⟩ := a.property
  change HasDerivative f a (deriv f a)
  rw [derivative_value hd]
  exact hd

theorem abs_continuous_zero : Ch04Continuity.BookContinuousAt (abs : ℝ → ℝ) 0 := by
  exact (Ch04Continuity.continuous_mathlib _ _).2
    ((continuous_abs : Continuous (abs : ℝ → ℝ)).continuousAt)

theorem abs_example :
    Ch04Continuity.BookContinuousAt (abs : ℝ → ℝ) 0 ∧
      ¬ ∃ d, HasDerivative (abs : ℝ → ℝ) 0 d :=
  ⟨abs_continuous_zero, abs_has_no_derivative⟩

theorem linear_vs_continuous :
    HasDerivative (fun x : ℝ => x^2) 0 0 ∧
      Ch04Continuity.BookContinuousAt (abs : ℝ → ℝ) 0 ∧
      ¬ ∃ d, HasDerivative (abs : ℝ → ℝ) 0 d :=
  ⟨by simpa using derivative_square 0, abs_continuous_zero, abs_has_no_derivative⟩

theorem cubic_tangent :
    HasDerivative (fun x : ℝ => x^3) 0 0 ∧
    (∀ x : ℝ, tangentModel (fun t => t^3) 0 0 x = 0) ∧
    ∀ x : ℝ, (x < 0 → x^3 < 0) ∧ (0 < x → 0 < x^3) :=
  ⟨cubic_stationary, fun x => by simp [tangentModel], cubic_tangent_sign⟩

theorem zero_slope_comparison :
    HasDerivative (fun x : ℝ => x^2) 0 0 ∧
    HasDerivative (fun x : ℝ => -(x^2)) 0 0 ∧
    HasDerivative (fun x : ℝ => x^3) 0 0 ∧
    (∀ c : ℝ, HasDerivative (fun _ => c) 0 0) ∧
    (∀ x : ℝ, 0 ≤ x^2 ∧ -(x^2) ≤ 0) ∧
    ∀ x : ℝ, (x < 0 → x^3 < 0) ∧ (0 < x → 0 < x^3) := by
  refine ⟨by simpa using derivative_square 0, ?_, cubic_stationary,
    fun c => derivative_const c 0, fun x => ⟨sq_nonneg x, neg_nonpos.mpr (sq_nonneg x)⟩,
    cubic_tangent_sign⟩
  apply (derivative_mathlib _ _ _).2
  have hsq : HasDerivAt (fun x : ℝ => x^2) 0 0 :=
    (derivative_mathlib _ _ _).1 (by simpa using derivative_square 0)
  change HasDerivAt (-(fun x : ℝ => x^2)) 0 0
  simpa only [neg_zero] using hsq.neg

theorem oscillatory_remainder :
    HasDerivative (fun x : ℝ => 3*x+x^2*Real.sin (1/x)) 0 3 := by
  apply derivative_perturbation (f := fun x => 3*x) (v := fun x => x^2*Real.sin (1/x))
  · simpa using derivative_affine 3 0 0
  · simp
  · apply (increment_limit_iff _ _).2
    intro ε hε
    refine ⟨ε, hε, fun h hh => ?_⟩
    simp only [zero_add, sub_zero]
    have hn := abs_pos.mp hh.1
    have he : h^2*Real.sin (1/h)/h = h*Real.sin (1/h) := by
      field_simp [hn]
      <;> ring
    rw [he, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg h) (Real.abs_sin_le_one _)).trans_lt hh.2

theorem reciprocal_tolerance (a h : ℝ) (ha : a ≠ 0) (hh : |h| ≤ |a|/2) :
    |1/(a+h)-(1/a-h/a^2)| ≤ 2*h^2/|a|^3 := by
  have ha' := abs_pos.mpr ha
  have htri : |a| ≤ |a+h|+|h| := by
    simpa [show (a+h)+(-h) = a by ring] using abs_add_le (a+h) (-h)
  have hl : |a|/2 ≤ |a+h| := by linarith
  have hs : 0 < |a+h| := by linarith
  rw [reciprocal_remainder a h ha (abs_pos.mp hs), abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg h), abs_of_nonneg (sq_nonneg a)]
  have hden : 0 < a^2*|a+h| := mul_pos (sq_pos_of_ne_zero ha) hs
  rw [div_le_div_iff₀ hden (pow_pos ha' 3)]
  have he : |a|^3 = a^2*|a| := by rw [pow_succ, sq_abs]
  rw [he]
  calc
    h^2 * (a^2 * |a|) ≤ h^2 * (a^2 * (2*|a+h|)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg a)) (sq_nonneg h)
    _ = 2*h^2*(a^2*|a+h|) := by ring

theorem reciprocal_zero (h : ℝ) :
    ((1/h-1/(0:ℝ))/h = 1/h^2) ∧
      ¬ ∃ d, HasDerivative (fun x : ℝ => 1/x) 0 d := by
  refine ⟨by simp [pow_two, div_eq_mul_inv], ?_⟩
  rintro ⟨d, hd⟩
  have hc := derivative_continuous hd
  unfold Ch04Continuity.BookContinuousAt at hc
  obtain ⟨δ, hδ, H⟩ := (real_iff _ _ _).1 hc 1 zero_lt_one
  let x : ℝ := min δ 1 / 2
  have hp : 0 < x := half_pos (lt_min hδ zero_lt_one)
  have hxδ : x < δ := by
    dsimp [x]
    linarith [min_le_left δ (1:ℝ)]
  have hx1 : x < 1 := by
    dsimp [x]
    linarith [min_le_right δ (1:ℝ)]
  have hxmem : x ∈ Ch02Neighborhoods.epsNeighborhood 0 δ := by
    change |x-0| < δ
    simpa [abs_of_pos hp] using hxδ
  have hh := H hxmem
  change |1/x-1/(0:ℝ)| < 1 at hh
  have hq : 1/x < 1 := (le_abs_self _).trans_lt (by simpa using hh)
  have := (div_lt_iff₀ hp).1 hq
  linarith

theorem abs_sequence_witnesses :
    ∃ h k : ℕ → ℝ, (∀ n, h n ≠ 0 ∧ k n ≠ 0) ∧
      Converges h 0 ∧ Converges k 0 ∧
      (∀ n, (|h n|-|0|)/h n = 1 ∧ (|k n|-|0|)/k n = -1) := by
  let h : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hp (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have H : Converges h 0 := reciprocal_sequence
  refine ⟨h, fun n => -h n, fun n => ⟨(hp n).ne', neg_ne_zero.mpr (hp n).ne'⟩,
    H, ?_, fun n => ?_⟩
  · simpa only [Converges, neg_zero] using Ch04.limit_neg H
  · simp [abs_of_pos (hp n), (hp n).ne']

theorem noisy_square_bound (a h e₀ e₁ σ : ℝ) (hh : h ≠ 0)
    (he₀ : |e₀| ≤ σ) (he₁ : |e₁| ≤ σ) :
    |(((a+h)^2+e₁)-(a^2+e₀))/h-2*a| ≤ |h|+2*σ/|h| := by
  have he : (((a+h)^2+e₁)-(a^2+e₀))/h-2*a = h+(e₁-e₀)/h := by
    field_simp [hh]
    <;> ring
  rw [he]
  calc
    |h+(e₁-e₀)/h| ≤ |h|+|(e₁-e₀)/h| := abs_add_le _ _
    _ ≤ |h|+2*σ/|h| := by
      rw [abs_div]
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ (abs_nonneg h)
      have ht := abs_add_le e₁ (-e₀)
      rw [← sub_eq_add_neg, abs_neg] at ht
      change |e₁-e₀| ≤ 2*σ
      linarith

theorem noisy_step_optimal (σ s : ℝ) (hσ : 0 < σ) (hs : 0 < s) :
    2*Real.sqrt (2*σ) ≤ s+2*σ/s ∧
      (2*Real.sqrt (2*σ) = s+2*σ/s ↔ s = Real.sqrt (2*σ)) := by
  have hsq := Real.sq_sqrt (show 0 ≤ 2*σ by positivity)
  have he : s+2*σ/s-2*Real.sqrt (2*σ) = (s-Real.sqrt (2*σ))^2/s := by
    apply (eq_div_iff hs.ne').2
    rw [sub_mul, add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith
  have hnon : 0 ≤ (s-Real.sqrt (2*σ))^2/s := by positivity
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have hz : (s-Real.sqrt (2*σ))^2/s = 0 := by linarith
    have hz' : (s-Real.sqrt (2*σ))^2 = 0 :=
      (div_eq_zero_iff.mp hz).resolve_right hs.ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz')
  · intro h
    subst s
    rw [sub_self, zero_pow (by decide : (2:ℕ) ≠ 0), zero_div] at he
    linarith

theorem sqrt_right_diverges :
    Approaches (fun h => (Real.sqrt h-Real.sqrt 0)/h) (rightNear 0) (upperFilter ℝ) := by
  apply (Ch03Definitions.upper_target_iff _ _).2
  intro M
  let K := |M|+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨1/K^2, by positivity, fun x hx hpos => ?_⟩
  change |x-0| < 1/K^2 at hx
  change 0 < x at hpos
  rw [sub_zero, abs_of_pos hpos] at hx
  change M ≤ (Real.sqrt x-Real.sqrt 0)/x
  have hs := Real.sqrt_pos.2 hpos
  have hsq := Real.sq_sqrt hpos.le
  have hkx : x*K^2 < 1 := (lt_div_iff₀ (sq_pos_of_ne_zero hK.ne')).1 hx
  have hp : Real.sqrt x*K < 1 := by
    by_contra! h
    have ht := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) h
    have he : (Real.sqrt x*K)*(Real.sqrt x*K) = x*K^2 := by
      calc
        _ = (Real.sqrt x)^2*K^2 := by ring
        _ = _ := by rw [hsq]
    rw [he] at ht
    linarith
  have hq : K ≤ 1/Real.sqrt x := (le_div_iff₀ hs).2 (by linarith)
  have he : (Real.sqrt x-Real.sqrt 0)/x = 1/Real.sqrt x := by
    rw [Real.sqrt_zero, sub_zero]
    apply (div_eq_div_iff hpos.ne' hs.ne').2
    nlinarith
  rw [he]
  exact (show M ≤ K by dsimp [K]; linarith [le_abs_self M]).trans hq

theorem sqrt_right_no_finite :
    ¬ ∃ d, HasRightDerivative Real.sqrt 0 d := by
  rintro ⟨d, hd⟩
  have hu := (Ch03Definitions.upper_target_iff _ _).1 sqrt_right_diverges (d+2)
  obtain ⟨ρ, hρ, hu⟩ := hu
  obtain ⟨δ, hδ, H⟩ := (derivative_right_epsilon_iff _ _ _).1 hd 1 zero_lt_one
  let x := min ρ δ/2
  have hp : 0 < x := half_pos (lt_min hρ hδ)
  have hxρ : x < ρ := by dsimp [x]; linarith [min_le_left ρ δ]
  have hxδ : x < δ := by dsimp [x]; linarith [min_le_right ρ δ]
  have hxmem : x ∈ Ch02Neighborhoods.epsNeighborhood 0 ρ := by
    change |x-0| < ρ
    simpa [abs_of_pos hp] using hxρ
  have hu' := hu hxmem hp
  change d+2 ≤ (Real.sqrt x-Real.sqrt 0)/x at hu'
  have hl := H x ⟨hp, by simpa using hxδ⟩
  rw [sub_zero] at hl
  linarith [(abs_lt.mp hl).2]

end Ch06
