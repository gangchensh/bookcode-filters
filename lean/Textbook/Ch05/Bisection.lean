import Textbook.Ch05.Statements

namespace Ch05Bisection
open Ch05 Ch05Statements

def bracket : ℕ → ℚ × ℚ
  | 0 => (1,2)
  | n+1 =>
    let (a,b) := bracket n
    let m := (a+b)/2
    if m^2 ≤ 2 then (m,b) else (a,m)

abbrev left (n : ℕ) : ℝ := (bracket n).1
abbrev right (n : ℕ) : ℝ := (bracket n).2

theorem bracket_step (n : ℕ) :
    let m := (left n+right n)/2
    (m^2 ≤ 2 ∧ left (n+1) = m ∧ right (n+1) = right n) ∨
      (2 < m^2 ∧ left (n+1) = left n ∧ right (n+1) = m) := by
  let q := ((bracket n).1+(bracket n).2)/2
  have hq : (q:ℝ) = (left n+right n)/2 := by simp [q]
  by_cases h : q^2 ≤ 2
  · have hs : (q:ℝ)^2 ≤ 2 := by exact_mod_cast h
    have hb : bracket (n+1) = (q,(bracket n).2) := by
      rw [bracket]
      change (if q^2 ≤ 2 then (q,(bracket n).2) else ((bracket n).1,q)) = _
      rw [if_pos h]
    exact Or.inl ⟨by rwa [← hq], by simpa only [left,hb] using hq, by simp only [right,hb]⟩
  · have hs : (2:ℝ) < (q:ℝ)^2 := by exact_mod_cast (lt_of_not_ge h)
    have hb : bracket (n+1) = ((bracket n).1,q) := by
      rw [bracket]
      change (if q^2 ≤ 2 then (q,(bracket n).2) else ((bracket n).1,q)) = _
      rw [if_neg h]
    exact Or.inr ⟨by rwa [← hq], by simp only [left,hb], by simpa only [right,hb] using hq⟩

theorem bracket_contains (n : ℕ) : 1 ≤ left n ∧ left n ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ right n ∧
    right n-left n = (1/2:ℝ)^n := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg 2
  induction n with
  | zero =>
    have hl : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith
    have hr : Real.sqrt 2 ≤ 2 := by nlinarith
    exact ⟨by norm_num [left,bracket], by simpa [left,bracket] using hl,
      by simpa [right,bracket] using hr, by norm_num [left,right,bracket]⟩
  | succ n ih =>
    rcases ih with ⟨ha,hl,hr,hw⟩
    rcases bracket_step n with ⟨hm,hleft,hright⟩ | ⟨hm,hleft,hright⟩
    · rw [hleft,hright,pow_succ]
      refine ⟨by linarith, (Real.le_sqrt (by linarith) (by norm_num)).2 hm, hr, by linarith⟩
    · rw [hleft,hright,pow_succ]
      refine ⟨ha,hl,(Real.sqrt_le_left (by linarith)).2 hm.le,by linarith⟩

theorem bracket_nested (n : ℕ) : Set.Icc (left (n+1)) (right (n+1)) ⊆ Set.Icc (left n) (right n) := by
  have h := bracket_contains n
  intro x hx
  rcases bracket_step n with ⟨_,hl,hr⟩ | ⟨_,hl,hr⟩
  · exact ⟨by linarith [hx.1,h.2.1,h.2.2.1],by linarith [hx.2]⟩
  · exact ⟨by linarith [hx.1],by linarith [hx.2,h.2.1,h.2.2.1]⟩

theorem midpoint_error (n : ℕ) : |(left n+right n)/2-Real.sqrt 2| ≤ (1/2:ℝ)^(n+1) := by
  have h := bracket_contains n
  rw [pow_succ]
  exact abs_le.mpr ⟨by linarith [h.2.1,h.2.2.1,h.2.2.2],by linarith [h.2.1,h.2.2.1,h.2.2.2]⟩

theorem rational_left_cauchy_no_rational_limit :
    CauchySequence left ∧ Converges left (Real.sqrt 2) ∧ ¬ ∃ q : ℚ, Converges left (q : ℝ) := by
  have hl : Converges left (Real.sqrt 2) := by
    apply (converges_iff _ _).2
    intro ε hε
    obtain ⟨N,hN⟩ := (converges_iff _ _).1 (geometric_zero (1/2) (by norm_num) (by norm_num)) ε hε
    refine ⟨N,fun n hn => ?_⟩
    have h := bracket_contains n
    have hh := hN n hn
    rw [abs_of_nonpos (sub_nonpos.mpr h.2.1)]
    linarith [h.2.2.1,h.2.2.2,le_abs_self ((1/2:ℝ)^n-0)]
  refine ⟨convergent_cauchy hl,hl,?_⟩
  rintro ⟨q,hq⟩
  have he := Ch03Rules.real_limit_unique Ch02.tailFilter_proper hq hl
  exact irrational_sqrt_two ⟨q, he⟩

end Ch05Bisection
