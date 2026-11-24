import Textbook.Ch07.Differentiation
import Textbook.Ch06.Statements

namespace Ch07
open Ch06 Set Filter
open Ch02 Ch03 Ch03Approach Ch03Rules Ch04

theorem remainder_algebra {r s : ℝ → ℝ} (hr : LittleOIncrement r)
    (hs : LittleOIncrement s) (c : ℝ) :
    LittleOIncrement (fun h => r h+s h) ∧ LittleOIncrement (fun h => c*r h) := by
  obtain ⟨hr₀,hr⟩ := hr
  obtain ⟨hs₀,hs⟩ := hs
  constructor
  · refine ⟨by simp [hr₀,hs₀], ?_⟩
    simpa only [add_div, add_zero] using limit_add hr hs
  · refine ⟨by simp [hr₀], ?_⟩
    simpa only [mul_div_assoc, mul_zero] using limit_const_mul c hr

theorem linear_rule {f g : ℝ → ℝ} {a df dg : ℝ}
    (hf : HasDerivative f a df) (hg : HasDerivative g a dg) (α β : ℝ) :
    HasDerivative (fun x => α*f x+β*g x) a (α*df+β*dg) :=
  (derivative_mathlib _ _ _).2
    ((((derivative_mathlib _ _ _).1 hf).const_mul α).add
      (((derivative_mathlib _ _ _).1 hg).const_mul β))

theorem linear_example (a : ℝ) :
    HasDerivative (fun x : ℝ => 3*x^2-2*x+7) a (6*a-2) ∧
      (3*(3:ℝ)^2-2*3+7 = 28) ∧ (6*(3:ℝ)-2 = 16) := by
  refine ⟨?_,by norm_num,by norm_num⟩
  have h := linear_rule (derivative_square a) (derivative_id a) 3 (-2)
  apply (derivative_mathlib _ _ _).2
  convert ((derivative_mathlib _ _ _).1 h).add_const 7 using 1
  · funext x
    ring
  · ring

theorem quotient_rule {f g : ℝ → ℝ} {a df dg : ℝ}
    (hf : HasDerivative f a df) (hg : HasDerivative g a dg) (h₀ : g a ≠ 0) :
    HasDerivative (fun x => 1/g x) a (-dg/(g a)^2) ∧
    HasDerivative (fun x => f x/g x) a ((df*g a-f a*dg)/(g a)^2) := by
  have hf' := (derivative_mathlib _ _ _).1 hf
  have hg' := (derivative_mathlib _ _ _).1 hg
  refine ⟨(derivative_mathlib _ _ _).2 ?_, (derivative_mathlib _ _ _).2 (hf'.div hg' h₀)⟩
  rw [show (fun x => 1/g x) = g⁻¹ by funext x; exact one_div (g x)]
  exact hg'.inv h₀

theorem rolle_book {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (he : f a = f b)
    (hd : ∀ x ∈ Ioo a b, ∃ d, HasDerivative f x d) :
    ∃ x ∈ Ioo a b, HasDerivative f x 0 := by
  obtain ⟨x,hx,hext⟩ := exists_isLocalExtr_Ioo hab hc he
  obtain ⟨d,hd⟩ := hd x hx
  have hz := hext.hasDerivAt_eq_zero ((derivative_mathlib _ _ _).1 hd)
  exact ⟨x,hx,hz ▸ hd⟩

theorem mean_value_book (f df : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivative f x (df x)) :
    ∃ c ∈ Ioo a b, f b-f a = df c*(b-a) := by
  obtain ⟨c,hc',he⟩ := mean_value f df hab hc (fun x hx => (derivative_mathlib _ _ _).1 (hd x hx))
  exact ⟨c,hc',((eq_div_iff (sub_ne_zero.mpr hab.ne')).1 he).symm⟩

theorem mean_value_square {a b : ℝ} (hab : a < b) :
    (a+b)/2 ∈ Ioo a b ∧
      HasDerivative (fun x => x^2) ((a+b)/2) ((b^2-a^2)/(b-a)) := by
  refine ⟨⟨by linarith,by linarith⟩,?_⟩
  rw [show (b^2-a^2)/(b-a) = 2*((a+b)/2) by
    field_simp [sub_ne_zero.mpr hab.ne']
    <;> ring]
  exact derivative_square _

def IsLipschitzOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ∀ y ∈ S, |f y-f x| ≤ M*|y-x|

theorem near_optimal {S : Set ℝ} {C actual : ℝ → ℝ} {x₀ η : ℝ}
    (hx₀ : x₀ ∈ S) (hmin : ∀ x ∈ S, C x₀ ≤ C x)
    (herr : ∀ x ∈ S, |actual x-C x| ≤ η) :
    ∀ x ∈ S, actual x₀ ≤ actual x+2*η := by
  intro x hx
  have h₀ := (abs_le.mp (herr x₀ hx₀)).2
  have h₁ := (abs_le.mp (herr x hx)).1
  linarith [hmin x hx]

theorem cauchy_mean_value_book (f g df dg : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ x ∈ Ioo a b, HasDerivative f x (df x))
    (hdg : ∀ x ∈ Ioo a b, HasDerivative g x (dg x)) :
    ∃ c ∈ Ioo a b, (f b-f a)*dg c = (g b-g a)*df c := by
  obtain ⟨c,hc,he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f df hab hf
    (fun x hx => (derivative_mathlib _ _ _).1 (hdf x hx)) g dg hg
    (fun x hx => (derivative_mathlib _ _ _).1 (hdg x hx))
  exact ⟨c,hc,he.symm⟩

theorem local_inverse_rule {f g : ℝ → ℝ} {a b p : ℝ}
    (hf : HasDerivative f a p) (hp : p ≠ 0) (_hb : b = f a) (hga : g b = a)
    (hg : ContinuousAt g b)
    (hfg : ∃ δ > 0, ∀ y, |y-b| < δ → f (g y) = y) :
    HasDerivative g b (1/p) := by
  obtain ⟨δ,hδ,he⟩ := hfg
  have hev : ∀ᶠ y in nhds b, f (g y) = y :=
    Metric.eventually_nhds_iff.2 ⟨δ,hδ,fun y hy => he y (by simpa only [Real.dist_eq] using hy)⟩
  have hf' : HasDerivAt f p (g b) := hga.symm ▸ (derivative_mathlib _ _ _).1 hf
  exact (derivative_mathlib _ _ _).2
    (by simpa only [one_div] using HasDerivAt.of_local_left_inverse hg hf' hp hev)

theorem fermat_book {f : ℝ → ℝ} {a d : ℝ}
    (he : IsLocalMin f a ∨ IsLocalMax f a) (hd : HasDerivative f a d) :
    d = 0 := by
  rcases he with h | h
  · exact h.hasDerivAt_eq_zero ((derivative_mathlib _ _ _).1 hd)
  · exact h.hasDerivAt_eq_zero ((derivative_mathlib _ _ _).1 hd)

theorem composition_example (a : ℝ) :
    HasDerivative (fun x : ℝ => (x^2+1)^3) a (6*a*(a^2+1)^2) := by
  apply (derivative_mathlib _ _ _).2
  have h := (((hasDerivAt_id a).fun_pow 2).add_const 1).fun_pow 3
  convert h using 1 <;> (try simp only [id_eq]) <;> ring

theorem exp_tangent_lower (x : ℝ) :
    1+x ≤ Real.exp x ∧ (1+x = Real.exp x ↔ x = 0) := by
  refine ⟨by simpa only [add_comm] using Real.add_one_le_exp x, ?_⟩
  constructor
  · intro h
    by_contra hx
    have hs := Real.add_one_lt_exp hx
    linarith
  · rintro rfl
    simp

end Ch07
