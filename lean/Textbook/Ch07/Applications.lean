import Textbook.Ch07.SignTests
import Textbook.Ch06.Counterexamples

namespace Ch07
open Ch06 Ch02 Ch03 Ch03Approach Set Filter
open scoped Topology

theorem rational_derivative (a : ℝ) (ha : a ≠ 1) :
    HasDerivative (fun x => (x^2+1)/(x-1)) a ((a^2-2*a-1)/(a-1)^2) := by
  apply (derivative_mathlib _ _ _).2
  have h := (((hasDerivAt_id a).fun_pow 2).add_const 1).div
    ((hasDerivAt_id a).sub_const 1) (sub_ne_zero.mpr ha)
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

theorem area_product {u v : ℝ → ℝ} {a du dv : ℝ}
    (hu : HasDerivative u a du) (hv : HasDerivative v a dv) :
    HasDerivative (fun t => u t*v t) a (du*v a+u a*dv) ∧
      ∀ x, u x*v x-u a*v a =
        v a*(u x-u a)+u a*(v x-v a)+(u x-u a)*(v x-v a) := by
  exact ⟨product_rule_direct hu hv,fun x => by ring⟩

def LocalMinimumOn (f : ℝ → ℝ) (S : Set ℝ) (a : ℝ) : Prop :=
  a ∈ S ∧ ∃ δ > 0, ∀ x ∈ S, |x-a| < δ → f a ≤ f x

def GlobalMinimumOn (f : ℝ → ℝ) (S : Set ℝ) (a : ℝ) : Prop :=
  a ∈ S ∧ ∀ x ∈ S, f a ≤ f x

def StrictLocalMinimumOn (f : ℝ → ℝ) (S : Set ℝ) (a : ℝ) : Prop :=
  a ∈ S ∧ ∃ δ > 0, ∀ x ∈ S, x ≠ a → |x-a| < δ → f a < f x

def Stationary (f : ℝ → ℝ) (a : ℝ) : Prop := HasDerivative f a 0

theorem cube_strict_stationary :
    StrictMono (fun x : ℝ => x^3) ∧ Stationary (fun x => x^3) 0 :=
  ⟨(by decide : Odd 3).strictMono_pow, cubic_stationary⟩

theorem candidate_examples :
    Stationary (fun x : ℝ => x^2) 0 ∧
    GlobalMinimumOn (fun x : ℝ => x^2) univ 0 ∧
    GlobalMinimumOn (abs : ℝ → ℝ) univ 0 ∧
    (¬ ∃ d, HasDerivative (abs : ℝ → ℝ) 0 d) ∧
    GlobalMinimumOn id (Icc (0:ℝ) 1) 0 ∧ HasDerivative id 0 1 := by
  refine ⟨by simpa [Stationary] using derivative_square 0,
    ⟨mem_univ _,fun x _ => by simpa using sq_nonneg x⟩,
    ⟨mem_univ _,fun x _ => by simpa using abs_nonneg x⟩,
    abs_has_no_derivative,⟨⟨le_rfl,zero_le_one⟩,fun _ hx => hx.1⟩,derivative_id 0⟩

theorem interval_lipschitz {f df : ℝ → ℝ} {S : Set ℝ} {M : ℝ}
    (hS : Convex ℝ S) (hc : ContinuousOn f S) (hM : 0 ≤ M)
    (hd : ∀ x ∈ interior S, HasDerivative f x (df x))
    (hb : ∀ x ∈ interior S, |df x| ≤ M) :
    ∀ x ∈ S, ∀ y ∈ S, |f y-f x| ≤ M*|y-x| := by
  have H (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
      |f y-f x| ≤ M*|y-x| := by
    obtain ⟨c,hc',he⟩ := interval_increment hS hc hd hx hy hxy
    rw [he,abs_mul]
    exact mul_le_mul_of_nonneg_right (hb c hc') (abs_nonneg _)
  intro x hx y hy
  rcases lt_trichotomy x y with h | h | h
  · exact H x y hx hy h
  · simp [h]
  · simpa only [abs_sub_comm] using H y x hy hx h

theorem residual_bound {f df : ℝ → ℝ} {S : Set ℝ} {m r : ℝ}
    (hS : Convex ℝ S) (hc : ContinuousOn f S) (hm : 0 < m)
    (hd : ∀ t ∈ interior S, HasDerivative f t (df t))
    (hb : ∀ t ∈ interior S, m ≤ df t) (hr : r ∈ S) (hz : f r = 0) :
    ∀ x ∈ S, |x-r| ≤ |f x|/m := by
  have H (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
      |y-x| * m ≤ |f y-f x| := by
    obtain ⟨c,hc',he⟩ := interval_increment hS hc hd hx hy hxy
    rw [he,abs_mul,abs_of_nonneg (hm.le.trans (hb c hc'))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hb c hc') (abs_nonneg (y-x))
  intro x hx
  apply (le_div_iff₀ hm).2
  rcases lt_trichotomy r x with h | h | h
  · simpa [hz] using H r x hr hx h
  · simp [h]
  · have hh := H x r hx hr h
    rw [abs_sub_comm r x, abs_sub_comm (f r) (f x), hz, sub_zero] at hh
    exact hh

theorem log_bounds (x : ℝ) (hx : 0 < x) :
    (x-1)/x ≤ Real.log x ∧ Real.log x ≤ x-1 := by
  refine ⟨?_,Real.log_le_sub_one_of_pos hx⟩
  have he : (x-1)/x = 1-x⁻¹ := by
    field_simp [hx.ne']
  rw [he]
  exact Real.one_sub_inv_le_log_of_pos hx

theorem log_increment_limit :
    Approaches (fun h : ℝ => Real.log (1+h)/h) (punctured 0) (neighborhoodFilter 1) := by
  have hd : HasDerivative Real.log 1 1 := (derivative_mathlib _ _ _).2
    (by simpa using Real.hasDerivAt_log (show (1:ℝ) ≠ 0 by norm_num))
  simpa only [Real.log_one,sub_zero] using (derivative_increment_iff _ _ _).1 hd

theorem exp_decay_derivative (A k t : ℝ) (hA : 0 < A) (hk : 0 < k) :
    HasDerivative (fun x => A*Real.exp (-k*x)) t (-k*A*Real.exp (-k*t)) ∧
      -k*A*Real.exp (-k*t) < 0 := by
  refine ⟨?_,by
    have hn : -k*A < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hA
    exact mul_neg_of_neg_of_pos hn (Real.exp_pos _)⟩
  apply (derivative_mathlib _ _ _).2
  convert (((hasDerivAt_id t).const_mul (-k)).exp.const_mul A) using 1 <;>
    (try simp only [id_eq]) <;> ring

theorem reciprocal_design (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    2*Real.sqrt A ≤ x+A/x ∧ (x+A/x = 2*Real.sqrt A ↔ x = Real.sqrt A) := by
  have he : x+A/x-2*Real.sqrt A = (x-Real.sqrt A)^2/x := by
    apply (eq_div_iff hx.ne').2
    rw [sub_mul,add_mul,div_mul_cancel₀ _ hx.ne']
    nlinarith [Real.sq_sqrt hA.le]
  have hn : 0 ≤ (x-Real.sqrt A)^2/x := by positivity
  refine ⟨by linarith,?_⟩
  constructor
  · intro h
    have hz : (x-Real.sqrt A)^2/x = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hz).resolve_right hx.ne'))
  · intro h
    subst x
    simp only [sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div] at he
    linarith

end Ch07
