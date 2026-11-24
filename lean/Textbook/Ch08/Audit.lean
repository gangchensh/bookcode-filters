import Textbook.Ch08.Taylor

namespace Ch08

open Asymptotics Filter Set
open scoped Topology

theorem quotient_test {α : Type*} {F : Filter α} {r g : α → ℝ}
    (hg : ∀ᶠ x in F, g x ≠ 0) :
    BookLittleO r g F ↔ Tendsto (fun x => r x / g x) F (𝓝 0) := by
  rw [littleO_mathlib]
  apply isLittleO_iff_tendsto'
  filter_upwards [hg] with x hx h
  exact (hx h).elim

theorem littleO_const_mul {α : Type*} {F : Filter α} {r g : α → ℝ}
    (hr : BookLittleO r g F) (c : ℝ) :
    BookLittleO (fun x => c * r x) g F := by
  intro ε hε
  have hd : 0 < |c| + 1 := by positivity
  filter_upwards [hr (ε / (|c| + 1)) (div_pos hε hd)] with x hx
  rw [abs_mul]
  calc
    |c| * |r x| ≤ |c| * (ε / (|c| + 1) * |g x|) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = (|c| * (ε / (|c| + 1))) * |g x| := by ring
    _ ≤ ε * |g x| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [← mul_div_assoc, div_le_iff₀ hd]
      nlinarith

theorem asymptotic_transitivity {α : Type*} {F : Filter α} {r g k : α → ℝ} :
    (BookLittleO r g F → BookBigO g k F → BookLittleO r k F) ∧
    (BookBigO r g F → BookBigO g k F → BookBigO r k F) := by
  simp only [littleO_mathlib, bigO_mathlib]
  exact ⟨fun hr hg => hr.trans_isBigO hg, fun hr hg => hr.trans hg⟩

theorem asymptotic_product_rules {α : Type*} {F : Filter α} {r s g k : α → ℝ} :
    (BookLittleO r g F → BookBigO r g F) ∧
    (BookBigO r g F → BookBigO s k F →
      BookBigO (fun x => r x * s x) (fun x => g x * k x) F) ∧
    (BookBigO r g F → BookLittleO g k F → BookLittleO r k F) := by
  simp only [littleO_mathlib, bigO_mathlib]
  exact ⟨fun hr => hr.isBigO, fun hr hs => hr.mul hs, fun hr hg => hr.trans_isLittleO hg⟩

theorem power_to_littleO {R : ℝ → ℝ} {n : ℕ} {r K : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (h : ∀ x, |x| < r → |R x| ≤ K * |x|^(n+1)) :
    BookLittleO R (fun x => x^n) (𝓝 0) := by
  intro ε hε
  have hd : 0 < K + 1 := by positivity
  have he : ∀ᶠ x : ℝ in 𝓝 0, |x| < min r (ε / (K+1)) := by
    exact (continuous_abs.continuousAt.eventually_lt continuousAt_const)
      (by simpa using lt_min hr (div_pos hε hd))
  filter_upwards [he] with x hx
  rw [abs_pow]
  have hk := (lt_div_iff₀ hd).mp ((lt_min_iff.mp hx).2)
  calc
    |R x| ≤ K * |x|^(n+1) := h x (lt_min_iff.mp hx).1
    _ = (K * |x|) * |x|^n := by rw [pow_succ]; ring
    _ ≤ ε * |x|^n :=
      mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg x]) (by positivity)

theorem power_source :
    BookLittleO (fun x : ℝ => x^2) id (𝓝[≠] 0) ∧
    ¬ BookBigO (fun x : ℝ => x^2) id atTop := by
  constructor
  · apply (littleO_mathlib _ _ _).2
    exact (isLittleO_pow_id (by decide : 1 < 2)).mono inf_le_left
  · rintro ⟨C, _, hC⟩
    obtain ⟨x, hx, h⟩ := (hC.and (eventually_gt_atTop (max C 0))).exists
    have hp : 0 < x := lt_of_le_of_lt (le_max_right _ _) h
    have hCx : C < x := lt_of_le_of_lt (le_max_left _ _) h
    change |x^2| ≤ C * |x| at hx
    rw [abs_of_nonneg (sq_nonneg x), abs_of_pos hp] at hx
    nlinarith [mul_pos hp (sub_pos.mpr hCx)]

theorem exp_and_log_growth (n : ℕ) {a : ℝ} (ha : 0 < a) :
    BookLittleO (fun x : ℝ => x^n) Real.exp atTop ∧
    BookLittleO Real.log (fun x : ℝ => x^a) atTop :=
  ⟨(littleO_mathlib _ _ _).2 Real.isLittleO_pow_exp_atTop,
    (littleO_mathlib _ _ _).2 (isLittleO_log_rpow_atTop ha)⟩

theorem curvature_example :
    HasDerivAt (fun x : ℝ => x + x^2) 1 0 ∧
    HasDerivAt (fun x : ℝ => x + 100*x^2) 1 0 ∧
    (∀ c : ℝ, (0:ℝ) + c*0^2 = 0) ∧
    |(1/100:ℝ) + (1/100)^2 - 1/100| = 1/10000 ∧
    |(1/100:ℝ) + 100*(1/100)^2 - 1/100| = 1/100 := by
  refine ⟨?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · convert (hasDerivAt_id (0:ℝ)).add ((hasDerivAt_id (0:ℝ)).pow 2) using 1 <;> first | rfl | norm_num
  · convert (hasDerivAt_id (0:ℝ)).add
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul 100) using 1 <;> first | rfl | norm_num

theorem cubic_expansion (a h : ℝ) :
    (a+h)^3 - (a^3+3*a^2*h+3*a*h^2) = h^3 ∧
    (a+h)^3 = a^3+3*a^2*h+3*a*h^2+h^3 := by constructor <;> ring

theorem scale_remainder {R : ℝ → ℝ} {C L r a x : ℝ} {n : ℕ}
    (hL : 0 < L) (hx : |x-a| ≤ L*r)
    (h : ∀ z, |z| ≤ r → |R z| ≤ C*|z|^(n+1)) :
    |R ((x-a)/L)| ≤ C/L^(n+1)*|x-a|^(n+1) := by
  have hz : |(x-a)/L| ≤ r := by
    rw [abs_div, abs_of_pos hL]
    apply (div_le_iff₀ hL).2
    simpa [mul_comm] using hx
  calc
    |R ((x-a)/L)| ≤ C * |(x-a)/L|^(n+1) := h _ hz
    _ = _ := by rw [abs_div, abs_of_pos hL, div_pow]; ring

theorem resistance_bound {r z : ℝ} (hr : 0 < r) (hz : |z| ≤ 1/2) :
    |1/(r*(1+z)) - (1-z+z^2)/r| ≤ 2*|z|^3/r := by
  rw [mul_comm r (1+z), ← div_div, ← sub_div, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (reciprocal_error z hz) hr.le

theorem reciprocal_linear_error {h : ℝ} (hh : |h| ≤ 1/2) :
    |1/(1+h) - (1-h)| ≤ 2*|h|^2 := by
  have hp : 0 < 1+h := by linarith [(abs_le.mp hh).1]
  have he : 1/(1+h)-(1-h) = h^2/(1+h) := by
    field_simp [hp.ne']
    ring
  rw [he, abs_div, abs_pow, abs_of_pos hp, div_le_iff₀ hp]
  nlinarith [mul_nonneg (sq_nonneg |h|) (show 0 ≤ 1+2*h by linarith [(abs_le.mp hh).1])]

theorem reciprocal_budget :
    |1/(1+(1/100:ℝ))-(1-1/100+(1/100)^2)| ≤ 2/1000000 ∧
    |1/(1+(1/100:ℝ))-(1-1/100)| ≤ 2/10000 := by
  norm_num

noncomputable def bookTaylor (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), iteratedDeriv k f a / (k.factorial : ℝ) * (x-a)^k

theorem bookTaylor_within {f : ℝ → ℝ} {a x : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (ha : a ∈ s) (hf : ContDiffAt ℝ n f a) :
    taylorWithinEval f n s a x = bookTaylor f n a x := by
  rw [taylor_within_apply, bookTaylor]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.of_le (by exact_mod_cast hkn)) ha]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

theorem book_lagrange {f : ℝ → ℝ} {a x : ℝ} {n : ℕ}
    (hax : a ≠ x) (hf : ∀ t ∈ uIcc a x, ContDiffAt ℝ (n+1) f t) :
    ∃ c ∈ uIoo a x, f x = bookTaylor f n a x +
      iteratedDeriv (n+1) f c * (x-a)^(n+1) / ((n+1).factorial : ℝ) := by
  obtain ⟨c, hc, he⟩ := lagrange_remainder hax (fun t ht => (hf t ht).contDiffWithinAt)
  rw [bookTaylor_within (uniqueDiffOn_uIcc hax) left_mem_uIcc
    ((hf a left_mem_uIcc).of_le (by norm_cast; omega))] at he
  exact ⟨c, hc, by linarith⟩

theorem book_lagrange_bound {f : ℝ → ℝ} {a x M : ℝ} {n : ℕ}
    (hf : ∀ t ∈ uIcc a x, ContDiffAt ℝ (n+1) f t)
    (hM : ∀ t ∈ uIcc a x, |iteratedDeriv (n+1) f t| ≤ M) :
    |f x - bookTaylor f n a x| ≤ M / ((n+1).factorial : ℝ) * |x-a|^(n+1) := by
  by_cases hax : a = x
  · subst x
    have he : bookTaylor f n a a = f a := by
      rw [← bookTaylor_within (s := univ) uniqueDiffOn_univ (mem_univ a)
        ((hf a left_mem_uIcc).of_le (by norm_cast; omega)), taylorWithinEval_self]
    simp [he]
  have h := lagrange_bound (n := n) hax
    (fun t ht => (hf t ht).contDiffWithinAt) (fun t ht => hM t (Ioo_subset_Icc_self ht))
  rw [bookTaylor_within (uniqueDiffOn_uIcc hax) left_mem_uIcc
    ((hf a left_mem_uIcc).of_le (by norm_cast; omega))] at h
  simpa [div_eq_mul_inv, mul_right_comm] using h

theorem bookTaylor_one (f : ℝ → ℝ) (a x : ℝ) :
    bookTaylor f 1 a x = f a + deriv f a * (x-a) := by
  simp [bookTaylor, Finset.sum_range_succ, iteratedDeriv_succ]

theorem bookTaylor_two (f : ℝ → ℝ) (a x : ℝ) :
    bookTaylor f 2 a x = f a + deriv f a * (x-a) +
      iteratedDeriv 2 f a / 2 * (x-a)^2 := by
  simp [bookTaylor, Finset.sum_range_succ, iteratedDeriv_succ (n := 0), Nat.factorial]

theorem linear_error {f : ℝ → ℝ} {a h M : ℝ}
    (hf : ∀ t ∈ uIcc a (a+h), ContDiffAt ℝ 2 f t)
    (hM : ∀ t ∈ uIcc a (a+h), |iteratedDeriv 2 f t| ≤ M) :
    |f (a+h)-f a-deriv f a*h| ≤ M/2*h^2 := by
  have hb := book_lagrange_bound (n := 1) (a := a) (x := a+h) hf hM
  rw [bookTaylor_one, add_sub_cancel_left, sq_abs] at hb
  convert hb using 1 <;> ring_nf

theorem exp_iteratedDeriv (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]

theorem exp_quadratic_bound {h r : ℝ} (hh : |h| ≤ r) :
    |Real.exp h - (1+h+h^2/2)| ≤ Real.exp r / 6 * |h|^3 := by
  have hb := book_lagrange_bound (n := 2) (a := 0) (x := h)
    (fun t _ => Real.contDiff_exp.contDiffAt)
    (fun t ht => by
      rw [exp_iteratedDeriv, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_max_iff.mp ht.2).elim (fun h0 => h0.trans ((abs_nonneg h).trans hh))
        (fun h1 => h1.trans ((le_abs_self h).trans hh)))
  rw [bookTaylor_two, Real.deriv_exp, exp_iteratedDeriv] at hb
  norm_num [Nat.factorial] at hb
  convert hb using 1 <;> ring

theorem exp_rational_certificate :
    20201/20000 - 1/3000000 ≤ Real.exp (1/100) ∧
    Real.exp (1/100) ≤ 20201/20000 + 1/3000000 := by
  have h := exp_quadratic_bound (h := 1/100) (r := 1/2) (by norm_num)
  have he : Real.exp (1/2) ≤ 2 := by
    have hlog := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
    have hl : (1/2:ℝ) ≤ Real.log 2 := by norm_num at hlog; linarith
    exact (Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log (by norm_num))
  norm_num at h
  have hb := abs_le.mp h
  constructor <;> linarith

theorem sqrt_linear_certificate {h : ℝ} (hh : -1 ≤ h) :
    0 ≤ 1+h/2-Real.sqrt (1+h) ∧ 1+h/2-Real.sqrt (1+h) ≤ h^2/2 := by
  let s := Real.sqrt (1+h)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have he : s^2 = 1+h := Real.sq_sqrt (by linarith)
  have hi : 1+h/2-s = h^2/(2*(s+1)^2) := by
    have hh' : h = (s-1)*(s+1) := by linarith
    rw [hh']
    field_simp [show s+1 ≠ 0 by positivity]
    ring
  change 0 ≤ 1+h/2-s ∧ 1+h/2-s ≤ h^2/2
  rw [hi]
  refine ⟨by positivity, (div_le_iff₀ (by positivity)).2 ?_⟩
  nlinarith [mul_nonneg (sq_nonneg h) (show 0 ≤ s^2+2*s by positivity)]

theorem sqrt_quadratic_certificate {h : ℝ} (hh : -1 ≤ h) :
    |Real.sqrt (1+h) - (1+h/2-h^2/8)| ≤ |h|^3/2 := by
  let s := Real.sqrt (1+h)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have he : s^2 = 1+h := Real.sq_sqrt (by linarith)
  have hp : 0 < s+1 := by positivity
  have hi : s-(1+h/2-h^2/8) = h^3*(s+3)/(8*(s+1)^3) := by
    have hh' : h = (s-1)*(s+1) := by linarith
    rw [hh']
    field_simp [hp.ne']
    ring
  change |s-(1+h/2-h^2/8)| ≤ |h|^3/2
  rw [hi, abs_div, abs_mul, abs_pow, abs_of_nonneg (show 0 ≤ s+3 by positivity),
    abs_of_pos (show 0 < 8*(s+1)^3 by positivity), div_le_iff₀ (by positivity)]
  have hb : s+3 ≤ 4*(s+1)^3 := by nlinarith [sq_nonneg s, pow_nonneg hs 3]
  nlinarith [mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg h) 3)]

theorem sqrt_ai_certificate {h : ℝ} (hh : |h| ≤ 1/100) :
    0 < 1+h ∧ |Real.sqrt (1+h)-(1+h/2-h^2/8)| ≤ 1/2000000 := by
  have hp : 0 < 1+h := by linarith [(abs_le.mp hh).1]
  refine ⟨hp, (sqrt_quadratic_certificate (le_of_lt (by linarith : -1 < h))).trans ?_⟩
  have hb := pow_le_pow_left₀ (abs_nonneg h) hh 3
  norm_num at hb ⊢
  linarith

theorem fixed_parameter {a : ℝ} (ha : 0 < a) :
    BookLittleO (fun h : ℝ => h^2/a) id (𝓝 0) := by
  suffices H : BookLittleO (fun h : ℝ => h^2/a) (fun h => h^1) (𝓝 0) by
    change BookLittleO _ (fun h : ℝ => h) _
    simpa using H
  apply power_to_littleO (n := 1) (r := 1) (K := 1/a) one_pos (by positivity)
  intro h _
  rw [abs_div, abs_of_pos ha, abs_pow]
  exact le_of_eq (by ring)

theorem moving_parameter {h : ℝ} (hh : h ≠ 0) :
    abs (h^2 / |h|) / |h| = 1 := by
  rw [abs_div, abs_abs, abs_pow]
  field_simp [abs_ne_zero.mpr hh]

theorem reciprocal_center {a h : ℝ} (ha : a ≠ 0) (hh : |h| ≤ |a|/2) :
    let E := 1/(a+h)-(1/a-h/a^2+h^2/a^3)
    E = -h^3/(a^3*(a+h)) ∧ |E| ≤ 2*|h|^3/|a|^4 := by
  have hp : 0 < |a| := abs_pos.mpr ha
  have ht : |a| ≤ |a+h|+|h| := by
    simpa using abs_sub (a+h) h
  have hl : |a|/2 ≤ |a+h| := by linarith
  have hb : a+h ≠ 0 := abs_pos.mp (by linarith)
  have he : 1/(a+h)-(1/a-h/a^2+h^2/a^3) = -h^3/(a^3*(a+h)) := by
    field_simp [ha, hb]
    ring
  dsimp
  refine ⟨he, ?_⟩
  rw [he, abs_div, abs_neg, abs_mul, abs_pow, abs_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hn := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 2*|h|^3*|a|^3 by positivity)
  nlinarith only [hn]

theorem uniform_reciprocal {m a h : ℝ} (hm : 0 < m) (ha : m ≤ a)
    (hh : |h| ≤ m/2) :
    |1/(a+h)-(1/a-h/a^2+h^2/a^3)| ≤ 2/m^4*|h|^3 := by
  have ha' : 0 < a := hm.trans_le ha
  have hb := (reciprocal_center ha'.ne' (by rw [abs_of_pos ha']; linarith : |h| ≤ |a|/2)).2
  rw [abs_of_pos ha'] at hb
  refine hb.trans ?_
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hm.le ha 4)

theorem factorial_error_tendsto (h : ℝ) :
    Tendsto (fun n : ℕ => Real.exp |h| * |h|^(n+1) / ((n+1).factorial : ℝ))
      atTop (𝓝 0) := by
  have hl := (FloorSemiring.tendsto_pow_div_factorial_atTop |h|).comp
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ n+1 by omega) tendsto_id)
  simpa [Function.comp_def, mul_div_assoc] using hl.const_mul (Real.exp |h|)

def BookEquivalent {α : Type*} (f g : α → ℝ) (F : Filter α) : Prop :=
  BookLittleO (fun x => f x-g x) g F

theorem equivalent_mathlib {α : Type*} {f g : α → ℝ} {F : Filter α} :
    BookEquivalent f g F ↔ f ~[F] g := littleO_mathlib _ _ _

theorem equivalent_quotient {α : Type*} {f g : α → ℝ} {F : Filter α}
    (hg : ∀ᶠ x in F, g x ≠ 0) :
    BookEquivalent f g F ↔ Tendsto (fun x => f x/g x) F (𝓝 1) := by
  have he : (fun x => (f x-g x)/g x) =ᶠ[F] fun x => f x/g x-1 := by
    filter_upwards [hg] with x hx
    field_simp [hx]
  rw [BookEquivalent, quotient_test hg, tendsto_congr' he, tendsto_sub_nhds_zero_iff]

theorem equivalent_operations {α : Type*} {F : Filter α} {f g u v : α → ℝ}
    (hf : BookEquivalent f g F) (hu : BookEquivalent u v F) :
    BookEquivalent (fun x => f x*u x) (fun x => g x*v x) F ∧
    BookEquivalent (fun x => f x/u x) (fun x => g x/v x) F := by
  simp only [equivalent_mathlib] at *
  exact ⟨hf.mul hu, hf.div hu⟩

theorem equivalent_laws {α : Type*} {F : Filter α} {f g u : α → ℝ} {L : ℝ} :
    BookEquivalent f f F ∧
    (BookEquivalent f g F → BookEquivalent g f F) ∧
    (BookEquivalent f g F → BookEquivalent g u F → BookEquivalent f u F) ∧
    (BookEquivalent f g F → Tendsto g F (𝓝 L) → Tendsto f F (𝓝 L)) := by
  simp only [equivalent_mathlib]
  exact ⟨IsEquivalent.refl, IsEquivalent.symm, IsEquivalent.trans,
    fun h hg => h.symm.tendsto_nhds hg⟩

theorem cancellation_example :
    BookEquivalent (fun h : ℝ => 1+h) (fun _ => 1) (𝓝 0) ∧
    (∀ h : ℝ, (1+h)-1=h ∧ (1:ℝ)-1=0) := by
  refine ⟨(equivalent_quotient (Eventually.of_forall (by simp))).2 ?_, ?_⟩
  · have hc : ContinuousAt (fun h : ℝ => (1:ℝ)+h) 0 := by fun_prop
    simpa using hc.tendsto
  · intro h
    constructor <;> ring

theorem reciprocal_cancellation :
    (∀ h : ℝ, h ≠ 0 → 1+h ≠ 0 →
      (1/(1+h)-1+h)/h^2 = 1/(1+h)) ∧
    Tendsto (fun h : ℝ => (1/(1+h)-1+h)/h^2) (𝓝[≠] 0) (𝓝 1) := by
  have he : ∀ h : ℝ, h ≠ 0 → 1+h ≠ 0 →
      (1/(1+h)-1+h)/h^2 = 1/(1+h) := by
    intro h hh hd
    field_simp [hh, hd]
    ring
  refine ⟨he, ?_⟩
  have hd : ContinuousAt (fun h : ℝ => (1:ℝ)+h) 0 := by fun_prop
  have hc : ContinuousAt (fun h : ℝ => 1/(1+h)) 0 :=
    continuousAt_const.div hd (by norm_num)
  have hn : ∀ᶠ h : ℝ in 𝓝[≠] 0, 1+h ≠ 0 :=
    ((continuousAt_const.add (continuousAt_id (x := (0:ℝ)))).eventually_ne
      (by norm_num : (1:ℝ)+0 ≠ 0)).filter_mono inf_le_left
  have hc' : Tendsto (fun h : ℝ => 1/(1+h)) (𝓝 0) (𝓝 1) := by simpa using hc.tendsto
  apply (hc'.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)).congr'
  filter_upwards [hn, self_mem_nhdsWithin] with h hd hh
  exact (he h hh hd).symm

theorem small_angle_certificate {h : ℝ} (hh : |h| ≤ 1/10) :
    |Real.sin h-h| ≤ 1/6000 := by
  have hb := Real.abs_sub_sin_le h
  rw [abs_sub_comm h (Real.sin h)] at hb
  have hp := pow_le_pow_left₀ (abs_nonneg h) hh 3
  norm_num at hp
  linarith

theorem interpolation_example :
    (∀ h ∈ ({-1, 0, 1} : Set ℝ), h^3 = h) ∧
    ¬ BookLittleO (fun h : ℝ => h^3-h) (fun h => h^2) (𝓝[≠] 0) := by
  constructor
  · intro h hh
    simp only [mem_insert_iff, mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl <;> norm_num
  · intro ho
    have hl := (littleO_mathlib _ _ _).1 ho
    have hp : (fun h : ℝ => h^3) =o[𝓝[≠] 0] fun h => h^2 :=
      (isLittleO_pow_pow (by decide : 2 < 3)).mono inf_le_left
    have hi : (fun h : ℝ => h) =o[𝓝[≠] 0] fun h => h^2 := by
      convert hp.sub hl using 1
      funext h
      simp [Pi.sub_apply]
    have hn : (fun h : ℝ => h) =o[𝓝[≠] 0] fun h => h :=
      hi.trans ((isLittleO_pow_id (by decide : 1 < 2)).mono inf_le_left)
    have hz : ∀ᶠ h : ℝ in 𝓝[≠] 0, h = 0 :=
      by
        filter_upwards [((littleO_mathlib _ _ _).2 hn) (1/2) (by norm_num)] with h hh
        exact abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg h))
    have hfalse : ∀ᶠ h : ℝ in 𝓝[≠] 0, False := by
      filter_upwards [hz, self_mem_nhdsWithin] with h he hn
      exact hn he
    exact hfalse.exists.elim (fun _ h => h)

theorem central_difference {f : ℝ → ℝ} {a h M : ℝ} (hh : h ≠ 0)
    (hf : ∀ t ∈ uIcc (a-h) (a+h), ContDiffAt ℝ 3 f t)
    (hM : ∀ t ∈ uIcc (a-h) (a+h), |iteratedDeriv 3 f t| ≤ M) :
    |(f (a+h)-f (a-h))/(2*h)-deriv f a| ≤ M/6*h^2 := by
  have ha : a ∈ uIcc (a-h) (a+h) := by
    rcases le_total h 0 with h₀ | h₀
    · rw [uIcc_comm, uIcc_of_le (by linarith : a+h ≤ a-h)]
      exact ⟨by linarith, by linarith⟩
    · rw [uIcc_of_le (by linarith : a-h ≤ a+h)]
      exact ⟨by linarith, by linarith⟩
  have bounds (x : ℝ) (hx : x ∈ uIcc (a-h) (a+h)) :
      |f x-bookTaylor f 2 a x| ≤ M/6*|x-a|^3 := by
    have hi : uIcc a x ⊆ uIcc (a-h) (a+h) := (convex_uIcc (𝕜 := ℝ) _ _).ordConnected.uIcc_subset ha hx
    simpa [Nat.factorial] using book_lagrange_bound (n := 2)
      (fun t ht => hf t (hi ht)) (fun t ht => hM t (hi ht))
  have hp := bounds _ right_mem_uIcc
  have hm := bounds _ left_mem_uIcc
  rw [add_sub_cancel_left] at hp
  rw [sub_sub_cancel_left, abs_neg] at hm
  have he : (f (a+h)-f (a-h))/(2*h)-deriv f a =
      ((f (a+h)-bookTaylor f 2 a (a+h))-(f (a-h)-bookTaylor f 2 a (a-h)))/(2*h) := by
    rw [bookTaylor_two, bookTaylor_two]
    field_simp [hh]
    ring
  rw [he, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2),
    div_le_iff₀ (by positivity)]
  calc
    _ ≤ |f (a+h)-bookTaylor f 2 a (a+h)| + |f (a-h)-bookTaylor f 2 a (a-h)| :=
      abs_sub _ _
    _ ≤ M/6*|h|^3 + M/6*|h|^3 := add_le_add hp hm
    _ = _ := by rw [← sq_abs h]; ring

theorem power_order {R : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h, |h| < 1 → |R h| ≤ C*|h|^3) :
    BookBigO R (fun h => h^3) (𝓝 0) ∧
    BookLittleO R (fun h => h^2) (𝓝 0) ∧ BookLittleO R id (𝓝 0) := by
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < 1 :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by norm_num)
  have h₂ := power_to_littleO (n := 2) one_pos hC hb
  refine ⟨⟨C, hC, ?_⟩, h₂, ?_⟩
  · filter_upwards [he] with h hh
    simpa [abs_pow] using hb h hh
  · apply (littleO_mathlib _ _ _).2
    exact ((littleO_mathlib _ _ _).1 h₂).trans (isLittleO_pow_id (by decide : 1 < 2))

theorem reciprocal_model :
    BookBigO (fun h : ℝ => 1/(1+h)-(1-h+h^2)) (fun h => h^3) (𝓝 0) ∧
    BookLittleO (fun h : ℝ => 1/(1+h)-(1-h+h^2)) (fun h => h^2) (𝓝 0) := by
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < 1/2 :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by norm_num)
  refine ⟨⟨2, by norm_num, ?_⟩, power_to_littleO (n := 2) (r := 1/2) (K := 2) (by norm_num) (by norm_num) ?_⟩
  · filter_upwards [he] with h hh
    simpa [abs_pow] using reciprocal_error h hh.le
  · exact fun h hh => reciprocal_error h hh.le

theorem eventual_nonzero_punctured : ∀ᶠ h : ℝ in 𝓝[≠] 0, h ≠ 0 :=
  self_mem_nhdsWithin

theorem quotient_from_power_bound {R : ℝ → ℝ} {n : ℕ} {K r : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hb : ∀ h, |h| < r → |R h| ≤ K*|h|^(n+1)) :
    Tendsto (fun h => R h/h^n) (𝓝[≠] 0) (𝓝 0) := by
  have h := (littleO_mathlib _ _ _).1 (power_to_littleO hr hK hb)
  apply (quotient_test (g := fun h : ℝ => h^n) ?_).1
  · exact (littleO_mathlib _ _ _).2 (h.mono inf_le_left)
  · filter_upwards [eventual_nonzero_punctured] with x hx
    exact pow_ne_zero _ hx

theorem exp_second_limit :
    Tendsto (fun h : ℝ => (Real.exp h-1-h)/h^2) (𝓝[≠] 0) (𝓝 (1/2)) := by
  have hz := quotient_from_power_bound (n := 2) (K := Real.exp 1 / 6) one_pos (by positivity)
    (fun h hh => exp_quadratic_bound hh.le)
  have hs : Tendsto (fun h : ℝ => 1/2+(Real.exp h-(1+h+h^2/2))/h^2)
      (𝓝[≠] 0) (𝓝 (1/2)) := by
    simpa using tendsto_const_nhds.add hz
  apply hs.congr'
  filter_upwards [eventual_nonzero_punctured] with h hh
  field_simp [hh]
  ring

theorem exp_three_tasks :
    Tendsto Real.exp (𝓝 0) (𝓝 1) ∧
    Tendsto (fun h : ℝ => (Real.exp h-1)/h) (𝓝[≠] 0) (𝓝 1) ∧
    Tendsto (fun h : ℝ => (Real.exp h-1-h)/h^2) (𝓝[≠] 0) (𝓝 (1/2)) := by
  refine ⟨by simpa using (Real.continuous_exp.continuousAt (x := 0)).tendsto, ?_, exp_second_limit⟩
  have h : Tendsto (slope Real.exp 0) (𝓝[≠] 0) (𝓝 1) := by
    simpa using (Real.hasDerivAt_exp 0).tendsto_slope
  apply h.congr
  intro x
  simp [slope_def_field, div_eq_mul_inv, mul_comm]

theorem peano_bound {f : ℝ → ℝ} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ (n+1) f a) :
    BookBigO (fun h => f (a+h)-bookTaylor f n a (a+h)) (fun h => h^(n+1)) (𝓝 0) ∧
    BookLittleO (fun h => f (a+h)-bookTaylor f n a (a+h)) (fun h => h^n) (𝓝 0) := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  have hc : ContinuousAt (fun t => |iteratedDeriv (n+1) f t|) a := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      (hf.continuousAt_iteratedFDeriv (k := n+1) (by simp)).norm
  let M := |iteratedDeriv (n+1) f a|+1
  have hm : 0 ≤ M := by dsimp [M]; positivity
  have hB : ∀ᶠ t in 𝓝 a, |iteratedDeriv (n+1) f t| < M :=
    hc.eventually_lt continuousAt_const (by dsimp [M]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hB)
  have bounds : ∀ h, |h| < r →
      |f (a+h)-bookTaylor f n a (a+h)| ≤ M/((n+1).factorial : ℝ)*|h|^(n+1) := by
    intro h hh
    have ha : a ∈ Metric.ball a r := Metric.mem_ball_self hr
    have hx : a+h ∈ Metric.ball a r := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have hi : uIcc a (a+h) ⊆ Metric.ball a r := (convex_ball a r).ordConnected.uIcc_subset ha hx
    have hb := book_lagrange_bound (n := n) (a := a) (x := a+h)
      (fun t ht => (hfs t (hball (hi ht)).1).contDiffAt
        (mem_of_superset (Metric.isOpen_ball.mem_nhds (hi ht))
          (fun _ hu => (hball hu).1)))
      (fun t ht => (hball (hi ht)).2.le)
    simpa using hb
  have hk : 0 ≤ M/((n+1).factorial : ℝ) := by positivity
  refine ⟨⟨_, hk, ?_⟩, power_to_littleO hr hk bounds⟩
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < r :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by simpa using hr)
  filter_upwards [he] with h hh
  simpa [abs_pow] using bounds h hh

theorem cos_fourth_limit :
    Tendsto (fun h : ℝ => (Real.cos h-1+h^2/2)/h^4) (𝓝[≠] 0) (𝓝 (1/24)) := by
  have d₁ : iteratedDeriv 1 Real.cos = fun h => -Real.sin h := by
    simp [iteratedDeriv_succ, Real.deriv_cos]
  have d₂ : iteratedDeriv 2 Real.cos = fun h => -Real.cos h := by
    rw [show 2 = 1+1 by decide, iteratedDeriv_succ, d₁]
    simp [deriv.neg, Real.deriv_sin]
  have d₃ : iteratedDeriv 3 Real.cos = Real.sin := by
    rw [show 3 = 2+1 by decide, iteratedDeriv_succ, d₂]
    simp [deriv.neg, Real.deriv_cos]
  have d₄ : iteratedDeriv 4 Real.cos = Real.cos := by
    rw [show 4 = 3+1 by decide, iteratedDeriv_succ, d₃, Real.deriv_sin]
  have d₅ : iteratedDeriv 5 Real.cos = fun h => -Real.sin h := by
    rw [show 5 = 4+1 by decide, iteratedDeriv_succ, d₄]
    simpa [iteratedDeriv_succ] using d₁
  have d₆ : iteratedDeriv 6 Real.cos = fun h => -Real.cos h := by
    rw [show 6 = 5+1 by decide, iteratedDeriv_succ, d₅]
    simp [deriv.neg, Real.deriv_sin]
  have hp (h : ℝ) : bookTaylor Real.cos 5 0 h = 1-h^2/2+h^4/24 := by
    norm_num [bookTaylor, Finset.sum_range_succ, d₁, d₂, d₃, d₄, d₅, Nat.factorial]
    ring
  have hb (h : ℝ) : |Real.cos h-(1-h^2/2+h^4/24)| ≤ (1/720)*|h|^6 := by
    have H := book_lagrange_bound (a := 0) (x := h) (M := 1) (n := 5)
      (fun t _ => Real.contDiff_cos.contDiffAt) (fun t _ => by simpa [d₆] using Real.abs_cos_le_one t)
    simpa [hp, Nat.factorial] using H
  have hz := quotient_from_power_bound (R := fun h => Real.cos h-(1-h^2/2+h^4/24))
    (n := 4) (K := 1/720) one_pos (by norm_num) (fun h hh => (hb h).trans
      (mul_le_mul_of_nonneg_left (by
        simpa [pow_succ' _ 5] using mul_le_of_le_one_left (pow_nonneg (abs_nonneg h) 5) hh.le)
        (by norm_num)))
  have h : Tendsto (fun h : ℝ => 1/24+(Real.cos h-(1-h^2/2+h^4/24))/h^4)
      (𝓝[≠] 0) (𝓝 (1/24)) := by simpa using tendsto_const_nhds.add hz
  apply h.congr'
  filter_upwards [eventual_nonzero_punctured] with h hh
  field_simp [hh]
  ring

theorem ratio_of_remainders :
    Tendsto (fun h : ℝ => (Real.exp h-1-h)/(1-Real.cos h)) (𝓝[≠] 0) (𝓝 1) := by
  have hp : Tendsto (fun h : ℝ => h^2) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun h : ℝ => h^2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  have hzero := hp.mul cos_fourth_limit
  have hd : Tendsto (fun h : ℝ => (1-Real.cos h)/h^2) (𝓝[≠] 0) (𝓝 (1/2)) := by
    have H : Tendsto (fun h : ℝ => 1/2-h^2*((Real.cos h-1+h^2/2)/h^4))
        (𝓝[≠] 0) (𝓝 (1/2)) := by simpa using tendsto_const_nhds.sub hzero
    apply H.congr'
    filter_upwards [eventual_nonzero_punctured] with h hh
    field_simp [hh]
    ring
  have H := exp_second_limit.div hd (by norm_num)
  have H' : Tendsto (fun h : ℝ => ((Real.exp h-1-h)/h^2)/((1-Real.cos h)/h^2))
      (𝓝[≠] 0) (𝓝 1) := by norm_num at H ⊢; exact H
  apply H'.congr'
  filter_upwards [eventual_nonzero_punctured] with h hh
  by_cases hz : 1-Real.cos h = 0
  · simp [hz]
  · field_simp [hh, hz]

theorem exp_square_composition :
    BookBigO (fun h : ℝ => Real.exp (h^2)-(1+h^2)) (fun h => h^4) (𝓝 0) := by
  let K := Real.exp 1/6+1/2
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < 1 :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [he] with h hh
  have h₂ : h^2 ≤ 1 := by nlinarith [(abs_lt.mp hh).1, (abs_lt.mp hh).2]
  have hb := exp_quadratic_bound (h := h^2) (r := 1) (by rwa [abs_of_nonneg (sq_nonneg h)])
  rw [abs_of_nonneg (sq_nonneg h)] at hb
  have ha : Real.exp (h^2)-(1+h^2) =
      Real.exp (h^2)-(1+h^2+(h^2)^2/2)+(h^2)^2/2 := by ring
  rw [ha, abs_of_nonneg (show 0 ≤ h^4 by positivity)]
  have hmul := mul_le_mul_of_nonneg_right h₂ (show 0 ≤ Real.exp 1/6*h^4 by positivity)
  have ht := abs_add_le (Real.exp (h^2)-(1+h^2+(h^2)^2/2)) ((h^2)^2/2)
  rw [abs_of_nonneg (by positivity : 0 ≤ (h^2)^2/2)] at ht
  dsimp [K]
  nlinarith only [hb, hmul, ht]

theorem polynomial_coefficients_zero (n : ℕ) (c : ℕ → ℝ)
    (hc : (fun h : ℝ => ∑ k ∈ Finset.range (n+1), c k*h^k)
      =o[𝓝[≠] 0] fun h => h^n) :
    ∀ k ≤ n, c k = 0 := by
  induction n generalizing c with
  | zero =>
    have h₀ : (fun _ : ℝ => c 0) =o[𝓝[≠] 0] (fun _ => (1:ℝ)) := by simpa using hc
    have ht := (isLittleO_one_iff ℝ).1 h₀
    have hlim : Tendsto (fun _ : ℝ => c 0) (𝓝[≠] 0) (𝓝 (c 0)) := tendsto_const_nhds
    exact fun k hk => by simpa [Nat.eq_zero_of_le_zero hk] using tendsto_nhds_unique hlim ht
  | succ n ih =>
    let P := fun h : ℝ => ∑ k ∈ Finset.range (n+1), c (k+1)*h^k
    have he (h : ℝ) : (∑ k ∈ Finset.range (n+2), c k*h^k) = c 0 + h*P h := by
      rw [Finset.sum_range_succ']
      unfold P
      rw [Finset.mul_sum]
      simp only [pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    have ht : Tendsto (fun h : ℝ => ∑ k ∈ Finset.range (n+2), c k*h^k)
        (𝓝[≠] 0) (𝓝 0) := by
      apply (isLittleO_one_iff ℝ).1
      exact hc.trans (by simpa using (isLittleO_pow_pow (by omega : 0 < n+1) (𝕜 := ℝ)).mono (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0))
    have hcont : ContinuousAt P 0 := by dsimp [P]; fun_prop
    have hlim : Tendsto (fun h : ℝ => c 0+h*P h) (𝓝[≠] 0) (𝓝 (c 0)) := by
      have H : ContinuousAt (fun h : ℝ => c 0+h*P h) 0 := by fun_prop
      simpa using H.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
    have hz : c 0 = 0 := tendsto_nhds_unique (hlim.congr (fun h => (he h).symm)) ht
    have hR : BookLittleO P (fun h => h^n) (𝓝[≠] 0) := by
      intro ε hε
      filter_upwards [((littleO_mathlib _ _ _).2 hc) ε hε, eventual_nonzero_punctured] with h hh hn
      rw [he, hz, zero_add, abs_mul, abs_pow, pow_succ] at hh
      refine le_of_mul_le_mul_left ?_ (abs_pos.mpr hn)
      simpa only [abs_pow, mul_assoc, mul_left_comm, mul_comm] using hh
    intro k hk
    cases k with
    | zero => exact hz
    | succ k => exact ih (fun k => c (k+1)) ((littleO_mathlib _ _ _).1 hR) k (by omega)

theorem polynomial_unique (n : ℕ) (a b : ℕ → ℝ) (f : ℝ → ℝ)
    (ha : BookLittleO (fun h => f h-∑ k ∈ Finset.range (n+1), a k*h^k)
      (fun h => h^n) (𝓝[≠] 0))
    (hb : BookLittleO (fun h => f h-∑ k ∈ Finset.range (n+1), b k*h^k)
      (fun h => h^n) (𝓝[≠] 0)) :
    ∀ k ≤ n, a k = b k := by
  have hc := ((littleO_mathlib _ _ _).1 hb).sub ((littleO_mathlib _ _ _).1 ha)
  have hz := polynomial_coefficients_zero n (fun k => a k-b k)
    (hc.congr_left (fun h => by
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring))
  exact fun k hk => sub_eq_zero.mp (hz k hk)

theorem reciprocal_budget_bounds {h : ℝ} (hh : |h| ≤ 1/2) :
    (|h|^2 ≤ 1/2000000 → |1/(1+h)-(1-h)| ≤ 1/1000000) ∧
    (|h|^3 ≤ 1/2000000 → |1/(1+h)-(1-h+h^2)| ≤ 1/1000000) := by
  constructor
  · intro hb
    exact (reciprocal_linear_error hh).trans (by linarith)
  · intro hb
    exact (reciprocal_error h hh).trans (by linarith)

theorem exp_sin_composition :
    BookBigO (fun h : ℝ => Real.exp (Real.sin h)-(1+h+h^2/2)) (fun h => h^3) (𝓝 0) := by
  refine ⟨Real.exp 1/6+1/3, by positivity, ?_⟩
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < 1 :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [he] with h hh
  let u := Real.sin h
  have hu : |u| ≤ |h| := Real.abs_sin_le_abs
  have hs : |u-h| ≤ |h|^3/6 := by rw [abs_sub_comm]; exact Real.abs_sub_sin_le h
  have hex := exp_quadratic_bound (h := u) (r := 1) (hu.trans hh.le)
  have hcube := pow_le_pow_left₀ (abs_nonneg u) hu 3
  have hb := hex.trans (mul_le_mul_of_nonneg_left hcube (show 0 ≤ Real.exp 1/6 by positivity))
  have hsum : |u+h| ≤ 2 := (abs_add_le u h).trans (by linarith)
  have hsq : |u^2-h^2| ≤ |h|^3/3 := by
    rw [show u^2-h^2=(u-h)*(u+h) by ring, abs_mul]
    have H := mul_le_mul hs hsum (abs_nonneg _) (by positivity : 0 ≤ |h|^3/6)
    linarith
  have hid : Real.exp u-(1+h+h^2/2) =
      (Real.exp u-(1+u+u^2/2))+(u-h)+(u^2-h^2)/2 := by ring
  rw [abs_pow]
  change |Real.exp u-(1+h+h^2/2)| ≤ (Real.exp 1/6+1/3)*|h|^3
  rw [hid]
  have H := (abs_add_le (_+_) ((u^2-h^2)/2)).trans
    (add_le_add (abs_add_le (Real.exp u-(1+u+u^2/2)) (u-h)) le_rfl)
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] at H
  linarith

theorem contDiff_characterization (n : ℕ) (f : ℝ → ℝ) :
    ContDiff ℝ n f ↔
      (∀ m ≤ n, Continuous (iteratedDeriv m f)) ∧
      (∀ m < n, Differentiable ℝ (iteratedDeriv m f)) :=
  contDiff_nat_iff_iteratedDeriv

noncomputable def flatExample (h : ℝ) : ℝ := expNegInvGlue (h^2)

theorem flat_example :
    (∀ n : ℕ, ContDiff ℝ n flatExample) ∧
    flatExample 0 = 0 ∧
    (∀ h ≠ 0, flatExample h = Real.exp (-1/h^2) ∧ 0 < flatExample h) := by
  refine ⟨?_, by simp [flatExample, expNegInvGlue.zero], ?_⟩
  · intro n
    exact expNegInvGlue.contDiff.comp (contDiff_id.pow 2)
  · intro h hh
    have hp : 0 < h^2 := sq_pos_of_ne_zero hh
    exact ⟨by simp [flatExample, expNegInvGlue, hp.not_ge, div_eq_mul_inv],
      expNegInvGlue.pos_of_pos hp⟩

theorem flat_littleO (n : ℕ) :
    BookLittleO flatExample (fun h => h^n) (𝓝[≠] 0) := by
  have hc : ContinuousAt (fun h : ℝ => h^2) 0 := by fun_prop
  have ht : Tendsto (fun h : ℝ => h^2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  have hpoly := (expNegInvGlue.tendsto_polynomial_inv_mul_zero
    ((Polynomial.X : Polynomial ℝ)^n)).comp ht
  have hpow : Tendsto (fun h : ℝ => h^n) (𝓝[≠] 0) (𝓝 ((0:ℝ)^n)) := by
    have hc' : ContinuousAt (fun h : ℝ => h^n) 0 := by fun_prop
    exact hc'.tendsto.mono_left nhdsWithin_le_nhds
  apply (quotient_test (g := fun h : ℝ => h^n) ?_).2
  · have H := hpow.mul hpoly
    simp only [mul_zero, Function.comp_apply, Polynomial.eval_pow, Polynomial.eval_X] at H
    apply H.congr'
    filter_upwards [eventual_nonzero_punctured] with h hh
    have he : h * (h^2)⁻¹ = h⁻¹ := by field_simp [hh]
    rw [← mul_assoc, ← mul_pow, he, inv_pow, div_eq_mul_inv, mul_comm]
    rfl
  · filter_upwards [eventual_nonzero_punctured] with h hh
    exact pow_ne_zero _ hh

theorem flat_derivatives_zero (n : ℕ) : iteratedDeriv n flatExample 0 = 0 := by
  have h := (peano_bound (n := n) ((flat_example.1 (n+1)).contDiffAt (x := 0))).2
  have h' : (fun h : ℝ => flatExample h-bookTaylor flatExample n 0 h)
      =o[𝓝[≠] 0] fun h => h^n := by
    have H := ((littleO_mathlib _ _ _).1 h).mono
      (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
    simpa using H
  have hc := ((littleO_mathlib _ _ _).1 (flat_littleO n)).sub h'
  have hz := polynomial_coefficients_zero n (fun k => iteratedDeriv k flatExample 0 / (k.factorial : ℝ))
    (hc.congr_left (fun h => by simp [bookTaylor, Pi.sub_apply])) n le_rfl
  exact (div_eq_zero_iff.mp hz).resolve_right (by positivity)

theorem first_nonzero_term {f : ℝ → ℝ} {a : ℝ} {n : ℕ} (hn : 0 < n)
    (hf : ContDiffAt ℝ (n+1) f a)
    (hv : ∀ k, 0 < k → k < n → iteratedDeriv k f a = 0) :
    Tendsto (fun h : ℝ => (f (a+h)-f a)/h^n) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv n f a / (n.factorial : ℝ))) := by
  let c := iteratedDeriv n f a / (n.factorial : ℝ)
  have hp (h : ℝ) : bookTaylor f n a (a+h) = f a+c*h^n := by
    rw [bookTaylor, Finset.sum_range_succ, add_sub_cancel_left]
    congr 1
    have hmem : 0 ∈ Finset.range n := Finset.mem_range.mpr hn
    rw [Finset.sum_eq_single_of_mem 0 hmem]
    · simp
    · intro k hk hk0
      simp [hv k (Nat.pos_of_ne_zero hk0) (Finset.mem_range.mp hk)]
  have hr := (peano_bound hf).2
  have hr' := ((littleO_mathlib _ _ _).1 hr).mono
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  have he : ∀ᶠ h : ℝ in 𝓝[≠] 0, h^n ≠ 0 := by
    filter_upwards [eventual_nonzero_punctured] with h hh
    exact pow_ne_zero n hh
  have hz := (quotient_test he).1 ((littleO_mathlib _ _ _).2 hr')
  have H : Tendsto (fun h : ℝ => c+(f (a+h)-bookTaylor f n a (a+h))/h^n)
      (𝓝[≠] 0) (𝓝 c) := by simpa using tendsto_const_nhds.add hz
  apply H.congr'
  filter_upwards [eventual_nonzero_punctured] with h hh
  rw [hp]
  field_simp [hh]
  ring

theorem higher_extrema {f : ℝ → ℝ} {a : ℝ} {n : ℕ} (hn : 0 < n)
    (hf : ContDiffAt ℝ (n+1) f a)
    (hv : ∀ k, 0 < k → k < n → iteratedDeriv k f a = 0)
    (hc : iteratedDeriv n f a ≠ 0) :
    (Even n → 0 < iteratedDeriv n f a →
      ∀ᶠ h : ℝ in 𝓝[≠] 0, f a < f (a+h)) ∧
    (Even n → iteratedDeriv n f a < 0 →
      ∀ᶠ h : ℝ in 𝓝[≠] 0, f (a+h) < f a) ∧
    (Odd n → ¬ IsLocalMin f a ∧ ¬ IsLocalMax f a) := by
  let q := fun h : ℝ => (f (a+h)-f a)/h^n
  let c := iteratedDeriv n f a / (n.factorial : ℝ)
  have hp : 0 < (n.factorial : ℝ) := by positivity
  have ht : Tendsto q (𝓝[≠] 0) (𝓝 c) := first_nonzero_term hn hf hv
  have pos (hc' : 0 < c) : ∀ᶠ h : ℝ in 𝓝[≠] 0, 0 < q h := ht.eventually (lt_mem_nhds hc')
  have neg (hc' : c < 0) : ∀ᶠ h : ℝ in 𝓝[≠] 0, q h < 0 := ht.eventually (gt_mem_nhds hc')
  have he (h : ℝ) (hh : h ≠ 0) : q h * h^n = f (a+h)-f a := by
    dsimp [q]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hh)
  refine ⟨?_, ?_, ?_⟩
  · intro hn' hd
    filter_upwards [pos (div_pos hd hp), eventual_nonzero_punctured] with h hq hh
    have hh' : 0 < h^n := lt_of_le_of_ne (hn'.pow_nonneg _) (pow_ne_zero _ hh).symm
    exact sub_pos.mp (he h hh ▸ mul_pos hq hh')
  · intro hn' hd
    filter_upwards [neg (div_neg_of_neg_of_pos hd hp), eventual_nonzero_punctured] with h hq hh
    have hh' : 0 < h^n := lt_of_le_of_ne (hn'.pow_nonneg _) (pow_ne_zero _ hh).symm
    exact sub_neg.mp (he h hh ▸ mul_neg_of_neg_of_pos hq hh')
  · intro ho
    have getPos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    have getNeg : ∀ᶠ h : ℝ in 𝓝[<] 0, h < 0 := self_mem_nhdsWithin
    have extract (hs : ∀ᶠ h : ℝ in 𝓝[<] 0, f (a+h) < f a)
        (hb : ∀ᶠ h : ℝ in 𝓝[>] 0, f a < f (a+h)) :
        ¬ IsLocalMin f a ∧ ¬ IsLocalMax f a := by
      have hcont : ContinuousAt (fun h : ℝ => a+h) 0 := by fun_prop
      have hs' : Tendsto (fun h : ℝ => a+h) (𝓝 0) (𝓝 a) := by simpa using hcont.tendsto
      constructor
      · intro hm
        have he := (hs'.eventually hm).filter_mono (nhdsWithin_le_nhds : 𝓝[<] (0:ℝ) ≤ 𝓝 0)
        obtain ⟨h, h₁, h₂⟩ := (hs.and he).exists
        exact (not_le_of_gt h₁) h₂
      · intro hm
        have he := (hs'.eventually hm).filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
        obtain ⟨h, h₁, h₂⟩ := (hb.and he).exists
        exact (not_le_of_gt h₁) h₂
    rcases lt_or_gt_of_ne hc with hd | hd
    · have hs : ∀ᶠ h : ℝ in 𝓝[>] 0, f (a+h) < f a := by
        filter_upwards [(neg (div_neg_of_neg_of_pos hd hp)).filter_mono (nhdsGT_le_nhdsNE _), getPos] with h hq hh
        exact sub_neg.mp (he h hh.ne' ▸ mul_neg_of_neg_of_pos hq (pow_pos hh _))
      have hb : ∀ᶠ h : ℝ in 𝓝[<] 0, f a < f (a+h) := by
        filter_upwards [(neg (div_neg_of_neg_of_pos hd hp)).filter_mono (nhdsLT_le_nhdsNE _), getNeg] with h hq hh
        exact sub_pos.mp (he h hh.ne ▸ mul_pos_of_neg_of_neg hq (ho.pow_neg hh))
      have hcont : ContinuousAt (fun h : ℝ => a+h) 0 := by fun_prop
      have ht' : Tendsto (fun h : ℝ => a+h) (𝓝 0) (𝓝 a) := by simpa using hcont.tendsto
      constructor
      · intro hm
        obtain ⟨_, h₁, h₂⟩ := (hs.and ((ht'.eventually hm).filter_mono nhdsWithin_le_nhds)).exists
        exact (not_le_of_gt h₁) h₂
      · intro hm
        obtain ⟨_, h₁, h₂⟩ := (hb.and ((ht'.eventually hm).filter_mono nhdsWithin_le_nhds)).exists
        exact (not_le_of_gt h₁) h₂
    · apply extract
      · filter_upwards [(pos (div_pos hd hp)).filter_mono (nhdsLT_le_nhdsNE _), getNeg] with h hq hh
        exact sub_neg.mp (he h hh.ne ▸ mul_neg_of_pos_of_neg hq (ho.pow_neg hh))
      · filter_upwards [(pos (div_pos hd hp)).filter_mono (nhdsGT_le_nhdsNE _), getPos] with h hq hh
        exact sub_pos.mp (he h hh.ne' ▸ mul_pos hq (pow_pos hh _))

theorem cubic_taylor (a h : ℝ) :
    bookTaylor (fun x => x^3) 2 a (a+h) = a^3+3*a^2*h+3*a*h^2 ∧
    bookTaylor (fun x => x^3) 3 a (a+h) = (a+h)^3 := by
  constructor
  all_goals
    norm_num [bookTaylor, Finset.sum_range_succ, Nat.descFactorial, Nat.factorial]
    ring_nf <;> simp

theorem linear_error_radius {h M η E : ℝ} (hM : 0 < M) (hη : 0 < η)
    (hE : |E| ≤ M/2*h^2) (hh : |h| ≤ Real.sqrt (2*η/M)) : |E| ≤ η := by
  have hs := pow_le_pow_left₀ (abs_nonneg h) hh 2
  rw [sq_abs, Real.sq_sqrt (by positivity)] at hs
  have hb := (le_div_iff₀ hM).mp hs
  linarith

theorem small_algebra {α : Type*} {F : Filter α} {r s g : α → ℝ}
    (hr : BookLittleO r g F) :
    (BookLittleO s g F → BookLittleO (fun x => r x+s x) g F) ∧
    (∀ c : ℝ, BookLittleO (fun x => c*r x) g F) :=
  ⟨littleO_add hr, littleO_const_mul hr⟩

theorem mixed_product {α : Type*} {F : Filter α} {r g s k : α → ℝ}
    (hr : BookLittleO r g F) (hs : BookBigO s k F) :
    BookLittleO (fun x => r x*s x) (fun x => g x*k x) F :=
  littleO_mul_bigO hr hs

theorem bookTaylor_center_derivative (f : ℝ → ℝ) {n j : ℕ} (a : ℝ)
    (hj : j ≤ n) : iteratedDeriv j (bookTaylor f n a) a = iteratedDeriv j f a := by
  classical
  unfold bookTaylor
  rw [iteratedDeriv_fun_sum (fun k _ => by fun_prop)]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))]
  · rw [iteratedDeriv_const_mul_field]
    change iteratedDeriv j f a / (j.factorial : ℝ) *
      iteratedDeriv j (fun x : ℝ => (x-a)^j) a = _
    rw [iteratedDeriv_comp_sub_const j (fun x : ℝ => x^j) a]
    simp only [sub_self, iteratedDeriv_fun_pow_zero, if_pos rfl]
    exact div_mul_cancel₀ _ (by positivity)
  · intro k _ hkj
    rw [iteratedDeriv_const_mul_field]
    change iteratedDeriv k f a / (k.factorial : ℝ) *
      iteratedDeriv j (fun x : ℝ => (x-a)^k) a = 0
    rw [iteratedDeriv_comp_sub_const j (fun x : ℝ => x^k) a]
    simp only [sub_self, iteratedDeriv_fun_pow_zero, if_neg hkj.symm, Nat.cast_zero, mul_zero]

def BookContDiffOn (f : ℝ → ℝ) (n : ℕ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ContDiffAt ℝ n f x

theorem bookContDiffOn_mathlib {f : ℝ → ℝ} {n : ℕ} {S : Set ℝ} (hS : IsOpen S) :
    BookContDiffOn f n S ↔ ContDiffOn ℝ n f S :=
  hS.contDiffOn_iff.symm

theorem equivalent_ratio_operations {α : Type*} {F : Filter α} {f g u v : α → ℝ}
    (hf : Tendsto (fun x => f x/g x) F (𝓝 1))
    (hu : Tendsto (fun x => u x/v x) F (𝓝 1))
    (hne : ∀ᶠ x in F, g x ≠ 0 ∧ u x ≠ 0 ∧ v x ≠ 0) :
    Tendsto (fun x => (f x*u x)/(g x*v x)) F (𝓝 1) ∧
    Tendsto (fun x => (f x/u x)/(g x/v x)) F (𝓝 1) := by
  have hm : Tendsto (fun x => (f x/g x)*(u x/v x)) F (𝓝 1) := by simpa using hf.mul hu
  have hd : Tendsto (fun x => (f x/g x)/(u x/v x)) F (𝓝 1) := by
    have H := hf.div hu (by norm_num)
    rw [div_self (by norm_num : (1:ℝ) ≠ 0)] at H
    exact H.congr (fun _ => rfl)
  refine ⟨hm.congr' ?_, hd.congr' ?_⟩
  · filter_upwards [hne] with x ⟨hg, _, hv⟩
    field_simp [hg, hv]
  · filter_upwards [hne] with x ⟨hg, hx, hv⟩
    field_simp [hg, hx, hv]

end Ch08
