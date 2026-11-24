import Textbook.Ch07.Applications
import Textbook.Ch05.ClosedIntervals

namespace Ch07
open Ch06 Ch02 Ch03 Ch03Approach Set Filter
open scoped Topology

theorem ratio_limit_at_center {f g : ℝ → ℝ} {a p q : ℝ}
    (hf : HasDerivative f a p) (hg : HasDerivative g a q)
    (hf₀ : f a = 0) (hg₀ : g a = 0) (hq : q ≠ 0) :
    Approaches (fun h => f (a+h)/g (a+h)) (punctured 0) (neighborhoodFilter (p/q)) := by
  have hf' := (derivative_increment_iff _ _ _).1 hf
  have hg' := (derivative_increment_iff _ _ _).1 hg
  simp only [hf₀,hg₀,sub_zero] at hf' hg'
  have h := Ch04.limit_div hf' hg' hq
  apply Ch03Rules.approaches_congr (F := punctured 0) ?_ h
  refine ⟨1,zero_lt_one,fun x _ hx => ?_⟩
  change x ≠ 0 at hx
  change (f (a+x)/x)/(g (a+x)/x) = f (a+x)/g (a+x)
  by_cases hgx : g (a+x) = 0
  · simp [hgx]
  · field_simp [hx,hgx]

theorem parametric_rate (f g df dg : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ x ∈ Ioo a b, HasDerivative f x (df x))
    (hdg : ∀ x ∈ Ioo a b, HasDerivative g x (dg x))
    (hn : ∀ x ∈ Ioo a b, dg x ≠ 0) :
    g b ≠ g a ∧ ∃ c ∈ Ioo a b, (f b-f a)/(g b-g a) = df c/dg c := by
  have hb : g b ≠ g a := by
    intro he
    obtain ⟨c,hc,h⟩ := mean_value_book g dg hab hg hdg
    exact (mul_ne_zero (hn c hc) (sub_ne_zero.mpr hab.ne')) (by linarith)
  obtain ⟨c,hc,h⟩ := cauchy_mean_value_book f g df dg hab hf hg hdf hdg
  exact ⟨hb,c,hc,(div_eq_div_iff (sub_ne_zero.mpr hb) (hn c hc)).2
    (by simpa only [mul_comm] using h)⟩

theorem quadratic_design :
    GlobalMinimumOn cost (Icc (0:ℝ) 5) 3 ∧
      (∀ x ∈ Icc (0:ℝ) 5, cost x = 2 ↔ x = 3) ∧
      cost 0 = 11 ∧ cost 5 = 6 := by
  refine ⟨⟨by constructor <;> norm_num,fun x _ => ?_⟩,
    fun x _ => cost_eq_minimum x,by norm_num [cost],by norm_num [cost]⟩
  simpa only [show cost 3 = 2 by norm_num [cost]] using cost_minimum x

theorem perturbed_design (actual : ℝ → ℝ) (y η : ℝ)
    (hy : y ∈ Icc (0:ℝ) 5) (hη : 0 ≤ η)
    (herr : ∀ x ∈ Icc (0:ℝ) 5, |actual x-cost x| ≤ η)
    (hopt : actual y ≤ actual 3) :
    |y-3| ≤ Real.sqrt (2*η) := by
  have h3 : (3:ℝ) ∈ Icc (0:ℝ) 5 := by constructor <;> norm_num
  have hY := (abs_le.mp (herr y hy)).1
  have h3' := (abs_le.mp (herr 3 h3)).2
  have h := perturbed_cost_bound y η (actual y) (actual 3) (by linarith) hopt (by linarith)
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).2
  rwa [sq_abs]

theorem box_unique_minimum (V r x : ℝ) (hr : 0 < r) (hx : 0 < x) (hV : r^3 = 2*V) :
    3*r^2 ≤ x^2+4*V/x ∧ (x^2+4*V/x = 3*r^2 ↔ x = r) ∧ V/r^2 = r/2 := by
  have hcoef : 4*V = 2*r^3 := by linarith
  rw [hcoef]
  have he := box_identity x r hx.ne'
  refine ⟨box_minimum x r hx hr,?_,?_⟩
  · constructor
    · intro h
      have hz : (x-r)^2*(x+2*r)/x = 0 := by linarith
      have hm := (div_eq_zero_iff.mp hz).resolve_right hx.ne'
      have hp : x+2*r ≠ 0 := by positivity
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hm).resolve_right hp))
    · intro h
      subst x
      simp only [sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,zero_div] at he
      linarith
  · apply (div_eq_iff (sq_pos_of_ne_zero hr.ne').ne').2
    nlinarith

theorem square_root_arcsin_derivatives (b : ℝ) :
    (0 < b → HasDerivative Real.sqrt b (1/(2*Real.sqrt b))) ∧
    (-1 < b → b < 1 → HasDerivative Real.arcsin b (1/Real.sqrt (1-b^2))) := by
  refine ⟨derivative_sqrt b,fun h₁ h₂ => ?_⟩
  exact (derivative_mathlib _ _ _).2 (Real.hasDerivAt_arcsin h₁.ne' h₂.ne)

theorem log_composition_derivative (a : ℝ) :
    HasDerivative (fun x => Real.log (1+x^2)) a (2*a/(1+a^2)) := by
  apply (derivative_mathlib _ _ _).2
  have hu := ((hasDerivAt_id a).fun_pow 2).const_add 1
  have h := hu.log (show 1+id a^2 ≠ 0 by positivity)
  convert h using 1 <;> (try simp only [id_eq]) <;> ring

theorem closed_interval_candidates {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) :
    (∃ x ∈ Icc a b, IsMinOn f (Icc a b) x) ∧
    (∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x) ∧
    ∀ x ∈ Icc a b, IsMinOn f (Icc a b) x ∨ IsMaxOn f (Icc a b) x →
      x = a ∨ x = b ∨ ¬ DifferentiableAt ℝ f x ∨ Stationary f x := by
  refine ⟨Ch05ClosedIntervals.minimum_on_interval hab.le hc,
    Ch05ClosedIntervals.maximum_on_interval hab.le hc,?_⟩
  intro x hx he
  by_cases ha : x = a
  · exact Or.inl ha
  by_cases hb : x = b
  · exact Or.inr (Or.inl hb)
  by_cases hd : DifferentiableAt ℝ f x
  · have hx' : x ∈ interior (Icc a b) := by
      rw [interior_Icc]
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm ha),lt_of_le_of_ne hx.2 hb⟩
    have hn := mem_interior_iff_mem_nhds.mp hx'
    have hs : HasDerivative f x (deriv f x) := (derivative_mathlib _ _ _).2 hd.hasDerivAt
    have hz := fermat_book (he.imp (fun h => h.isLocalMin hn) (fun h => h.isLocalMax hn)) hs
    rw [hz] at hs
    exact Or.inr (Or.inr (Or.inr hs))
  · exact Or.inr (Or.inr (Or.inl hd))

theorem decay_lipschitz (A k x y : ℝ) (hA : 0 < A) (hk : 0 < k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |A*Real.exp (-k*y)-A*Real.exp (-k*x)| ≤ k*A*|y-x| := by
  refine interval_lipschitz (S := Ici (0:ℝ)) (f := fun t => A*Real.exp (-k*t))
    (M := k*A) (df := fun t => -k*A*Real.exp (-k*t)) (convex_Ici _)
    ?_ ?_ ?_ ?_ x hx y hy
  · exact (show Continuous (fun t : ℝ => A*Real.exp (-k*t)) by fun_prop).continuousOn
  · positivity
  · intro t _
    exact (exp_decay_derivative A k t hA hk).1
  · intro t ht
    have ht' : 0 ≤ t := interior_subset ht
    have hE : Real.exp (-k*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he : |-k*A*Real.exp (-k*t)| = k*A*Real.exp (-k*t) := by
      rw [abs_of_neg (exp_decay_derivative A k t hA hk).2]
      ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hE

theorem reciprocal_working_range (m x y : ℝ) (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |1/x-1/y| ≤ |x-y|/m^2 := by
  have hx' := hm.trans_le hx
  have hy' := hm.trans_le hy
  have he : 1/x-1/y = (y-x)/(x*y) := by
    field_simp [hx'.ne',hy'.ne']
  rw [he,abs_div,abs_of_pos (mul_pos hx' hy'),abs_sub_comm y x]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_ne_zero hm.ne')
  nlinarith [mul_le_mul hx hy hm.le hx'.le]

theorem reciprocal_no_global_bound :
    ¬ IsLipschitzOn (fun x : ℝ => 1/x) (Ioi 0) := by
  rintro ⟨M,hM,h⟩
  let x : ℝ := 1/(M+1)
  have hp : 0 < M+1 := by linarith
  have hx : 0 < x := one_div_pos.mpr hp
  have hx1 : x ≤ 1 := (div_le_iff₀ hp).2 (by linarith)
  have H := h x hx (x/2) (half_pos hx)
  have he : 1/(x/2)-1/x = 1/x := by field_simp [hx.ne'] <;> ring
  rw [he,abs_of_pos (one_div_pos.mpr hx),abs_of_neg (by linarith : x/2-x < 0)] at H
  have hbound : M * (-(x/2-x)) ≤ M/2 := by
    nlinarith [mul_le_mul_of_nonneg_left (show -(x/2-x) ≤ 1/2 by linarith) hM]
  have he' : 1/x = M+1 := by simp [x,one_div]
  linarith

theorem cubic_residual_certificate (r : ℝ)
    (hr : Ch05ClosedIntervals.rootPolynomial r = 0) :
    (0.68 : ℝ) < r ∧ r ≤ 0.685568 := by
  let f := Ch05ClosedIntervals.rootPolynomial
  have hl : f 0.68 < f r := by
    change Ch05ClosedIntervals.rootPolynomial 0.68 < Ch05ClosedIntervals.rootPolynomial r
    rw [hr]
    norm_num [Ch05ClosedIntervals.rootPolynomial]
  refine ⟨Ch05ClosedIntervals.rootPolynomial_strictMono.lt_iff_lt.mp hl,?_⟩
  have hd (x : ℝ) : HasDerivative f x (3*x^2+1) := by
    apply (derivative_mathlib _ _ _).2
    have hh := (((hasDerivAt_id x).fun_pow 3).add (hasDerivAt_id x)).sub_const 1
    convert hh using 1
    · rfl
    · simp only [id_eq]
      ring
  have hh := residual_bound (S := univ) (m := 1) (df := fun x => 3*x^2+1)
    convex_univ (show Continuous f by unfold f Ch05ClosedIntervals.rootPolynomial; fun_prop).continuousOn
    zero_lt_one (fun x _ => hd x) (fun x _ => by nlinarith [sq_nonneg x])
    (mem_univ r) hr 0.68 (mem_univ _)
  change |(0.68:ℝ)-r| ≤ |Ch05ClosedIntervals.rootPolynomial 0.68|/1 at hh
  norm_num [Ch05ClosedIntervals.rootPolynomial] at hh
  linarith [(abs_le.mp hh).1]

theorem cubic_closed_interval (x : ℝ) (hx : x ∈ Icc (-2:ℝ) 2) :
    -2 ≤ x^3-3*x ∧ x^3-3*x ≤ 2 ∧
    (x^3-3*x = -2 ↔ x = -2 ∨ x = 1) ∧
    (x^3-3*x = 2 ↔ x = -1 ∨ x = 2) := by
  have hL : x^3-3*x+2 = (x+2)*(x-1)^2 := by ring
  have hR : 2-(x^3-3*x) = (2-x)*(x+1)^2 := by ring
  have hLo : 0 ≤ (x+2)*(x-1)^2 := mul_nonneg (by linarith [hx.1]) (sq_nonneg _)
  have hHi : 0 ≤ (2-x)*(x+1)^2 := mul_nonneg (by linarith [hx.2]) (sq_nonneg _)
  refine ⟨by linarith,by linarith,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro h
    have hz : (x+2)*(x-1)^2 = 0 := by linarith
    rcases mul_eq_zero.mp hz with hz | hz
    · left; linarith
    · exact Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro (rfl | rfl) <;> norm_num
  · intro h
    have hz : (2-x)*(x+1)^2 = 0 := by linarith
    rcases mul_eq_zero.mp hz with hz | hz
    · right; linarith
    · left; linarith [sq_eq_zero_iff.mp hz]
  · rintro (rfl | rfl) <;> norm_num

theorem cubic_stationary_points (x : ℝ) :
    HasDerivative (fun t : ℝ => t^3-3*t) x (3*(x^2-1)) ∧
      (3*(x^2-1) = 0 ↔ x = -1 ∨ x = 1) := by
  constructor
  · apply (derivative_mathlib _ _ _).2
    have h := ((hasDerivAt_id x).fun_pow 3).sub ((hasDerivAt_id x).const_mul 3)
    convert h using 1
    · rfl
    · simp only [id_eq]
      ring
  · constructor
    · intro h
      have hz : (x-1)*(x+1) = 0 := by nlinarith
      exact (mul_eq_zero.mp hz).elim (fun h => Or.inr (by linarith)) (fun h => Or.inl (by linarith))
    · rintro (rfl | rfl) <;> norm_num

theorem fourth_and_cube_tests :
    StrictLocalMinimum (fun x : ℝ => x^4) 0 ∧
    StrictLocalMinimum (fun x : ℝ => -(-(x^4))) 0 ∧
    ¬ IsLocalMin (fun x : ℝ => x^3) 0 ∧ ¬ IsLocalMax (fun x : ℝ => x^3) 0 := by
  have h4 : StrictLocalMinimum (fun x : ℝ => x^4) 0 := by
    refine ⟨1,zero_lt_one,fun x hx _ => ?_⟩
    simp only [sub_zero] at hx
    change (0:ℝ)^4 < x^4
    have he : x^4 = (x^2)^2 := by ring
    rw [he]
    norm_num
    exact sq_pos_of_ne_zero (sq_pos_of_ne_zero (abs_pos.mp hx)).ne'
  refine ⟨h4,by simpa using h4,?_,?_⟩
  · intro H
    obtain ⟨δ,hδ,H⟩ := Metric.eventually_nhds_iff.1 H
    have h := H (show dist (-(δ/2)) 0 < δ by
      rw [Real.dist_eq,sub_zero,abs_neg,abs_of_pos (half_pos hδ)]
      linarith)
    have hneg := (cubic_tangent_sign (-(δ/2))).1 (by linarith)
    norm_num at h
    linarith
  · intro H
    obtain ⟨δ,hδ,H⟩ := Metric.eventually_nhds_iff.1 H
    have h := H (show dist (δ/2) 0 < δ by
      rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]
      linarith)
    have hp : 0 < (δ/2)^3 := pow_pos (half_pos hδ) _
    norm_num at h
    linarith

theorem quadratic_growth {f df ddf : ℝ → ℝ} {S : Set ℝ} {a m : ℝ}
    (hS : Convex ℝ S) (hc : ContinuousOn f S) (ha : a ∈ interior S) (h₀ : df a = 0)
    (hd : ∀ x ∈ interior S, HasDerivative f x (df x))
    (hdd : ∀ x ∈ interior S, HasDerivative df x (ddf x))
    (hm : ∀ x ∈ interior S, m ≤ ddf x) :
    ∀ x ∈ S, f a+(m/2)*(x-a)^2 ≤ f x := by
  let G : ℝ → ℝ := fun x => f x-(m/2)*(x-a)^2
  let D : ℝ → ℝ := fun x => df x-m*(x-a)
  have hG : ContinuousOn G S := hc.sub (by fun_prop)
  have hD : ContinuousOn D (interior S) := by
    intro x hx
    have hdf := ((derivative_mathlib _ _ _).1 (hdd x hx)).continuousAt
    exact (hdf.sub (by fun_prop : ContinuousAt (fun x : ℝ => m*(x-a)) x)).continuousWithinAt
  have hG' (x : ℝ) (hx : x ∈ interior S) : HasDerivative G x (D x) := by
    apply (derivative_mathlib _ _ _).2
    have hp := (((hasDerivAt_id x).sub_const a).fun_pow 2).const_mul (m/2)
    convert ((derivative_mathlib _ _ _).1 (hd x hx)).sub hp using 1
    · rfl
    · simp only [D,id_eq]
      ring
  have hD' (x : ℝ) (hx : x ∈ interior S) : HasDerivative D x (ddf x-m) := by
    apply (derivative_mathlib _ _ _).2
    have hp := ((hasDerivAt_id x).sub_const a).const_mul m
    change HasDerivAt (df - fun y => m*(y-a)) (ddf x-m) x
    simpa only [id_eq,mul_one] using ((derivative_mathlib _ _ _).1 (hdd x hx)).sub hp
  have hmono : MonotoneOn D (interior S) :=
    (derivative_sign_monotonicity hS.interior hD
      (fun x hx => hD' x (interior_subset hx))).1
      (fun x hx => sub_nonneg.mpr (hm x (interior_subset hx)))
  have hz : D a = 0 := by simp [D,h₀]
  intro x hx
  have ha' := interior_subset ha
  have he : G a ≤ G x := by
    rcases lt_trichotomy a x with h | h | h
    · have hsub : Icc a x ⊆ S := hS.ordConnected.out ha' hx
      have hi : Ioo a x ⊆ interior S :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hsub⟩
      obtain ⟨c,hc',he⟩ := mean_value_book G D h (hG.mono hsub) (fun t ht => hG' t (hi ht))
      have hp : 0 ≤ D c := hz ▸ hmono ha (hi hc') hc'.1.le
      linarith [mul_nonneg hp (sub_nonneg.mpr h.le)]
    · simp [h]
    · have hsub : Icc x a ⊆ S := hS.ordConnected.out hx ha'
      have hi : Ioo x a ⊆ interior S :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hsub⟩
      obtain ⟨c,hc',he⟩ := mean_value_book G D h (hG.mono hsub) (fun t ht => hG' t (hi ht))
      have hp : D c ≤ 0 := hz ▸ hmono (hi hc') ha hc'.2.le
      linarith [mul_nonpos_of_nonpos_of_nonneg hp (sub_nonneg.mpr h.le)]
  simp only [G,sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,sub_zero] at he
  linarith

theorem inverse_continuous_at_interior {f : ℝ → ℝ} {S : Set ℝ} {a : ℝ}
    (hS : Convex ℝ S) (hc : ContinuousOn f S)
    (hm : StrictMonoOn f S ∨ StrictAntiOn f S) (ha : a ∈ interior S) :
    ∃ g : ℝ → ℝ, g (f a) = a ∧ ContinuousAt g (f a) ∧
      ∃ δ > 0, ∀ y, |y-f a| < δ → g y ∈ S ∧ f (g y) = y := by
  classical
  let g := Function.invFunOn f S
  have ha' := interior_subset ha
  have hinj : InjOn f S := hm.elim StrictMonoOn.injOn StrictAntiOn.injOn
  have hga : g (f a) = a := hinj.leftInvOn_invFunOn ha'
  have hn : S ∈ 𝓝 a := mem_interior_iff_mem_nhds.mp ha
  obtain ⟨ρ,hρ,hρS⟩ := Metric.mem_nhds_iff.mp hn
  have H (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) :
      ∃ δ > 0, ∀ y, |y-f a| < δ → g y ∈ S ∧ f (g y) = y ∧ |g y-a| ≤ r := by
    have hl : a-r ∈ S := hρS (by
      change dist (a-r) a < ρ
      rw [Real.dist_eq,show a-r-a = -r by ring,abs_neg,abs_of_pos hr]
      exact hrρ)
    have hu : a+r ∈ S := hρS (by
      change dist (a+r) a < ρ
      rw [Real.dist_eq,show a+r-a = r by ring,abs_of_pos hr]
      exact hrρ)
    let lo := min (f (a-r)) (f (a+r))
    let hi := max (f (a-r)) (f (a+r))
    have hb : lo < f a ∧ f a < hi := by
      rcases hm with h | h
      · exact ⟨(min_le_left _ _).trans_lt (h hl ha' (by linarith)),
          (h ha' hu (by linarith)).trans_le (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans_lt (h ha' hu (by linarith)),
          (h hl ha' (by linarith)).trans_le (le_max_left _ _)⟩
    have hsub : Icc (a-r) (a+r) ⊆ S := hS.ordConnected.out hl hu
    refine ⟨min (f a-lo) (hi-f a),lt_min (sub_pos.mpr hb.1) (sub_pos.mpr hb.2),fun y hy => ?_⟩
    have hyl := (abs_lt.mp (hy.trans_le (min_le_left _ _))).1
    have hyu := (abs_lt.mp (hy.trans_le (min_le_right _ _))).2
    obtain ⟨x,hx,he⟩ := Ch05ClosedIntervals.intermediate_on_interval
      (by linarith : a-r ≤ a+r) (hc.mono hsub)
      (show y ∈ Icc lo hi from ⟨by linarith,by linarith⟩)
    have he' : g y = x := by rw [← he]; exact hinj.leftInvOn_invFunOn (hsub hx)
    rw [he',he]
    exact ⟨hsub hx,rfl,abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  refine ⟨g,hga,Metric.continuousAt_iff.2 ?_,?_⟩
  · intro ε hε
    obtain ⟨δ,hδ,h⟩ := H (min ε ρ/2) (half_pos (lt_min hε hρ))
      ((half_lt_self (lt_min hε hρ)).trans_le (min_le_right _ _))
    refine ⟨δ,hδ,fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    rw [hga]
    exact (h y hy).2.2.trans_lt ((half_lt_self (lt_min hε hρ)).trans_le (min_le_left _ _))
  · obtain ⟨δ,hδ,h⟩ := H (ρ/2) (half_pos hρ) (half_lt_self hρ)
    exact ⟨δ,hδ,fun y hy => ⟨(h y hy).1,(h y hy).2.1⟩⟩

noncomputable def rolleJump (x : ℝ) : ℝ := if x = 1 then 0 else x

theorem rolle_counterexamples :
    ContinuousOn (abs : ℝ → ℝ) (Icc (-1:ℝ) 1) ∧
    |(-1:ℝ)| = |(1:ℝ)| ∧
    (¬ ∃ x ∈ Ioo (-1:ℝ) 1, HasDerivative abs x 0) ∧
    rolleJump 0 = rolleJump 1 ∧
    (∀ x ∈ Ioo (0:ℝ) 1, HasDerivative rolleJump x 1) ∧
    (¬ ContinuousOn rolleJump (Icc (0:ℝ) 1)) ∧
    ¬ ∃ x ∈ Ioo (0:ℝ) 1, HasDerivative rolleJump x 0 := by
  have hJ (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : HasDerivative rolleJump x 1 := by
    apply (derivative_locality (f := id) (g := rolleJump) (a := x) (d := 1) ?_).1 (derivative_id x)
    refine ⟨1-x,sub_pos.mpr hx.2,fun t ht => ?_⟩
    have ht' := (abs_lt.mp ht).2
    simp [rolleJump,show t ≠ 1 by intro h; linarith]
  have he : rolleJump 0 = rolleJump 1 := by norm_num [rolleJump]
  have hn : ¬ ∃ x ∈ Ioo (0:ℝ) 1, HasDerivative rolleJump x 0 := by
    rintro ⟨x,hx,h⟩
    exact one_ne_zero (derivative_unique (hJ x hx) h)
  refine ⟨continuous_abs.continuousOn,by norm_num,?_,he,hJ,?_,hn⟩
  · rintro ⟨x,_,hd⟩
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have hneg : HasDerivative abs x (-1) := by
        have h : HasDerivative (fun t : ℝ => -t) x (-1) := by simpa using derivative_affine (-1) 0 x
        apply (derivative_locality (f := fun t : ℝ => -t) (g := abs) (a := x) (d := -1) ?_).1 h
        refine ⟨-x,neg_pos.mpr hx,fun t ht => ?_⟩
        have ht' := (abs_lt.mp ht).2
        rw [abs_of_neg (show t < 0 by linarith)]
      linarith [derivative_unique hneg hd]
    · subst x
      exact abs_has_no_derivative ⟨0,hd⟩
    · have hpos : HasDerivative abs x 1 := by
        apply (derivative_locality (f := id) (g := abs) (a := x) (d := 1) ?_).1 (derivative_id x)
        refine ⟨x,hx,fun t ht => ?_⟩
        have ht' := (abs_lt.mp ht).1
        rw [abs_of_pos (show 0 < t by linarith)]
        rfl
      exact one_ne_zero (derivative_unique hpos hd)
  · intro hc
    exact hn (rolle_book zero_lt_one hc he (fun x hx => ⟨1,hJ x hx⟩))

theorem cube_inverse_not_derivative {g : ℝ → ℝ}
    (hg : ∀ y, (g y)^3 = y) : ¬ ∃ d, HasDerivative g 0 d := by
  rintro ⟨d,hd⟩
  have hz : g 0 = 0 := (pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)).1 (hg 0)
  have hc : HasDerivative (fun y => (g y)^3) 0 0 := by
    apply (derivative_mathlib _ _ _).2
    simpa [hz] using ((derivative_mathlib _ _ _).1 hd).fun_pow 3
  have he : (fun y => (g y)^3) = id := funext hg
  rw [he] at hc
  exact one_ne_zero (derivative_unique (derivative_id 0) hc)

theorem vanishing_first_and_second :
    HasSecondDerivative (fun x : ℝ => x^4) 0 0 ∧
    HasSecondDerivative (fun x : ℝ => -(x^4)) 0 0 ∧
    HasSecondDerivative (fun x : ℝ => x^3) 0 0 ∧
    Stationary (fun x : ℝ => x^4) 0 ∧ Stationary (fun x : ℝ => -(x^4)) 0 ∧
    Stationary (fun x : ℝ => x^3) 0 := by
  have h4 (x : ℝ) : HasDerivAt (fun y : ℝ => y^4) (4*x^3) x := by
    convert (derivative_mathlib _ _ _).1 (fourth_power_derivative x) using 1
    funext y
    ring
  have h4n (x : ℝ) : HasDerivAt (fun y : ℝ => -(y^4)) (-(4*x^3)) x := (h4 x).neg
  have h3 (x : ℝ) : HasDerivAt (fun y : ℝ => y^3) (3*x^2) x := by
    simpa using (hasDerivAt_id x).fun_pow 3
  have e4 : deriv (fun y : ℝ => y^4) = fun x => 4*x^3 := funext fun x => (h4 x).deriv
  have e4n : deriv (fun y : ℝ => -(y^4)) = fun x => -(4*x^3) := funext fun x => (h4n x).deriv
  have e3 : deriv (fun y : ℝ => y^3) = fun x => 3*x^2 := funext fun x => (h3 x).deriv
  have k4 := ((h3 0).const_mul 4)
  have k3 := (((hasDerivAt_id (0:ℝ)).fun_pow 2).const_mul 3)
  refine ⟨⟨⟨1,zero_lt_one,fun x _ => (h4 x).differentiableAt⟩,?_⟩,
    ⟨⟨1,zero_lt_one,fun x _ => (h4n x).differentiableAt⟩,?_⟩,
    ⟨⟨1,zero_lt_one,fun x _ => (h3 x).differentiableAt⟩,?_⟩,?_,?_,cubic_stationary⟩
  · rw [e4]
    exact (derivative_mathlib _ _ _).2 (by simpa using k4)
  · rw [e4n]
    have hn := k4.neg
    change HasDerivAt (fun x : ℝ => -(4 * x ^ 3)) (-(4 * (3 * (0 : ℝ) ^ 2))) 0 at hn
    norm_num at hn
    exact (derivative_mathlib _ _ _).2 hn
  · rw [e3]
    exact (derivative_mathlib _ _ _).2 (by simpa using k3)
  · exact (derivative_mathlib _ _ _).2 (by simpa using h4 0)
  · exact (derivative_mathlib _ _ _).2 (by simpa using h4n 0)

end Ch07
