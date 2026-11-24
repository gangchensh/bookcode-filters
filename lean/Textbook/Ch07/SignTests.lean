import Textbook.Ch07.Statements
import Textbook.Ch06.Estimates

namespace Ch07
open Ch06 Ch02 Ch03 Ch03Approach Set Filter
open scoped Topology

theorem right_limit_mathlib (f : ℝ → ℝ) (a b : ℝ) :
    Approaches f (rightNear a) (neighborhoodFilter b) ↔ Tendsto f (𝓝[>] a) (𝓝 b) := by
  rw [Ch04.real_mathlib_iff, rightNear, toMathlib_nearWithin]
  rfl

theorem lhopital_right {f g df dg : ℝ → ℝ} {a ρ L : ℝ} (hρ : 0 < ρ)
    (hf : ∀ x ∈ Ioo a (a+ρ), HasDerivative f x (df x))
    (hg : ∀ x ∈ Ioo a (a+ρ), HasDerivative g x (dg x))
    (hdg : ∀ x ∈ Ioo a (a+ρ), dg x ≠ 0)
    (hf₀ : Approaches f (rightNear a) (neighborhoodFilter 0))
    (hg₀ : Approaches g (rightNear a) (neighborhoodFilter 0))
    (hquot : Approaches (fun x => df x/dg x) (rightNear a) (neighborhoodFilter L)) :
    Approaches (fun x => f x/g x) (rightNear a) (neighborhoodFilter L) := by
  apply (right_limit_mathlib _ _ _).2
  exact HasDerivAt.lhopital_zero_right_on_Ioo (by linarith)
    (fun x hx => (derivative_mathlib _ _ _).1 (hf x hx))
    (fun x hx => (derivative_mathlib _ _ _).1 (hg x hx)) hdg
    ((right_limit_mathlib _ _ _).1 hf₀) ((right_limit_mathlib _ _ _).1 hg₀)
    ((right_limit_mathlib _ _ _).1 hquot)

theorem interval_increment {f df : ℝ → ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (hc : ContinuousOn f S)
    (hd : ∀ t ∈ interior S, HasDerivative f t (df t))
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    ∃ c ∈ interior S, f y-f x = df c*(y-x) := by
  have hsub : Icc x y ⊆ S := hS.ordConnected.out hx hy
  have hi : Ioo x y ⊆ interior S :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hsub⟩
  obtain ⟨c,hc',he⟩ := mean_value_book f df hxy (hc.mono hsub) (fun t ht => hd t (hi ht))
  exact ⟨c,hi hc',he⟩

theorem derivative_sign_monotonicity {f df : ℝ → ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (hc : ContinuousOn f S)
    (hd : ∀ t ∈ interior S, HasDerivative f t (df t)) :
    ((∀ t ∈ interior S, 0 ≤ df t) → MonotoneOn f S) ∧
    ((∀ t ∈ interior S, 0 < df t) → StrictMonoOn f S) ∧
    ((∀ t ∈ interior S, df t ≤ 0) → AntitoneOn f S) ∧
    ((∀ t ∈ interior S, df t < 0) → StrictAntiOn f S) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hp x hx y hy hxy
    rcases eq_or_lt_of_le hxy with he | hl
    · simp [he]
    obtain ⟨c,hc',he⟩ := interval_increment hS hc hd hx hy hl
    linarith [mul_nonneg (hp c hc') (sub_nonneg.mpr hxy)]
  · intro hp x hx y hy hxy
    obtain ⟨c,hc',he⟩ := interval_increment hS hc hd hx hy hxy
    linarith [mul_pos (hp c hc') (sub_pos.mpr hxy)]
  · intro hp x hx y hy hxy
    rcases eq_or_lt_of_le hxy with he | hl
    · simp [he]
    obtain ⟨c,hc',he⟩ := interval_increment hS hc hd hx hy hl
    linarith [mul_nonpos_of_nonpos_of_nonneg (hp c hc') (sub_nonneg.mpr hxy)]
  · intro hp x hx y hy hxy
    obtain ⟨c,hc',he⟩ := interval_increment hS hc hd hx hy hxy
    linarith [mul_neg_of_neg_of_pos (hp c hc') (sub_pos.mpr hxy)]

theorem derivative_nonneg_of_monotone_on {f : ℝ → ℝ} {S : Set ℝ} {a d : ℝ}
    (ha : a ∈ interior S) (hm : MonotoneOn f S) (hd : HasDerivative f a d) :
    0 ≤ d := by
  have hN : S ∈ 𝓝 a := mem_interior_iff_mem_nhds.mp ha
  have h := hm.derivWithin_nonneg (x := a)
  rw [derivWithin_of_mem_nhds hN, derivative_value hd] at h
  exact h

def StrictLocalMinimum (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ δ > 0, ∀ x, 0 < |x-a| → |x-a| < δ → f a < f x

theorem first_derivative_test {f df : ℝ → ℝ} {a ρ : ℝ}
    (hρ : 0 < ρ) (hc : ContinuousAt f a)
    (hd : ∀ x, 0 < |x-a| → |x-a| < ρ → HasDerivative f x (df x)) :
    ((∀ x ∈ Ioo (a-ρ) a, df x ≤ 0) → (∀ x ∈ Ioo a (a+ρ), 0 ≤ df x) → IsLocalMin f a) ∧
    ((∀ x ∈ Ioo (a-ρ) a, df x < 0) → (∀ x ∈ Ioo a (a+ρ), 0 < df x) → StrictLocalMinimum f a) ∧
    ((∀ x ∈ Ioo (a-ρ) a, 0 ≤ df x) → (∀ x ∈ Ioo a (a+ρ), df x ≤ 0) → IsLocalMax f a) ∧
    ((∀ x ∈ Ioo (a-ρ) a, 0 < df x) → (∀ x ∈ Ioo a (a+ρ), df x < 0) →
      StrictLocalMinimum (fun x => -f x) a) := by
  have H (x : ℝ) (hx : |x-a| < ρ) (hne : x ≠ a) :
      ∃ c, (x < a → c ∈ Ioo x a) ∧ (a < x → c ∈ Ioo a x) ∧
        f x-f a = df c*(x-a) := by
    have hc' (t : ℝ) (ht : |t-a| < ρ) : ContinuousAt f t := by
      by_cases he : t = a
      · simpa [he] using hc
      · exact ((derivative_mathlib _ _ _).1 (hd t (abs_pos.mpr (sub_ne_zero.mpr he)) ht)).continuousAt
    rcases lt_or_gt_of_ne hne with h | h
    · have hdist (t : ℝ) (ht : t ∈ Icc x a) : |t-a| < ρ := by
        rw [abs_lt]
        have hb := (abs_lt.mp hx).1
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨c,hc₁,he⟩ := mean_value_book f df h
        (fun t ht => (hc' t (hdist t ht)).continuousWithinAt)
        (fun t ht => hd t (abs_pos.mpr (sub_ne_zero.mpr ht.2.ne)) (hdist t ⟨ht.1.le,ht.2.le⟩))
      exact ⟨c,fun _ => hc₁,fun hn => (h.not_gt hn).elim,by linarith⟩
    · have hdist (t : ℝ) (ht : t ∈ Icc a x) : |t-a| < ρ := by
        rw [abs_lt]
        have hb := (abs_lt.mp hx).2
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨c,hc₁,he⟩ := mean_value_book f df h
        (fun t ht => (hc' t (hdist t ht)).continuousWithinAt)
        (fun t ht => hd t (abs_pos.mpr (sub_ne_zero.mpr ht.1.ne')) (hdist t ⟨ht.1.le,ht.2.le⟩))
      exact ⟨c,fun hn => (h.not_gt hn).elim,fun _ => hc₁,he⟩
  have Hc {x c : ℝ} (hx : |x-a| < ρ) :
      (c ∈ Ioo x a → c ∈ Ioo (a-ρ) a) ∧ (c ∈ Ioo a x → c ∈ Ioo a (a+ρ)) := by
    obtain ⟨hl,hr⟩ := abs_lt.mp hx
    exact ⟨fun h => ⟨by linarith [h.1],h.2⟩, fun h => ⟨h.1,by linarith [h.2]⟩⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro hl hr
    apply Metric.eventually_nhds_iff.2
    refine ⟨ρ,hρ,fun x hx => ?_⟩
    rw [Real.dist_eq] at hx
    by_cases he : x = a
    · simp [he]
    obtain ⟨c,hL,hR,heq⟩ := H x hx he
    rcases lt_or_gt_of_ne he with h | h
    · linarith [mul_nonneg_of_nonpos_of_nonpos (hl c ((Hc hx).1 (hL h))) (sub_nonpos.mpr h.le)]
    · linarith [mul_nonneg (hr c ((Hc hx).2 (hR h))) (sub_nonneg.mpr h.le)]
  · intro hl hr
    refine ⟨ρ,hρ,fun x hne hx => ?_⟩
    have he := sub_ne_zero.mp (abs_pos.mp hne)
    obtain ⟨c,hL,hR,heq⟩ := H x hx he
    rcases lt_or_gt_of_ne he with h | h
    · linarith [mul_pos_of_neg_of_neg (hl c ((Hc hx).1 (hL h))) (sub_neg.mpr h)]
    · linarith [mul_pos (hr c ((Hc hx).2 (hR h))) (sub_pos.mpr h)]
  · intro hl hr
    apply Metric.eventually_nhds_iff.2
    refine ⟨ρ,hρ,fun x hx => ?_⟩
    rw [Real.dist_eq] at hx
    by_cases he : x = a
    · simp [he]
    obtain ⟨c,hL,hR,heq⟩ := H x hx he
    rcases lt_or_gt_of_ne he with h | h
    · linarith [mul_nonpos_of_nonneg_of_nonpos (hl c ((Hc hx).1 (hL h))) (sub_nonpos.mpr h.le)]
    · linarith [mul_nonpos_of_nonpos_of_nonneg (hr c ((Hc hx).2 (hR h))) (sub_nonneg.mpr h.le)]
  · intro hl hr
    refine ⟨ρ,hρ,fun x hne hx => ?_⟩
    have he := sub_ne_zero.mp (abs_pos.mp hne)
    obtain ⟨c,hL,hR,heq⟩ := H x hx he
    rcases lt_or_gt_of_ne he with h | h
    · linarith [mul_neg_of_pos_of_neg (hl c ((Hc hx).1 (hL h))) (sub_neg.mpr h)]
    · linarith [mul_neg_of_neg_of_pos (hr c ((Hc hx).2 (hR h))) (sub_pos.mpr h)]

def HasSecondDerivative (f : ℝ → ℝ) (a d : ℝ) : Prop :=
  (∃ ρ > 0, ∀ x, |x-a| < ρ → DifferentiableAt ℝ f x) ∧ HasDerivative (deriv f) a d

theorem second_derivative_test {f : ℝ → ℝ} {a d : ℝ}
    (hd : HasSecondDerivative f a d) (ha : deriv f a = 0) :
    (0 < d → StrictLocalMinimum f a) ∧ (d < 0 → StrictLocalMinimum (fun x => -f x) a) := by
  obtain ⟨⟨ρ,hρ,hf⟩,hd⟩ := hd
  have hc := (hf a (by simpa using hρ)).continuousAt
  have test {q : ℝ → ℝ} {e : ℝ} (hq : HasDerivative q a e) (he : 0 < e) :
      ∃ δ > 0, (∀ x ∈ Ioo (a-δ) a, q x < q a) ∧
        (∀ x ∈ Ioo a (a+δ), q a < q x) := by
    obtain ⟨δ,hδ,hR,hL⟩ := positive_derivative_local hq he
    refine ⟨δ,hδ,fun x hx => ?_,fun x hx => ?_⟩
    · simpa only [show a+(x-a)=x by ring] using hL (x-a) (by linarith [hx.1]) (sub_neg.mpr hx.2)
    · simpa only [show a+(x-a)=x by ring] using hR (x-a) (sub_pos.mpr hx.1) (by linarith [hx.2])
  constructor
  · intro hp
    obtain ⟨δ,hδ,hL,hR⟩ := test hd hp
    have hh := first_derivative_test (df := deriv f) (lt_min hρ hδ) hc
      (fun x _ hx => (derivative_mathlib _ _ _).2
        ((hf x (hx.trans_le (min_le_left _ _))).hasDerivAt))
    apply hh.2.1
    · intro x hx
      rw [← ha]
      exact hL x ⟨by linarith [hx.1,min_le_right ρ δ],hx.2⟩
    · intro x hx
      rw [← ha]
      exact hR x ⟨hx.1,by linarith [hx.2,min_le_right ρ δ]⟩
  · intro hn
    have hneg : HasDerivative (fun x => -deriv f x) a (-d) := (derivative_mathlib _ _ _).2
      ((derivative_mathlib _ _ _).1 hd).neg
    obtain ⟨δ,hδ,hL,hR⟩ := test hneg (neg_pos.mpr hn)
    have hh := first_derivative_test (df := deriv f) (lt_min hρ hδ) hc
      (fun x _ hx => (derivative_mathlib _ _ _).2
        ((hf x (hx.trans_le (min_le_left _ _))).hasDerivAt))
    apply hh.2.2.2
    · intro x hx
      have h := hL x ⟨by linarith [hx.1,min_le_right ρ δ],hx.2⟩
      linarith
    · intro x hx
      have h := hR x ⟨hx.1,by linarith [hx.2,min_le_right ρ δ]⟩
      linarith

end Ch07
