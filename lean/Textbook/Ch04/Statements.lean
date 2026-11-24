import Textbook.Ch04.Continuity
import Textbook.Ch03.Statements

namespace Ch04Statements
open Ch02 Ch03 Ch03Approach Ch03Rules Ch04 Ch04Continuity

abbrev FiniteLimit {X : Type*} (f : X → ℝ) (F : BookFilter X) (a : ℝ) : Prop :=
  Approaches f F (neighborhoodFilter a)

theorem merge_thresholds_and_radii (P Q : ℕ → Prop) (p q : ℝ → Prop)
    (N M : ℕ) (a δ η : ℝ)
    (hP : ∀ n ≥ N, P n) (hQ : ∀ n ≥ M, Q n)
    (hp : ∀ x, 0 < |x-a| → |x-a| < δ → p x)
    (hq : ∀ x, 0 < |x-a| → |x-a| < η → q x) :
    (∀ n ≥ max N M, P n ∧ Q n) ∧
      (∀ x, 0 < |x-a| → |x-a| < min δ η → p x ∧ q x) := by
  constructor
  · intro n hn
    exact ⟨hP n ((le_max_left _ _).trans hn), hQ n ((le_max_right _ _).trans hn)⟩
  · intro x hx hsmall
    exact ⟨hp x hx (hsmall.trans_le (min_le_left _ _)), hq x hx (hsmall.trans_le (min_le_right _ _))⟩

variable {X : Type*} {F : BookFilter X} {f g r : X → ℝ} {a b : ℝ}

theorem bounded_and_positive (hf : FiniteLimit f F b) :
    Eventually F (fun x => |f x| < |b| + 1) ∧
      (0 < b → Eventually F (fun x => b / 2 < f x ∧ 0 < b / 2)) := by
  refine ⟨Ch04Local.limit_eventually_bounded hf, fun hb => ?_⟩
  apply eventually_mono ((real_iff _ _ _).1 hf _ (half_pos hb))
  intro x hx
  exact ⟨by linarith [(abs_lt.mp hx).1], half_pos hb⟩

theorem limit_finset_sum {I : Type*} (s : Finset I) (u : I → X → ℝ) (l : I → ℝ)
    (hu : ∀ i ∈ s, FiniteLimit (u i) F (l i)) :
    FiniteLimit (fun x => ∑ i ∈ s, u i x) F (∑ i ∈ s, l i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const_limit F 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact limit_add (hu i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem affine_of_limit (hf : FiniteLimit f F a) :
    FiniteLimit (fun x => 3 * f x - 2) F (3 * a - 2) :=
  limit_sub (limit_const_mul 3 hf) (const_limit F 2)

theorem abs_distance (u v : ℝ) : |(|u| - |v|)| ≤ |u - v| :=
  abs_abs_sub_abs_le_abs_sub u v

theorem limit_separated (hf : FiniteLimit f F a) (hg : FiniteLimit g F b) (hab : a < b) :
    Eventually F (fun x => f x < g x) := by
  have hd : 0 < (b-a)/3 := by linarith
  apply eventually_mono (eventually_and ((real_iff _ _ _).1 hf _ hd) ((real_iff _ _ _).1 hg _ hd))
  intro x hx
  change f x < g x
  linarith [(abs_lt.mp hx.1).2, (abs_lt.mp hx.2).1]

theorem limit_closed_bound (hF : IsProper F) (hf : FiniteLimit f F a) (A B : ℝ)
    (h : Eventually F (fun x => A ≤ f x ∧ f x ≤ B)) : A ≤ a ∧ a ≤ B :=
  ⟨limit_le hF (const_limit F A) hf (eventually_mono h fun _ hx => hx.1),
   limit_le hF hf (const_limit F B) (eventually_mono h fun _ hx => hx.2)⟩

theorem bounded_mul_zero_exists (h : ∃ C : ℝ, 0 ≤ C ∧ Eventually F (fun x => |f x| ≤ C))
    (hg : FiniteLimit g F 0) : FiniteLimit (fun x => f x * g x) F 0 := by
  obtain ⟨C, hC, hf⟩ := h
  exact bounded_mul_zero C hC hf hg

theorem limit_perturbation (hr : FiniteLimit r F 0) (hf : FiniteLimit f F a)
    (h : Eventually F (fun x => |g x - f x| ≤ |r x|)) : FiniteLimit g F a := by
  apply (real_iff _ _ _).2
  intro ε hε
  apply eventually_mono (eventually_and h (eventually_and
    ((real_iff _ _ _).1 hr _ (half_pos hε)) ((real_iff _ _ _).1 hf _ (half_pos hε))))
  intro x hx
  have htri : |g x-a| ≤ |g x-f x| + |f x-a| := by
    convert abs_add_le (g x-f x) (f x-a) using 2; ring
  have hrx : |r x| < ε/2 := by simpa only [sub_zero] using hx.2.1
  have hfx := hx.2.2
  linarith [hx.1]

theorem upper_const_mul (hf : Approaches f F (upperFilter ℝ)) (c : ℝ) (hc : 0 < c) :
    Approaches (fun x => c * f x) F (upperFilter ℝ) := by
  apply (Ch04Infinity.upper_iff _ _).2
  intro M
  apply eventually_mono ((Ch04Infinity.upper_iff _ _).1 hf (M/c))
  intro x hx
  simpa only [mul_comm (f x) c] using (div_le_iff₀ hc).1 hx

theorem continuous_epsilon (f : ℝ → ℝ) (a : ℝ) : BookContinuousAt f a ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x-a| < δ → |f x-f a| < ε :=
  Ch03Definitions.finite_neighborhood_iff f a (f a)

theorem continuous_punctured_iff (f : ℝ → ℝ) (a : ℝ) :
    BookContinuousAt f a ↔ Approaches f (punctured a) (neighborhoodFilter (f a)) := by
  constructor
  · exact approaches_within_source _
  · intro h
    apply (continuous_epsilon f a).2
    intro ε hε
    obtain ⟨δ,hδ,h⟩ := (punctured_real_iff _ _ _).1 h ε hε
    refine ⟨δ,hδ,fun x hx => ?_⟩
    by_cases hn : x = a
    · simpa [hn] using hε
    · exact h x hx hn

theorem continuous_sub {f g : ℝ → ℝ} {a : ℝ}
    (hf : BookContinuousAt f a) (hg : BookContinuousAt g a) :
    BookContinuousAt (fun x => f x - g x) a := limit_sub hf hg

theorem continuous_comp {f g : ℝ → ℝ} {a : ℝ}
    (hf : BookContinuousAt f a) (hg : BookContinuousAt g (f a)) :
    BookContinuousAt (fun x => g (f x)) a := approaches_comp hf hg

theorem continuous_arithmetic {f g : ℝ → ℝ} {a : ℝ}
    (hf : BookContinuousAt f a) (hg : BookContinuousAt g a) :
    BookContinuousAt (fun x => f x + g x) a ∧
    BookContinuousAt (fun x => f x - g x) a ∧
    BookContinuousAt (fun x => f x * g x) a ∧
    (g a ≠ 0 → BookContinuousAt (fun x => f x / g x) a) :=
  ⟨continuous_add_book hf hg, continuous_sub hf hg, continuous_mul_book hf hg,
    continuous_div_book hf hg⟩

theorem limit_into_continuous {g : ℝ → ℝ} (hf : FiniteLimit f F a)
    (hg : BookContinuousAt g a) : FiniteLimit (fun x => g (f x)) F (g a) :=
  approaches_comp hf hg

def BookContinuousWithinAt (f : ℝ → ℝ) (S : Set ℝ) (a : ℝ) : Prop :=
  FiniteLimit f (nearWithin a S) (f a)

def BookContinuousOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ a ∈ S, BookContinuousWithinAt f S a

theorem sqrt_continuous_on : BookContinuousOn Real.sqrt (Set.Ici 0) := by
  intro a ha
  apply approaches_within_source
  exact (continuous_mathlib _ _).2 (Real.continuous_sqrt.continuousAt)

noncomputable def fillCenter (f : ℝ → ℝ) (a b x : ℝ) : ℝ := if x = a then b else f x

theorem extend_continuously (f : ℝ → ℝ) (S : Set ℝ) (a b : ℝ)
    (hf : Ch04Local.DomainLimit f S a b) :
    BookContinuousWithinAt (fillCenter f a b) (insert a S) a := by
  change FiniteLimit (fillCenter f a b) (nearWithin a (insert a S)) (fillCenter f a b a)
  rw [show fillCenter f a b a = b by simp [fillCenter]]
  apply (Ch03Definitions.finite_within_iff _ _ _ _).2
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := (Ch04Local.domain_limit_iff _ _ _ _).1 hf ε hε
  refine ⟨δ,hδ,fun x hx hS => ?_⟩
  by_cases hn : x = a
  · simpa [fillCenter, hn] using hε
  · have hxS : x ∈ S := (Set.mem_insert_iff.mp hS).resolve_left hn
    simpa [fillCenter, hn] using h x hx ⟨hxS, hn⟩

theorem continuous_gluing (f : ℝ → ℝ) (a : ℝ) : BookContinuousAt f a ↔
    FiniteLimit f (leftNear a) (f a) ∧ FiniteLimit f (rightNear a) (f a) := by
  rw [continuous_punctured_iff, Ch04Infinity.sides_iff]

theorem extension_and_unique_limit (f : ℝ → ℝ) (S : Set ℝ) (a b : ℝ)
    (ha : Ch04Local.IsAccumulationPoint S a) (hf : Ch04Local.DomainLimit f S a b) :
    BookContinuousWithinAt (fillCenter f a b) (insert a S) a ∧
    (∀ c, Ch04Local.DomainLimit f S a c → b = c) :=
  ⟨extend_continuously f S a b hf, fun _ hc => Ch04Local.domain_limit_unique ha hf hc⟩

theorem infinity_reciprocal_rules (f : X → ℝ) (F : BookFilter X) :
    (Approaches f F (upperFilter ℝ) → FiniteLimit (fun x => 1 / f x) F 0) ∧
    (∀ c : ℝ, 0 < c → Approaches f F (upperFilter ℝ) →
      Approaches (fun x => c * f x) F (upperFilter ℝ)) ∧
    (FiniteLimit f F 0 → Eventually F (fun x => 0 < f x) →
      Approaches (fun x => 1 / f x) F (upperFilter ℝ)) ∧
    (Approaches f F (lowerFilter ℝ) ↔ Approaches (fun x => -f x) F (upperFilter ℝ)) :=
  ⟨Ch04Infinity.reciprocal_upper_zero, fun c hc hf => upper_const_mul hf c hc,
    Ch04Infinity.reciprocal_zero_upper, (Ch04Infinity.neg_upper_iff f F).symm⟩

end Ch04Statements
