import Textbook.Ch03.BasicExamples
import Textbook.Ch03.DefinitionExamples
import Textbook.Ch03.LimitRules

namespace Ch03Statements
open Ch02 Ch03 Ch03Approach Ch03Definitions

/-- The preimage takes an output requirement back to the input type. -/
abbrev preimage {X Y : Type*} (f : X → Y) (V : Set Y) : Set X :=
  {x | f x ∈ V}

theorem preimage_laws {X Y : Type*} (f : X → Y) (A B : Set Y) :
    preimage f Set.univ = Set.univ ∧
      preimage f (A ∩ B) = preimage f A ∩ preimage f B ∧
      (A ⊆ B → preimage f A ⊆ preimage f B) :=
  ⟨rfl, rfl, fun h _ hx => h hx⟩

theorem square_preimages :
    preimage (fun x : ℝ => x ^ 2) (Set.Ioo (-1) 4) = Set.Ioo (-2) 2 ∧
      preimage (fun x : ℝ => x ^ 2) (Set.Ioo (-1) 0) = ∅ := by
  constructor
  · ext x
    change (-1 < x ^ 2 ∧ x ^ 2 < 4) ↔ (-2 < x ∧ x < 2)
    constructor
    · intro h
      constructor
      · by_contra! hx
        nlinarith [sq_nonneg (x + 2)]
      · by_contra! hx
        nlinarith [sq_nonneg (x - 2)]
    · rintro ⟨hl, hr⟩
      have hprod := mul_pos (show 0 < x + 2 by linarith) (show 0 < 2 - x by linarith)
      exact ⟨by nlinarith [sq_nonneg x], by nlinarith⟩
  · ext x
    change (-1 < x ^ 2 ∧ x ^ 2 < 0) ↔ False
    exact ⟨fun h => (not_lt_of_ge (sq_nonneg x)) h.2, False.elim⟩

theorem eventually_upper_iff {X : Type*} [LinearOrder X] [Nonempty X]
    (P : X → Prop) :
    Eventually (upperFilter X) P ↔ ∃ b : X, ∀ x ≥ b, P x := Iff.rfl

theorem square_eventually_gt_hundred :
    Eventually (upperFilter ℝ) (fun x => 100 < x ^ 2) := by
  apply (eventually_upper_iff _).2
  refine ⟨11, ?_⟩
  intro x hx
  nlinarith [sq_nonneg (x - 11)]

theorem principal_within_sets {X : Type*} (A S : Set X) :
    (within (principal A) S).sets = (principal (A ∩ S)).sets := by
  ext U
  change (∀ ⦃x⦄, x ∈ A → x ∈ S → x ∈ U) ↔ (A ∩ S ⊆ U)
  exact ⟨fun h _ hx => h hx.1 hx.2, fun h _ hx hs => h ⟨hx, hs⟩⟩

/-- Fin 3 labels the three paper points 1, 2, 3 by 0, 1, 2. -/
theorem three_point_restriction (U : Set (Fin 3)) :
    U ∈ (within (principal ({0, 1} : Set (Fin 3))) {1, 2}).sets ↔ 1 ∈ U := by
  rw [principal_within_sets]
  have h : ({0, 1} : Set (Fin 3)) ∩ {1, 2} = {1} := by
    ext x
    fin_cases x <;> decide
  rw [h]
  exact Set.singleton_subset_iff

theorem right_interval_iff (a : ℝ) (U : Set ℝ) :
    U ∈ (rightNear a).sets ↔ ∃ r > 0, Set.Ioo a (a + r) ⊆ U := by
  change (∃ r > 0, ∀ x, |x - a| < r → a < x → x ∈ U) ↔ _
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x hx => h x (by rw [abs_of_pos (sub_pos.mpr hx.1)]; linarith [hx.2]) hx.1⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun x hx hax => h ⟨hax, by linarith [(abs_lt.mp hx).2]⟩⟩

theorem right_interval_new_member (a r : ℝ) (hr : 0 < r) :
    Set.Ioo a (a + r) ∈ (rightNear a).sets ∧
      Set.Ioo a (a + r) ∉ (neighborhoodFilter a).sets := by
  refine ⟨(right_interval_iff a _).2 ⟨r, hr, fun _ h => h⟩, ?_⟩
  rintro ⟨δ, hδ, h⟩
  have ha : a ∈ Set.Ioo a (a + r) := h (by
    change |a - a| < δ
    simpa using hδ)
  exact (lt_irrefl a) ha.1

theorem right_restriction_strict (a : ℝ) :
    (neighborhoodFilter a).sets ⊆ (rightNear a).sets ∧
      ¬ (rightNear a).sets ⊆ (neighborhoodFilter a).sets := by
  refine ⟨fun _ h => eventually_to_within h, ?_⟩
  intro h
  obtain ⟨hmem, hnot⟩ := right_interval_new_member a 1 zero_lt_one
  exact hnot (h hmem)

theorem within_proper_iff {X : Type*} (F : BookFilter X) (S : Set X) :
    IsProper (within F S) ↔ ∀ A ∈ F.sets, (A ∩ S).Nonempty := by
  classical
  constructor
  · intro h A hA
    by_contra hn
    apply h
    exact F.upward hA (fun x hx hs => False.elim (hn ⟨x, hx, hs⟩))
  · intro h hempty
    obtain ⟨x, hx, hs⟩ := h {x | x ∈ S → x ∈ (∅ : Set X)} hempty
    exact hx hs

def WithinLimit (f : ℝ → ℝ) (S : Set ℝ) (a b : ℝ) : Prop :=
  Approaches f (nearWithin a S) (neighborhoodFilter b)

def PuncturedLimit (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Approaches f (punctured a) (neighborhoodFilter b)

theorem punctured_limit_iff (f : ℝ → ℝ) (a b : ℝ) :
    PuncturedLimit f a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - b| < ε := by
  have hn (x : ℝ) : 0 < |x - a| ↔ x ≠ a := abs_pos.trans sub_ne_zero
  change Approaches f (punctured a) (neighborhoodFilter b) ↔ _
  rw [punctured_real_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx => h x hx.2 ((hn x).1 hx.1)⟩
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxa => h x ⟨(hn x).2 hxa, hx⟩⟩

def RightLimit (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Approaches f (rightNear a) (neighborhoodFilter b)

def LeftLimit (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  Approaches f (leftNear a) (neighborhoodFilter b)

theorem right_limit_iff (f : ℝ → ℝ) (a b : ℝ) :
    RightLimit f a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Set.Ioo a (a + δ) → |f x - b| < ε := by
  change Approaches f (rightNear a) (neighborhoodFilter b) ↔ _
  rw [real_iff]
  exact forall_congr' fun ε => imp_congr_right fun _ => right_interval_iff a _

theorem left_limit_iff (f : ℝ → ℝ) (a b : ℝ) :
    LeftLimit f a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Set.Ioo (a - δ) a → |f x - b| < ε := by
  change Approaches f (leftNear a) (neighborhoodFilter b) ↔ _
  rw [finite_left_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx => h x (by rw [abs_of_neg (sub_neg.mpr hx.2)]; linarith [hx.1]) hx.2⟩
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxa => h x ⟨by linarith [(abs_lt.mp hx).1], hxa⟩⟩

def FiniteAtTop (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Approaches f (upperFilter ℝ) (neighborhoodFilter b)

def FiniteAtBot (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Approaches f (lowerFilter ℝ) (neighborhoodFilter b)

def TendsToPosInf {X : Type*} (f : X → ℝ) (F : BookFilter X) : Prop :=
  Approaches f F (upperFilter ℝ)

def TendsToNegInf {X : Type*} (f : X → ℝ) (F : BookFilter X) : Prop :=
  Approaches f F (lowerFilter ℝ)

theorem right_pos_inf_iff (f : ℝ → ℝ) (a : ℝ) :
    TendsToPosInf f (rightNear a) ↔
      ∀ M : ℝ, ∃ δ > 0, ∀ x, x ∈ Set.Ioo a (a + δ) → M ≤ f x := by
  change Approaches f (rightNear a) (upperFilter ℝ) ↔ _
  rw [upper_target_iff]
  exact forall_congr' fun M => right_interval_iff a {x | M ≤ f x}

theorem restricted_example_not_full :
    ¬ Approaches Ch03BasicExamples.restrictedExample (neighborhoodFilter 0) (neighborhoodFilter 0) := by
  intro h
  obtain ⟨δ, hδ, h⟩ := (finite_neighborhood_iff _ _ _).1 h (1 / 2) (by norm_num)
  have hx : |(-δ / 2) - 0| < δ := by rw [sub_zero, abs_of_neg (by linarith)]; linarith
  have hn : ¬ 0 ≤ -δ / 2 := by linarith
  have hbad := h (-δ / 2) hx
  norm_num [Ch03BasicExamples.restrictedExample, hn] at hbad

theorem restricted_example_comparison :
    WithinLimit Ch03BasicExamples.restrictedExample (Set.Ici 0) 0 0 ∧
      ¬ Approaches Ch03BasicExamples.restrictedExample (neighborhoodFilter 0) (neighborhoodFilter 0) :=
  ⟨Ch03BasicExamples.restricted_example_limit, restricted_example_not_full⟩

theorem sqrt_limits_at_zero :
    WithinLimit Real.sqrt (Set.Ici 0) 0 0 ∧
      Approaches Real.sqrt (neighborhoodFilter 0) (neighborhoodFilter 0) := by
  have h : Approaches Real.sqrt (neighborhoodFilter 0) (neighborhoodFilter 0) := by
    apply (finite_neighborhood_iff _ _ _).2
    intro ε hε
    refine ⟨ε ^ 2, by positivity, ?_⟩
    intro x hx
    rw [sub_zero, abs_of_nonneg (Real.sqrt_nonneg x)]
    exact (Real.sqrt_lt' hε).2 (by linarith [(abs_lt.mp hx).2])
  exact ⟨Ch03Rules.approaches_within_source _ h, h⟩

noncomputable def changedCenter (x : ℝ) : ℝ := if x = 0 then 1 else x

theorem changed_center_limits :
    PuncturedLimit changedCenter 0 0 ∧
      ¬ Approaches changedCenter (neighborhoodFilter 0) (neighborhoodFilter 0) := by
  constructor
  · apply (punctured_real_iff _ _ _).2
    intro ε hε
    exact ⟨ε, hε, fun x hx hn => by simpa [changedCenter, hn] using hx⟩
  · intro h
    obtain ⟨δ, hδ, h⟩ := (finite_neighborhood_iff _ _ _).1 h (1 / 2) (by norm_num)
    have hbad := h 0 (by simpa using hδ)
    norm_num [changedCenter] at hbad

theorem quotient_center (a : ℝ) : (a ^ 2 - a ^ 2) / (a - a) = 0 := by simp

theorem quotient_full_limit_iff (a : ℝ) :
    Approaches (fun x : ℝ => (x ^ 2 - a ^ 2) / (x - a))
      (neighborhoodFilter a) (neighborhoodFilter (2 * a)) ↔ a = 0 := by
  rw [finite_neighborhood_iff]
  constructor
  · intro h
    by_contra ha
    have he : 0 < |2 * a| := abs_pos.mpr (mul_ne_zero (by norm_num) ha)
    obtain ⟨δ, hδ, h⟩ := h _ he
    have hbad := h a (by simpa using hδ)
    rw [quotient_center, zero_sub, abs_neg] at hbad
    exact (lt_irrefl _) hbad
  · rintro rfl ε hε
    refine ⟨ε, hε, ?_⟩
    intro x hx
    have h : x ^ 2 / x = x := by
      by_cases hn : x = 0
      · simp [hn]
      · exact (div_eq_iff hn).2 (by ring)
    simpa [h] using hx

theorem quotient_limits (a : ℝ) :
    PuncturedLimit (fun x => (x ^ 2 - a ^ 2) / (x - a)) a (2 * a) ∧
      (a ^ 2 - a ^ 2) / (a - a) = 0 ∧
      (Approaches (fun x : ℝ => (x ^ 2 - a ^ 2) / (x - a))
        (neighborhoodFilter a) (neighborhoodFilter (2 * a)) ↔ a = 0) :=
  ⟨Ch03BasicExamples.quotient_punctured_from_definition a, quotient_center a, quotient_full_limit_iff a⟩

theorem shifted_reciprocal_sequence :
    SequenceLimit (fun n => 3 + 2 / ((n : ℝ) + 1)) 3 := by
  apply (sequence_limit_iff _ _).2
  intro ε hε
  obtain ⟨N, hN⟩ := Ch02Eventually.eventually_reciprocal (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have he := hN n hn
  have heq : 3 + 2 / ((n : ℝ) + 1) - 3 = 2 * (1 / ((n : ℝ) + 1)) := by ring
  rw [heq, abs_of_nonneg (by positivity)]
  linarith

theorem square_atTop : TendsToPosInf (fun x : ℝ => x ^ 2) (upperFilter ℝ) := by
  apply (upper_target_iff _ _).2
  intro M
  refine ⟨|M| + 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := by linarith [abs_nonneg M]
  have hprod := mul_nonneg (sub_nonneg.mpr hx1) (show 0 ≤ x by linarith)
  change M ≤ x ^ 2
  calc
    M ≤ |M| := le_abs_self M
    _ ≤ x := by linarith
    _ ≤ x ^ 2 := by nlinarith only [hprod]

theorem reciprocal_square_atTop : FiniteAtTop (fun x => 1 / x ^ 2) 0 := by
  apply (finite_atTop_iff _ _).2
  intro ε hε
  refine ⟨max 1 (2 / ε), ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 / ε ≤ x := (le_max_right _ _).trans hx
  have hpos : 0 < x := by linarith
  rw [sub_zero, abs_of_nonneg (by positivity)]
  calc
    1 / x ^ 2 ≤ 1 / x := one_div_le_one_div_of_le hpos (by nlinarith)
    _ ≤ ε / 2 := (div_le_iff₀ hpos).2 (by
      have h := (div_le_iff₀ hε).1 hx2
      nlinarith)
    _ < ε := by linarith

noncomputable def alternatingSequence (n : ℕ) : ℝ := (-1 : ℝ) ^ n * (n + 1)

theorem alternating_unbounded_not_pos_inf :
    (∀ M : ℝ, ∃ n, M < alternatingSequence n) ∧
      ¬ TendsToPosInf alternatingSequence tailFilter := by
  constructor
  · intro M
    obtain ⟨n, hn⟩ := exists_nat_gt M
    refine ⟨2 * n, ?_⟩
    unfold alternatingSequence
    norm_num [pow_mul]
    linarith
  · intro h
    obtain ⟨N, hN⟩ := (upper_target_iff _ _).1 h 0
    have hbad := hN (2 * N + 1) (by omega)
    unfold alternatingSequence at hbad
    norm_num [pow_add, pow_mul] at hbad
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith

end Ch03Statements
