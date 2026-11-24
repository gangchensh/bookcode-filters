import Textbook.Ch02.Logic

namespace Ch02

theorem sets_eq_univ_of_empty_mem {α : Type*} (F : BookFilter α)
    (h : (∅ : Set α) ∈ F.sets) : F.sets = Set.univ := by
  ext A
  constructor
  · intro _
    trivial
  · intro _
    exact F.upward h (Set.empty_subset A)

theorem basic_filters_proper :
    IsProper tailFilter ∧ ∀ a : ℝ, IsProper (neighborhoodFilter a) :=
  ⟨tailFilter_proper, neighborhoodFilter_proper⟩

theorem principal_proper_iff {α : Type*} (S : Set α) :
    IsProper (Ch02.principal S) ↔ S.Nonempty := by
  constructor
  · intro h
    by_contra hempty
    apply h
    intro x hx
    exact hempty ⟨x, hx⟩
  · exact principal_proper


open Ch02Eventually Ch02Neighborhoods

theorem eventually_nat_of_forall (P : ℕ → Prop) (h : ∀ n, P n) :
    EventuallyNat P := ⟨0, fun n _ => h n⟩

theorem threshold_hundred : EventuallyNat (fun n : ℕ => 100 ≤ n) :=
  ⟨100, fun _ hn => hn⟩

theorem threshold_examples :
    EventuallyNat (fun n : ℕ => 100 < n) ∧
      EventuallyNat (fun n : ℕ => n ≤ n ^ 2) := by
  constructor
  · exact ⟨101, fun n hn => by omega⟩
  · apply eventually_nat_of_forall
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · have : 1 ≤ n := by omega
      nlinarith

theorem reciprocal_eventual_abs (ε : ℝ) (hε : 0 < ε) :
    EventuallyNat (fun n => |1 / (n : ℝ)| < ε) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le
    (lt_trans (one_div_pos.mpr hε) hN) hcast
  rw [abs_of_pos (div_pos zero_lt_one hnpos)]
  apply (div_lt_iff₀ hnpos).2
  have hb : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hN
  nlinarith

noncomputable def finitePrefixSequence (n : ℕ) : ℝ :=
  if n = 1 then 10^100 else if n = 2 then -2026 else
    if n = 3 then 314159 else 1 / (n : ℝ)

theorem finite_prefix_eventually_equal :
    EventuallyNat (fun n => finitePrefixSequence n = 1 / (n : ℝ)) := by
  refine ⟨4, ?_⟩
  intro n hn
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  simp [finitePrefixSequence, h1, h2, h3]

theorem eventual_equality_preserves_limit {a b : ℕ → ℝ}
    (h : EventuallyNat (fun n => a n = b n)) (l : ℝ) :
    Filter.Tendsto a Filter.atTop (nhds l) ↔
      Filter.Tendsto b Filter.atTop (nhds l) := by
  have heq : a =ᶠ[Filter.atTop] b := (eventuallyNat_iff_mathlib _).1 h
  exact ⟨fun ha => ha.congr' heq, fun hb => hb.congr' heq.symm⟩

theorem infinite_conjunction_counterexample :
    (∀ k : ℕ, EventuallyNat (fun n => k ≤ n)) ∧
      ¬ EventuallyNat (fun n => ∀ k : ℕ, k ≤ n) := by
  constructor
  · intro k
    exact ⟨k, fun _ hn => hn⟩
  · rintro ⟨N, hN⟩
    have hbad := hN N (le_refl N) (N + 1)
    omega

theorem weaker_eventual_bound (u : ℕ → ℕ)
    (h : EventuallyNat (fun n => 1000 < u n)) :
    EventuallyNat (fun n => 100 < u n) :=
  EventuallyNat.mono h (fun _ hn => by omega)

theorem eventually_nonzero_denominator :
    EventuallyNat (fun n => ((n : ℝ) - 3) / ((n : ℝ) + 1) ≠ 0) := by
  refine ⟨4, ?_⟩
  intro n hn
  have h3 : (3 : ℝ) < n := by exact_mod_cast (show 3 < n by omega)
  apply div_ne_zero
  · linarith
  · positivity

theorem basic_neighborhood_mono (a ε₁ ε₂ : ℝ)
    (_hε : 0 < ε₁) (hle : ε₁ ≤ ε₂) :
    epsNeighborhood a ε₁ ⊆ epsNeighborhood a ε₂ := by
  intro x hx
  exact lt_of_lt_of_le hx hle

theorem smaller_neighborhood (a : ℝ) :
    epsNeighborhood a (1 / 100) ⊆ epsNeighborhood a 1 ∧
      ¬ epsNeighborhood a 1 ⊆ epsNeighborhood a (1 / 100) := by
  constructor
  · exact basic_neighborhood_mono a _ _ (by norm_num) (by norm_num)
  · intro h
    have heq : (a + 1 / 2) - a = (1 / 2 : ℝ) := by ring
    have hin : a + 1 / 2 ∈ epsNeighborhood a 1 := by
      change |(a + 1 / 2) - a| < 1
      rw [heq]
      norm_num
    have hout := h hin
    change |(a + 1 / 2) - a| < (1 / 100 : ℝ) at hout
    rw [heq] at hout
    norm_num at hout

theorem local_positive_not_global :
    LocallyHolds 0 (fun x => 0 < 1 - x ^ 2) ∧
      ¬ (∀ x : ℝ, 0 < 1 - x ^ 2) := by
  constructor
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    change |x - 0| < 1 at hx
    have hbounds := abs_lt.mp (show |x| < 1 by simpa using hx)
    have hprod := mul_pos (by linarith : 0 < x + 1)
      (by linarith : 0 < 1 - x)
    change 0 < 1 - x ^ 2
    nlinarith
  · intro h
    have hbad := h 2
    norm_num at hbad

def restrictedNeighborhoodSets (a : ℝ) (S : Set ℝ) : Set (Set ℝ) :=
  {U | ∃ δ > 0, epsNeighborhood a δ ∩ S ⊆ U}

theorem restricted_neighborhood_degenerate :
    restrictedNeighborhoodSets (-1) (Set.Ici 0) = Set.univ := by
  ext U
  simp only [Set.mem_univ, iff_true]
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro x hx
  have hdist : |x - (-1)| < (1 / 2 : ℝ) := hx.1
  have hpos : 0 ≤ x := hx.2
  have hu := (abs_lt.mp hdist).2
  linarith

end Ch02
