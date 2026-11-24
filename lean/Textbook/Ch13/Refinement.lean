import Textbook.Ch13.Bridges

namespace Ch13

open MeasureTheory Set
open scoped BigOperators Interval

theorem insertion_error {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) {l t r K : ℝ} (hlt : l ≤ t) (htr : t ≤ r)
    (hL : ∀ x y, l ≤ x → x ≤ y → y ≤ r → ‖γ y - γ x‖ ≤ K * (y-x)) :
    0 ≤ ‖γ t - γ l‖ + ‖γ r - γ t‖ - ‖γ r - γ l‖ ∧
      ‖γ t - γ l‖ + ‖γ r - γ t‖ - ‖γ r - γ l‖ ≤ K * (r-l) := by
  have htri : ‖γ r - γ l‖ ≤ ‖γ r - γ t‖ + ‖γ t - γ l‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (γ r - γ t) (γ t - γ l)
  have hleft := hL l t le_rfl hlt htr
  have hright := hL t r hlt htr le_rfl
  constructor
  · linarith
  · nlinarith [norm_nonneg (γ r - γ l)]

/-- Each changed coarse cell is counted once, even when it contains several inserted points. -/
theorem insertion_total_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (old refined width : ι → ℝ) (K mesh : ℝ) (hK : 0 ≤ K)
    (hwidth : ∀ i ∈ s, width i ≤ mesh)
    (hcell : ∀ i ∈ s, 0 ≤ refined i - old i ∧ refined i - old i ≤ K * width i) :
    0 ≤ (∑ i ∈ s, refined i) - ∑ i ∈ s, old i ∧
      (∑ i ∈ s, refined i) - ∑ i ∈ s, old i ≤ (s.card : ℝ) * K * mesh := by
  rw [← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun i hi => (hcell i hi).1)
  · calc
      _ ≤ ∑ _i ∈ s, K * mesh :=
        Finset.sum_le_sum (fun i hi => (hcell i hi).2.trans (mul_le_mul_of_nonneg_left (hwidth i hi) hK))
      _ = _ := by simp [mul_assoc]

theorem chord_bound_on_piece {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (γ v : ℝ → V) {l r K : ℝ} (hlr : l ≤ r)
    (hc : ContinuousOn γ (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hd : ∀ t ∈ Ioo l r, HasDerivAt γ (v t) t)
    (hK : ∀ t ∈ Icc l r, ‖v t‖ ≤ K) :
    ‖γ r - γ l‖ ≤ K * (r-l) := by
  have hi : IntervalIntegrable v volume l r := hv.intervalIntegrable_of_Icc hlr
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr hc hd hi]
  have hbound : ∀ t ∈ Ι l r, ‖v t‖ ≤ K := by
    rw [uIoc_of_le hlr]
    exact fun t ht => hK t (Ioc_subset_Icc_self ht)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hlr)] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- A sorted list of inserted points, with both endpoints kept. -/
inductive ChordSubdivision : ℝ → ℝ → Type where
  | one {l r : ℝ} (h : l ≤ r) : ChordSubdivision l r
  | step {l t r : ℝ} (h : l ≤ t) (rest : ChordSubdivision t r) : ChordSubdivision l r

noncomputable def chordLength {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) : {l r : ℝ} → ChordSubdivision l r → ℝ
  | l, r, .one _ => ‖γ r - γ l‖
  | l, _, .step (t := t) _ rest => ‖γ t - γ l‖ + chordLength γ rest

theorem ChordSubdivision.ordered {l r : ℝ} (P : ChordSubdivision l r) : l ≤ r := by
  induction P with
  | one h => exact h
  | step h _ ih => exact h.trans ih

theorem chord_refinement_bounds {V : Type*} [NormedAddCommGroup V] (γ : ℝ → V)
    {l r K : ℝ} (P : ChordSubdivision l r)
    (hL : ∀ x y, l ≤ x → x ≤ y → y ≤ r → ‖γ y - γ x‖ ≤ K * (y-x)) :
    ‖γ r - γ l‖ ≤ chordLength γ P ∧ chordLength γ P ≤ K * (r-l) := by
  induction P with
  | one h => exact ⟨le_rfl, hL _ _ le_rfl h le_rfl⟩
  | @step l t r h P ih =>
    have htr : t ≤ r := P.ordered
    have hb := ih (fun x y hx hxy hy => hL x y (h.trans hx) hxy hy)
    have hl := hL l t le_rfl h htr
    have ht : ‖γ r - γ l‖ ≤ ‖γ t - γ l‖ + ‖γ r - γ t‖ := by
      simpa [sub_add_sub_cancel, add_comm] using norm_add_le (γ r - γ t) (γ t - γ l)
    constructor
    · exact ht.trans (add_le_add le_rfl hb.1)
    · change ‖γ t - γ l‖ + chordLength γ P ≤ K * (r-l)
      nlinarith [hb.2]

theorem polygonal_refinement_error {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) {a b K : ℝ} (P : Ch09.TaggedPartition a b)
    (Q : (i : Fin (P.n+1)) → ChordSubdivision (P.points i.castSucc) (P.points i.succ))
    (changed : Finset (Fin (P.n+1))) (m : ℕ) (hcount : changed.card ≤ m)
    (hK : 0 ≤ K) (hmesh : 0 ≤ P.mesh)
    (hL : ∀ x y, a ≤ x → x ≤ y → y ≤ b → ‖γ y - γ x‖ ≤ K*(y-x))
    (hunchanged : ∀ i ∉ changed, chordLength γ (Q i) =
      ‖γ (P.points i.succ) - γ (P.points i.castSucc)‖) :
    0 ≤ (∑ i, chordLength γ (Q i)) - polygonalSum γ P ∧
      (∑ i, chordLength γ (Q i)) - polygonalSum γ P ≤ (m : ℝ)*K*P.mesh := by
  let old (i : Fin (P.n+1)) := ‖γ (P.points i.succ) - γ (P.points i.castSucc)‖
  let new (i : Fin (P.n+1)) := chordLength γ (Q i)
  have hb := insertion_total_bound changed old new P.width K P.mesh hK
    (fun i _ => Finset.le_sup' (f := P.width) (Finset.mem_univ i)) (by
      intro i _
      have hsub := P.subinterval_subset i
      have hord := (Q i).ordered
      have hleft := (hsub (left_mem_Icc.mpr hord)).1
      have hright := (hsub (right_mem_Icc.mpr hord)).2
      have h := chord_refinement_bounds γ (Q i)
        (fun x y hx hxy hy => hL x y (hleft.trans hx) hxy (hy.trans hright))
      exact ⟨sub_nonneg.mpr h.1, (sub_le_self _ (norm_nonneg _)).trans h.2⟩)
  have hsum : (∑ i, (new i-old i)) = ∑ i ∈ changed, (new i-old i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ changed)
    intro i _ hi
    exact sub_eq_zero.mpr (hunchanged i hi)
  change 0 ≤ (∑ i, new i) - ∑ i, old i ∧
    (∑ i, new i) - ∑ i, old i ≤ (m : ℝ)*K*P.mesh
  rw [← Finset.sum_sub_distrib, hsum, Finset.sum_sub_distrib]
  exact ⟨hb.1, hb.2.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hK) hmesh)⟩

end Ch13
