import Textbook.Ch13.Refinement
import Textbook.Ch13.Grid

namespace Ch13
open Set Filter
open scoped BigOperators Topology

noncomputable def subdivisionFromList {l r : ℝ} (h : l ≤ r) (xs : List ℝ)
    (hs : xs.Pairwise (· ≤ ·)) (hx : ∀ x ∈ xs, x ∈ Icc l r) :
    ChordSubdivision l r :=
  match xs with
  | [] => .one h
  | t :: ts =>
    have ht := hx t (by simp)
    .step ht.1 (subdivisionFromList ht.2 ts hs.tail
      (fun x hx' => ⟨(List.pairwise_cons.mp hs).1 x hx',
        (hx x (by simp [hx'])).2⟩))

noncomputable def subdivideAt {l r : ℝ} (h : l ≤ r) (B : Finset ℝ) :
    ChordSubdivision l r :=
  subdivisionFromList h ((B.filter fun t => t ∈ Ioo l r).sort (· ≤ ·))
    (Finset.pairwise_sort _ _) (by
      intro t ht
      exact Ioo_subset_Icc_self ((Finset.mem_filter.mp ((Finset.mem_sort _).mp ht)).2))

theorem subdivideAt_empty_cell {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) {l r : ℝ} (h : l ≤ r) (B : Finset ℝ)
    (hb : ∀ t ∈ B, t ∉ Ioo l r) :
    chordLength γ (subdivideAt h B) = ‖γ r - γ l‖ := by
  have he : (B.filter fun t => t ∈ Ioo l r) = ∅ := by
    ext t
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    exact fun ht => hb t ht.1 ht.2
  simp only [subdivideAt, he, Finset.sort_empty, subdivisionFromList, chordLength]

theorem actual_breakpoint_error {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) {a b K : ℝ} (P : Ch09.TaggedPartition a b) (B : Finset ℝ)
    (hK : 0 ≤ K)
    (hL : ∀ x y, a ≤ x → x ≤ y → y ≤ b → ‖γ y - γ x‖ ≤ K*(y-x)) :
    let Q := fun i : Fin (P.n+1) => subdivideAt (P.increasing (Fin.castSucc_lt_succ (i := i))).le B
    0 ≤ (∑ i, chordLength γ (Q i)) - polygonalSum γ P ∧
      (∑ i, chordLength γ (Q i)) - polygonalSum γ P ≤ (B.card : ℝ)*K*P.mesh := by
  classical
  dsimp only
  let changed := Finset.univ.filter (fun i : Fin (P.n+1) =>
    ∃ t ∈ B, t ∈ Ioo (P.points i.castSucc) (P.points i.succ))
  have hp (i : Fin (P.n+1)) (hi : i ∈ changed) :
      ∃ t ∈ B, t ∈ Ioo (P.points i.castSucc) (P.points i.succ) :=
    (Finset.mem_filter.mp hi).2
  let select : Fin (P.n+1) → ℝ := fun i =>
    if hi : i ∈ changed then Classical.choose (hp i hi) else 0
  have hselect (i : Fin (P.n+1)) (hi : i ∈ changed) :
      select i ∈ B ∧ select i ∈ Ioo (P.points i.castSucc) (P.points i.succ) := by
    simpa [select,hi] using Classical.choose_spec (hp i hi)
  have hcard : changed.card ≤ B.card :=
    Finset.card_le_card_of_injOn select
      (fun i hi => (hselect i hi).1) (by
        intro i hi j hj heq
        apply tagged_half_open_unique P
        · exact Ioo_subset_Ioc_self (hselect i hi).2
        · rw [heq]
          exact Ioo_subset_Ioc_self (hselect j hj).2)
  have hmesh : 0 ≤ P.mesh := (sub_nonneg.mpr
    (P.increasing (Fin.castSucc_lt_succ (i := (0 : Fin (P.n+1))))).le).trans
    (Finset.le_sup' (f := P.width) (Finset.mem_univ 0))
  apply polygonal_refinement_error γ P _ changed B.card hcard hK hmesh hL
  intro i hi
  apply subdivideAt_empty_cell
  intro t ht hx
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,ht,hx⟩)

theorem finite_piece_length_limit {X ι : Type*} (F : Filter X) (pieces : Finset ι)
    (pieceSum : ι → X → ℝ) (pieceLength : ι → ℝ) (coarse mesh : X → ℝ)
    (C : ℝ) (hmesh : Tendsto mesh F (𝓝 0))
    (hpiece : ∀ i ∈ pieces, Tendsto (pieceSum i) F (𝓝 (pieceLength i)))
    (herr : ∀ p, 0 ≤ (∑ i ∈ pieces, pieceSum i p) - coarse p ∧
      (∑ i ∈ pieces, pieceSum i p) - coarse p ≤ C * mesh p) :
    Tendsto coarse F (𝓝 (∑ i ∈ pieces, pieceLength i)) := by
  have hsum := tendsto_finsetSum pieces hpiece
  have hc : Tendsto (fun _ : X => C) F (𝓝 C) := tendsto_const_nhds
  have hupper : Tendsto (fun p => C * mesh p) F (𝓝 0) := by
    simpa only [mul_zero] using hc.mul hmesh
  have hzero : Tendsto (fun p => (∑ i ∈ pieces, pieceSum i p) - coarse p) F (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun p => (herr p).1) (fun p => (herr p).2)
  simpa only [sub_zero, sub_sub_cancel] using hsum.sub hzero

end Ch13
