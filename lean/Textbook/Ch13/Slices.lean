import Textbook.Ch13.Audit

namespace Ch13

open Set
open scoped BigOperators

/-- The same vertical mesh can approximate all slices at the finitely many outer tags. -/
theorem tagged_vertical_slices {a b c d I : ℝ} (hab : a < b) (hcd : c < d)
    (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (hI : HasRectangleIntegral f a b c d I)
    (hg : ∀ x ∈ Icc a b, Ch09.HasTaggedIntegral (fun y => f (x,y)) c d (g x)) :
    Ch09.HasTaggedIntegral g a b I := by
  classical
  apply (Ch09.tagged_integral_iff g a b I).2
  intro ε hε
  obtain ⟨δ,hδ,hrect⟩ := (rectangle_mesh_iff f a b c d I).1 hI (ε/2) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro X hX
  let η := (ε/2)/(b-a)
  have hη : 0 < η := div_pos (by positivity) (sub_pos.mpr hab)
  have hs (i : Fin (X.n+1)) :=
    (Ch09.tagged_integral_iff _ c d (g (X.tag i))).1
      (hg (X.tag i) (X.subinterval_subset i (X.tag_mem i))) η hη
  choose r hr hslice using hs
  let ρ := Finset.univ.inf' Finset.univ_nonempty r
  have hρ : 0 < ρ := by
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty r
    change ρ = r i at hi
    rw [hi]
    exact hr i
  obtain ⟨Y,hY⟩ := Ch09.arbitrarily_fine hcd (min δ ρ) (lt_min hδ hρ)
  let P : RectPartition a b c d :=
    ⟨X,Y,fun i j => (X.tag i,Y.tag j),fun i _ => X.tag_mem i,fun _ j => Y.tag_mem j⟩
  have hsum : rectangleSum f P =
      ∑ i : Fin (X.n+1), (Y.riemannSum (fun y => f (X.tag i,y))) * X.width i := by
    unfold rectangleSum
    apply Finset.sum_congr rfl
    intro i _
    rw [Ch09.TaggedPartition.riemannSum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hdiff : |X.riemannSum g - rectangleSum f P| ≤ ε/2 := by
    rw [hsum, Ch09.TaggedPartition.riemannSum, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    calc
      _ ≤ ∑ i : Fin (X.n+1), |g (X.tag i) - Y.riemannSum (fun y => f (X.tag i,y))| *
          |X.width i| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
          (fun i : Fin (X.n+1) => (g (X.tag i) - Y.riemannSum (fun y => f (X.tag i,y))) *
            X.width i) Finset.univ
      _ ≤ ∑ i : Fin (X.n+1), η * X.width i := by
        apply Finset.sum_le_sum
        intro i _
        have hw : 0 ≤ X.width i := sub_nonneg.mpr
          (X.increasing (Fin.castSucc_lt_succ (i := i))).le
        rw [abs_of_nonneg hw, abs_sub_comm]
        exact mul_le_mul_of_nonneg_right
          (hslice i Y ((hY.trans_le (min_le_right _ _)).trans_le
            (Finset.inf'_le (f := r) (Finset.mem_univ i)))).le hw
      _ = ε/2 := by
        rw [← Finset.mul_sum]
        unfold Ch09.TaggedPartition.width
        rw [Ch09.sum_endpoint_differences, X.first, X.last]
        exact div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
  have hp := hrect P (max_lt hX (hY.trans_le (min_le_left _ _)))
  exact (abs_sub_le _ (rectangleSum f P) _).trans_lt (by linarith)

def RectPartition.swap {a b c d : ℝ} (P : RectPartition a b c d) :
    RectPartition c d a b :=
  ⟨P.y,P.x,fun j i => ((P.tag i j).2,(P.tag i j).1),
    fun j i => P.tag_y i j,fun j i => P.tag_x i j⟩

theorem tagged_horizontal_slices {a b c d I : ℝ} (hab : a < b) (hcd : c < d)
    (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (hI : HasRectangleIntegral f a b c d I)
    (hg : ∀ y ∈ Icc c d, Ch09.HasTaggedIntegral (fun x => f (x,y)) a b (g y)) :
    Ch09.HasTaggedIntegral g c d I := by
  apply tagged_vertical_slices hcd hab (fun z => f (z.2,z.1)) g _ hg
  apply (rectangle_mesh_iff _ c d a b I).2
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := (rectangle_mesh_iff f a b c d I).1 hI ε hε
  refine ⟨δ,hδ,fun P hP => ?_⟩
  have hmesh : rectangleMesh P.swap = rectangleMesh P := max_comm _ _
  have hsum : rectangleSum f P.swap = rectangleSum (fun z => f (z.2,z.1)) P := by
    unfold rectangleSum RectPartition.swap
    rw [Finset.sum_comm]
    simp only [mul_comm (P.y.width _)]
  rw [← hsum]
  exact h P.swap (hmesh ▸ hP)

end Ch13
