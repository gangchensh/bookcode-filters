import Textbook.Ch13.Grid

namespace Ch13

open MeasureTheory Set
open scoped BigOperators

theorem grid_total_area {a b c d : ℝ} (P : RectPartition a b c d) :
    (∑ i, ∑ j, P.x.width i * P.y.width j) = (b-a) * (d-c) := by
  have hx : (∑ i, P.x.width i) = b-a := by
    unfold Ch09.TaggedPartition.width
    rw [Ch09.sum_endpoint_differences, P.x.first, P.x.last]
  have hy : (∑ j, P.y.width j) = d-c := by
    unfold Ch09.TaggedPartition.width
    rw [Ch09.sum_endpoint_differences, P.y.first, P.y.last]
  simp_rw [← Finset.mul_sum, hy]
  rw [← Finset.sum_mul, hx]

theorem grid_gap_of_tagged_integral {a b c d I : ℝ} (hab : a < b) (hcd : c < d)
    (f : ℝ × ℝ → ℝ) (hI : HasRectangleIntegral f a b c d I) :
    ∀ ε > 0, ∃ P : RectPartition a b c d,
      I - ε/2 < (∫ z, gridLower P f z ∂volume.prod volume) ∧
      (∫ z, gridUpper P f z ∂volume.prod volume) < I + ε/2 ∧
      (∫ z, gridUpper P f z ∂volume.prod volume) -
        (∫ z, gridLower P f z ∂volume.prod volume) < ε := by
  classical
  intro ε hε
  let A := (b-a)*(d-c)
  have hA : 0 < A := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hcd)
  let η := (ε/4)/A
  have hη : 0 < η := div_pos (by positivity) hA
  have hηA : η*A = ε/4 := div_mul_cancel₀ _ hA.ne'
  obtain ⟨δ,hδ,happrox⟩ := (rectangle_mesh_iff f a b c d I).1 hI (ε/4) (by positivity)
  obtain ⟨P,hP⟩ := rectangle_arbitrarily_fine hab hcd δ hδ
  have hnon (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) :
      (f '' closedGridCell P i j).Nonempty :=
    ⟨f (P.tag i j), mem_image_of_mem f ⟨P.tag_x i j,P.tag_y i j⟩⟩
  have hlow (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) :
      ∃ z ∈ closedGridCell P i j, f z < sInf (f '' closedGridCell P i j) + η := by
    obtain ⟨_,⟨z,hz,rfl⟩,h⟩ := exists_lt_of_csInf_lt (hnon i j) (lt_add_of_pos_right _ hη)
    exact ⟨z,hz,h⟩
  have hupp (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) :
      ∃ z ∈ closedGridCell P i j, sSup (f '' closedGridCell P i j) - η < f z := by
    obtain ⟨_,⟨z,hz,rfl⟩,h⟩ := exists_lt_of_lt_csSup (hnon i j) (sub_lt_self _ hη)
    exact ⟨z,hz,h⟩
  choose l hl hlt using hlow
  choose u hu hut using hupp
  let PL : RectPartition a b c d := ⟨P.x,P.y,l,fun i j => (hl i j).1,fun i j => (hl i j).2⟩
  let PU : RectPartition a b c d := ⟨P.x,P.y,u,fun i j => (hu i j).1,fun i j => (hu i j).2⟩
  have haL := abs_lt.mp (happrox PL hP)
  have haU := abs_lt.mp (happrox PU hP)
  have hw (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) : 0 ≤ P.x.width i * P.y.width j :=
    mul_nonneg (sub_nonneg.mpr (P.x.increasing (Fin.castSucc_lt_succ (i := i))).le)
      (sub_nonneg.mpr (P.y.increasing (Fin.castSucc_lt_succ (i := j))).le)
  let w := fun (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) => P.x.width i * P.y.width j
  have hsum (k : Fin (P.x.n+1) → Fin (P.y.n+1) → ℝ) :
      (∑ i, ∑ j, (k i j + η) * w i j) = (∑ i, ∑ j, k i j * w i j) + ε/4 := by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [show (∑ i, ∑ j, w i j) = A from grid_total_area P, hηA]
  have hupper : (∫ z, gridUpper P f z ∂volume.prod volume) ≤ rectangleSum f PU + ε/4 := by
    unfold gridUpper
    rw [gridStep_integral]
    change (∑ i, ∑ j, sSup (f '' closedGridCell P i j) * w i j) ≤ _
    calc
      _ ≤ ∑ i, ∑ j, (f (u i j) + η) * w i j := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (by linarith [hut i j]) (hw i j)))
      _ = _ := hsum (fun i j => f (u i j))
  have hlower : rectangleSum f PL ≤ (∫ z, gridLower P f z ∂volume.prod volume) + ε/4 := by
    unfold gridLower
    rw [gridStep_integral]
    change (∑ i, ∑ j, f (l i j) * w i j) ≤ _
    calc
      _ ≤ ∑ i, ∑ j, (sInf (f '' closedGridCell P i j) + η) * w i j := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hlt i j).le (hw i j)))
      _ = _ := hsum (fun i j => sInf (f '' closedGridCell P i j))
  exact ⟨P, by linarith [haL.1], by linarith [haU.2], by linarith [haU.2,haL.1]⟩

end Ch13
