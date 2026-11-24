import Textbook.Ch09.Tagged

namespace Ch09

open Set

def TaggedPartition.closedCell {a b : ℝ} (P : TaggedPartition a b) (i : Fin (P.n+1)) :
    Set ℝ := Icc (P.points i.castSucc) (P.points i.succ)

noncomputable def TaggedPartition.lowerSum {a b : ℝ} (P : TaggedPartition a b)
    (f : ℝ → ℝ) : ℝ := ∑ i, sInf (f '' P.closedCell i) * P.width i

noncomputable def TaggedPartition.upperSum {a b : ℝ} (P : TaggedPartition a b)
    (f : ℝ → ℝ) : ℝ := ∑ i, sSup (f '' P.closedCell i) * P.width i

/-- Existence of a tagged integral forces a uniformly small gap on fine point lists. -/
theorem tagged_integral_implies_small_darboux_gap {a b I : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hI : HasTaggedIntegral f a b I) :
    ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b,
      P.mesh < δ → P.upperSum f - P.lowerSum f < ε := by
  classical
  intro ε hε
  obtain ⟨δ,hδ,hfine⟩ := (tagged_integral_iff f a b I).1 hI (ε/4) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro P hP
  let η := (ε/8)/(b-a)
  have hη : 0 < η := div_pos (by positivity) (sub_pos.mpr hab)
  have hηw : η * (b-a) = ε/8 := div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
  have hn (i : Fin (P.n+1)) : (f '' P.closedCell i).Nonempty :=
    ⟨f (P.tag i), mem_image_of_mem f (P.tag_mem i)⟩
  have hl (i : Fin (P.n+1)) : ∃ x ∈ P.closedCell i, f x < sInf (f '' P.closedCell i) + η := by
    obtain ⟨_,⟨x,hx,rfl⟩,h⟩ := exists_lt_of_csInf_lt (hn i) (lt_add_of_pos_right _ hη)
    exact ⟨x,hx,h⟩
  have hu (i : Fin (P.n+1)) : ∃ x ∈ P.closedCell i, sSup (f '' P.closedCell i) - η < f x := by
    obtain ⟨_,⟨x,hx,rfl⟩,h⟩ := exists_lt_of_lt_csSup (hn i) (sub_lt_self _ hη)
    exact ⟨x,hx,h⟩
  choose l hlm hlt using hl
  choose u hum hut using hu
  let L : TaggedPartition a b := {P with tag := l, tag_mem := hlm}
  let U : TaggedPartition a b := {P with tag := u, tag_mem := hum}
  have hw (i : Fin (P.n+1)) : 0 ≤ P.width i :=
    sub_nonneg.mpr (P.increasing (Fin.castSucc_lt_succ (i := i))).le
  have hsum : ∑ i, P.width i = b-a := by
    unfold TaggedPartition.width
    rw [sum_endpoint_differences, P.last, P.first]
  have hL : L.riemannSum f ≤ P.lowerSum f + ε/8 := by
    calc
      _ ≤ ∑ i, (sInf (f '' P.closedCell i)+η)*P.width i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlt i).le (hw i)
      _ = _ := by
        simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hηw,
          TaggedPartition.lowerSum]
  have hU : P.upperSum f ≤ U.riemannSum f + ε/8 := by
    calc
      _ ≤ ∑ i, (f (u i)+η)*P.width i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by linarith [hut i]) (hw i)
      _ = _ := by
        simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hηw,
          TaggedPartition.riemannSum, U]
        rfl
  have h1 := (abs_lt.mp (hfine L hP)).1
  have h2 := (abs_lt.mp (hfine U hP)).2
  linarith

theorem small_darboux_gap_exists {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b,
      P.mesh < δ → P.upperSum f - P.lowerSum f < ε) :
    ∀ ε > 0, ∃ P : TaggedPartition a b, P.upperSum f - P.lowerSum f < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hδ'⟩ := h ε hε
  obtain ⟨P,hP⟩ := arbitrarily_fine hab δ hδ
  exact ⟨P,hδ' P hP⟩

end Ch09
