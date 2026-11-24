import Textbook.Ch13.GridAgreement

namespace Ch13
open Set
open scoped BigOperators

theorem rectangle_integral_linear {a b c d I J : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : HasRectangleIntegral f a b c d I) (hg : HasRectangleIntegral g a b c d J)
    (u v : ℝ) :
    HasRectangleIntegral (fun z => u*f z + v*g z) a b c d (u*I + v*J) := by
  apply (rectangle_mesh_iff _ _ _ _ _ _).2
  intro ε hε
  let η := ε/(|u|+|v|+1)
  have hD : 0 < |u|+|v|+1 := by positivity
  have hη : 0 < η := div_pos hε hD
  obtain ⟨δ,hδ,h₁⟩ := (rectangle_mesh_iff _ _ _ _ _ _).1 hf η hη
  obtain ⟨ρ,hρ,h₂⟩ := (rectangle_mesh_iff _ _ _ _ _ _).1 hg η hη
  refine ⟨min δ ρ,lt_min hδ hρ,fun P hP => ?_⟩
  have hs : rectangleSum (fun z => u*f z + v*g z) P =
      u*rectangleSum f P + v*rectangleSum g P := by
    simp only [rectangleSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [hs, show u*rectangleSum f P+v*rectangleSum g P-(u*I+v*J) =
    u*(rectangleSum f P-I)+v*(rectangleSum g P-J) by ring]
  calc
    _ ≤ |u*(rectangleSum f P-I)|+|v*(rectangleSum g P-J)| := abs_add_le _ _
    _ ≤ |u| * η + |v| * η := by
      rw [abs_mul,abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (h₁ P (hP.trans_le (min_le_left _ _))).le (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (h₂ P (hP.trans_le (min_le_right _ _))).le (abs_nonneg _))
    _ < ε := by
      have he : η*(|u|+|v|+1)=ε := div_mul_cancel₀ _ hD.ne'
      nlinarith

theorem cell_area_nonneg {a b c d : ℝ} (P : RectPartition a b c d)
    (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) :
    0 ≤ P.x.width i * P.y.width j :=
  mul_nonneg (sub_nonneg.mpr (P.x.increasing (Fin.castSucc_lt_succ (i := i))).le)
    (sub_nonneg.mpr (P.y.increasing (Fin.castSucc_lt_succ (i := j))).le)

private theorem rectangle_integral_compare {a b c d I J : ℝ}
    (hab : a < b) (hcd : c < d) {f g : ℝ × ℝ → ℝ}
    (hf : HasRectangleIntegral f a b c d I) (hg : HasRectangleIntegral g a b c d J)
    (hs : ∀ P : RectPartition a b c d, rectangleSum f P ≤ rectangleSum g P) : I ≤ J := by
  by_contra! h
  have hε : 0 < (I-J)/3 := by linarith
  obtain ⟨δ,hδ,h₁⟩ := (rectangle_mesh_iff _ _ _ _ _ _).1 hf _ hε
  obtain ⟨ρ,hρ,h₂⟩ := (rectangle_mesh_iff _ _ _ _ _ _).1 hg _ hε
  obtain ⟨P,hP⟩ := rectangle_arbitrarily_fine hab hcd (min δ ρ) (lt_min hδ hρ)
  have hl := (abs_lt.mp (h₁ P (hP.trans_le (min_le_left _ _)))).1
  have hu := (abs_lt.mp (h₂ P (hP.trans_le (min_le_right _ _)))).2
  linarith [hs P]

theorem rectangle_integral_mono {a b c d I J : ℝ} (hab : a < b) (hcd : c < d)
    {f g : ℝ × ℝ → ℝ} (hf : HasRectangleIntegral f a b c d I)
    (hg : HasRectangleIntegral g a b c d J)
    (h : ∀ z ∈ Icc a b ×ˢ Icc c d, f z ≤ g z) : I ≤ J := by
  apply rectangle_integral_compare hab hcd hf hg
  intro P
  unfold rectangleSum
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_right
      (h _ ⟨P.x.subinterval_subset i (P.tag_x i j),P.y.subinterval_subset j (P.tag_y i j)⟩)
      (cell_area_nonneg P i j)))

theorem rectangle_integral_abs_bound {a b c d I J : ℝ} (hab : a < b) (hcd : c < d)
    {f : ℝ × ℝ → ℝ} (hf : HasRectangleIntegral f a b c d I)
    (habs : HasRectangleIntegral (fun z => |f z|) a b c d J) : |I| ≤ J := by
  have hn : HasRectangleIntegral (fun z => -f z) a b c d (-I) := by
    simpa only [neg_one_mul,zero_mul,add_zero] using rectangle_integral_linear hf hf (-1) 0
  exact abs_le.mpr ⟨by
    have h := rectangle_integral_mono hab hcd hn habs (fun z _ => neg_le_abs (f z))
    linarith, rectangle_integral_mono hab hcd hf habs (fun z _ => le_abs_self (f z))⟩

theorem region_integral_linear {a b c d I J : ℝ} {D : Set (ℝ × ℝ)}
    {f g : ℝ × ℝ → ℝ} (hf : HasRegionIntegral a b c d D f I)
    (hg : HasRegionIntegral a b c d D g J) (u v : ℝ) :
    HasRegionIntegral a b c d D (fun z => u*f z + v*g z) (u*I + v*J) := by
  have he : D.indicator (fun z => u*f z + v*g z) =
      fun z => u*D.indicator f z + v*D.indicator g z := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  exact ⟨hf.1, he ▸ rectangle_integral_linear hf.2 hg.2 u v⟩

theorem region_integral_mono {a b c d I J : ℝ} (hab : a < b) (hcd : c < d)
    {D : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : HasRegionIntegral a b c d D f I) (hg : HasRegionIntegral a b c d D g J)
    (h : ∀ z ∈ D, f z ≤ g z) : I ≤ J := by
  apply rectangle_integral_mono hab hcd hf.2 hg.2
  intro z _
  by_cases hz : z ∈ D
  · simpa [hz] using h z hz
  · simp [hz]

theorem region_integral_abs_bound {a b c d I J : ℝ} (hab : a < b) (hcd : c < d)
    {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} (hf : HasRegionIntegral a b c d D f I)
    (hg : HasRegionIntegral a b c d D (fun z => |f z|) J) : |I| ≤ J := by
  apply rectangle_integral_abs_bound hab hcd hf.2
  have he : (fun z => |D.indicator f z|) = D.indicator (fun z => |f z|) := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  rw [he]
  exact hg.2

theorem region_integral_mean_value {a b c d I A : ℝ} (hab : a < b) (hcd : c < d)
    {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hD : IsCompact D) (hne : D.Nonempty) (hconn : IsPreconnected D)
    (hcont : ContinuousOn f D) (hA : 0 < A)
    (harea : HasRegionIntegral a b c d D (fun _ => 1) A)
    (hf : HasRegionIntegral a b c d D f I) : ∃ z ∈ D, I = f z * A := by
  obtain ⟨l,hl,hmin⟩ := hD.exists_isMinOn hne hcont
  obtain ⟨r,hr,hmax⟩ := hD.exists_isMaxOn hne hcont
  have hconst (u : ℝ) : HasRegionIntegral a b c d D (fun _ => u) (u*A) := by
    simpa only [mul_one,zero_mul,add_zero] using region_integral_linear harea harea u 0
  have hlo := region_integral_mono hab hcd (hconst (f l)) hf (fun z hz => hmin hz)
  have hhi := region_integral_mono hab hcd hf (hconst (f r)) (fun z hz => hmax hz)
  have hv : I/A ∈ Icc (f l) (f r) :=
    ⟨(le_div_iff₀ hA).2 hlo, (div_le_iff₀ hA).2 hhi⟩
  obtain ⟨z,hz,he⟩ := hconn.intermediate_value hl hr hcont hv
  exact ⟨z,hz,(div_mul_cancel₀ I hA.ne').symm.trans (congrArg (· * A) he.symm)⟩

end Ch13
