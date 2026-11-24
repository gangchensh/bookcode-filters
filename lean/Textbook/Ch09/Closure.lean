import Textbook.Ch09.DarbouxCriterion

namespace Ch09

open Set

private theorem cell_value_bounds {a b : ℝ} (P : TaggedPartition a b) (f : ℝ → ℝ)
    (M : ℝ) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (i : Fin (P.n+1)) :
    BddBelow (f '' P.closedCell i) ∧ BddAbove (f '' P.closedCell i) := by
  refine ⟨⟨-M,?_⟩,⟨M,?_⟩⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact (abs_le.mp (hf x (P.subinterval_subset i hx))).1
  · rintro _ ⟨x,hx,rfl⟩
    exact (abs_le.mp (hf x (P.subinterval_subset i hx))).2

private theorem gap_cell_le {a b : ℝ} (P : TaggedPartition a b) (f : ℝ → ℝ)
    (i : Fin (P.n+1)) (C : ℝ)
    (h : ∀ x ∈ P.closedCell i, ∀ y ∈ P.closedCell i, f x - f y ≤ C) :
    sSup (f '' P.closedCell i) - sInf (f '' P.closedCell i) ≤ C := by
  have hn : (f '' P.closedCell i).Nonempty := ⟨_,mem_image_of_mem f (P.tag_mem i)⟩
  apply sub_le_iff_le_add.mpr
  apply csSup_le hn
  rintro _ ⟨x,hx,rfl⟩
  have hh : f x - C ≤ sInf (f '' P.closedCell i) := by
    apply le_csInf hn
    rintro _ ⟨y,hy,rfl⟩
    linarith [h x hx y hy]
  linarith

private theorem abs_diff_le_gap {a b : ℝ} (P : TaggedPartition a b) (f : ℝ → ℝ)
    (M : ℝ) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (i : Fin (P.n+1))
    {x y : ℝ} (hx : x ∈ P.closedCell i) (hy : y ∈ P.closedCell i) :
    |f x-f y| ≤ sSup (f '' P.closedCell i) - sInf (f '' P.closedCell i) := by
  have h := cell_value_bounds P f M hf i
  have hx' := mem_image_of_mem f hx
  have hy' := mem_image_of_mem f hy
  rw [abs_le]
  exact ⟨by linarith [csInf_le h.1 hx',le_csSup h.2 hy'],
    by linarith [csInf_le h.1 hy',le_csSup h.2 hx']⟩

private theorem sum_gaps {a b : ℝ} (P : TaggedPartition a b) (f : ℝ → ℝ) :
    P.upperSum f - P.lowerSum f =
      ∑ i, (sSup (f '' P.closedCell i) - sInf (f '' P.closedCell i))*P.width i := by
  simp only [TaggedPartition.upperSum, TaggedPartition.lowerSum, sub_mul, Finset.sum_sub_distrib]

theorem tagged_integrable_abs {a b I : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (h : HasTaggedIntegral f a b I) : ∃ J, HasTaggedIntegral (fun x => |f x|) a b J := by
  obtain ⟨M,_,hf⟩ := tagged_integrable_bounded hab h
  apply tagged_integrable_of_darboux_gap hab _ M (fun x hx => by simpa using hf x hx)
  intro ε hε
  obtain ⟨P,hP⟩ := small_darboux_gap_exists hab f
    (tagged_integral_implies_small_darboux_gap hab f h) ε hε
  refine ⟨P,lt_of_le_of_lt ?_ hP⟩
  rw [sum_gaps,sum_gaps]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (P.increasing (Fin.castSucc_lt_succ (i := i))).le)
  apply gap_cell_le
  intro x hx y hy
  exact (abs_sub_abs_le_abs_sub (f x) (f y)).trans (abs_diff_le_gap P f M hf i hx hy)

theorem tagged_integral_triangle {a b I : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (h : HasTaggedIntegral f a b I) :
    ∃ J, HasTaggedIntegral (fun x => |f x|) a b J ∧ |I| ≤ J := by
  obtain ⟨J,hJ⟩ := tagged_integrable_abs hab h
  exact ⟨J,hJ,by
    rw [← (tagged_measure_agreement hab h).2, ← (tagged_measure_agreement hab hJ).2]
    exact integral_abs_bound hab.le⟩

theorem tagged_integrable_mul {a b I J : ℝ} {f g : ℝ → ℝ} (hab : a < b)
    (h₁ : HasTaggedIntegral f a b I) (h₂ : HasTaggedIntegral g a b J) :
    ∃ K, HasTaggedIntegral (fun x => f x * g x) a b K := by
  obtain ⟨M,hM,hf⟩ := tagged_integrable_bounded hab h₁
  obtain ⟨N,hN,hg⟩ := tagged_integrable_bounded hab h₂
  let F (x : ℝ) := f x * g x
  have hF (x) (hx : x ∈ Icc a b) : |F x| ≤ M*N := by
    change |f x * g x| ≤ M*N
    rw [abs_mul]
    exact mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) hM
  apply tagged_integrable_of_darboux_gap hab F (M*N) hF
  intro ε hε
  let η := ε / (M+N+1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨d,hd,hd'⟩ := tagged_integral_implies_small_darboux_gap hab f h₁ η hη
  obtain ⟨e,he,he'⟩ := tagged_integral_implies_small_darboux_gap hab g h₂ η hη
  obtain ⟨P,hP⟩ := arbitrarily_fine hab (min d e) (lt_min hd he)
  refine ⟨P,?_⟩
  have hcell (i : Fin (P.n+1)) :
      sSup (F '' P.closedCell i) - sInf (F '' P.closedCell i) ≤
        M*(sSup (g '' P.closedCell i)-sInf (g '' P.closedCell i)) +
        N*(sSup (f '' P.closedCell i)-sInf (f '' P.closedCell i)) := by
    apply gap_cell_le
    intro x hx y hy
    have hfx := hf x (P.subinterval_subset i hx)
    have hgy := hg y (P.subinterval_subset i hy)
    calc
      F x - F y ≤ |F x - F y| := le_abs_self _
      _ = |f x*(g x-g y)+(f x-f y)*g y| := by
        congr 1
        dsimp [F]
        ring
      _ ≤ |f x| * |g x-g y| + |f x-f y| * |g y| := by
        simpa only [abs_mul] using abs_add_le (f x*(g x-g y)) ((f x-f y)*g y)
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul hfx (abs_diff_le_gap P g N hg i hx hy) (abs_nonneg _) hM
        · rw [mul_comm N]
          exact mul_le_mul (abs_diff_le_gap P f M hf i hx hy) hgy (abs_nonneg _)
            ((abs_nonneg _).trans (abs_diff_le_gap P f M hf i hx hy))
  have hsum : P.upperSum F - P.lowerSum F ≤
      M*(P.upperSum g - P.lowerSum g)+N*(P.upperSum f-P.lowerSum f) := by
    rw [sum_gaps,sum_gaps,sum_gaps]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hw : 0 ≤ P.width i :=
      sub_nonneg.mpr (P.increasing (Fin.castSucc_lt_succ (i := i))).le
    simpa only [add_mul,mul_assoc] using
      mul_le_mul_of_nonneg_right (hcell i) hw
  have hbound := add_le_add (mul_le_mul_of_nonneg_left (he' P (hP.trans_le (min_le_right _ _))).le hM)
    (mul_le_mul_of_nonneg_left (hd' P (hP.trans_le (min_le_left _ _))).le hN)
  have hscale : η * (M+N+1) = ε := div_mul_cancel₀ _ (by linarith)
  nlinarith

end Ch09
