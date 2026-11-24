import Textbook.Ch13.GridAgreement

namespace Ch09

open MeasureTheory Set Filter
open scoped Interval

/-- Retagging one cell bounds every value of the integrand on that cell. -/
theorem tagged_integrable_bounded {f : ℝ → ℝ} {a b I : ℝ}
    (hab : a < b) (h : HasTaggedIntegral f a b I) :
    ∃ M ≥ 0, ∀ x ∈ Icc a b, |f x| ≤ M := by
  classical
  obtain ⟨δ,hδ,hfine⟩ := (tagged_integral_iff f a b I).1 h 1 zero_lt_one
  obtain ⟨P,hP⟩ := arbitrarily_fine hab δ hδ
  have hw (i : Fin (P.n+1)) : 0 < P.width i :=
    sub_pos.mpr (P.increasing (Fin.castSucc_lt_succ (i := i)))
  let B := fun i => |f (P.tag i)| + 2 / P.width i
  let M := Finset.univ.sup' Finset.univ_nonempty B
  have hM (i) : B i ≤ M := Finset.le_sup' B (Finset.mem_univ i)
  refine ⟨M, (add_nonneg (abs_nonneg _) (div_nonneg (by norm_num) (hw 0).le) : 0 ≤ B 0).trans (hM 0), ?_⟩
  intro x hx
  obtain ⟨i,hi⟩ : ∃ i : Fin (P.n+1), x ∈ Icc (P.points i.castSucc) (P.points i.succ) := by
    rcases eq_or_lt_of_le hx.1 with he | he
    · refine ⟨0, ?_, ?_⟩
      · simpa [P.first] using he.le
      · exact he.ge.trans (P.first.ge.trans (P.increasing.monotone (Fin.zero_le _)))
    · obtain ⟨i,hi⟩ := Ch13.tagged_half_open_cover P ⟨he,hx.2⟩
      exact ⟨i,Ioc_subset_Icc_self hi⟩
  let Q : TaggedPartition a b :=
    { P with
      tag := fun j => if j = i then x else P.tag j
      tag_mem := by
        intro j
        by_cases hj : j = i
        · subst j
          simpa using hi
        · simpa [hj] using P.tag_mem j }
  have hdiff : Q.riemannSum f - P.riemannSum f = (f x - f (P.tag i)) * P.width i := by
    unfold TaggedPartition.riemannSum
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp [Q, TaggedPartition.width, sub_mul]
    · intro j _ hj
      simp [Q, TaggedPartition.width, hj]
    · simp
  have hdist : |Q.riemannSum f - P.riemannSum f| < 2 := by
    have hq := abs_lt.mp (hfine Q hP)
    have hp := abs_lt.mp (hfine P hP)
    exact abs_lt.mpr ⟨by linarith [hq.1,hp.2], by linarith [hq.2,hp.1]⟩
  rw [hdiff, abs_mul, abs_of_pos (hw i)] at hdist
  have hcell : |f x - f (P.tag i)| < 2 / P.width i := (lt_div_iff₀ (hw i)).2 hdist
  exact (calc
    |f x| = |(f x - f (P.tag i)) + f (P.tag i)| := by rw [sub_add_cancel]
    _ ≤ |f x - f (P.tag i)| + |f (P.tag i)| := abs_add_le _ _
    _ ≤ B i := by dsimp [B]; linarith).trans (hM i)

/-- Taking a weighted average of the column sums gives the rectangular sum
for an integrand which depends only on the first coordinate. -/
theorem tagged_lift_unit_rectangle {f : ℝ → ℝ} {a b I : ℝ}
    (h : HasTaggedIntegral f a b I) :
    Ch13.HasRectangleIntegral (fun z => f z.1) a b 0 1 I := by
  rw [Ch13.rectangle_mesh_iff]
  intro ε hε
  obtain ⟨δ,hδ,hfine⟩ := (tagged_integral_iff f a b I).1 h (ε/2) (by linarith)
  refine ⟨δ,hδ,?_⟩
  intro P hP
  let X (j : Fin (P.y.n+1)) : TaggedPartition a b :=
    { P.x with tag := fun i => (P.tag i j).1, tag_mem := fun i => P.tag_x i j }
  have hw (j : Fin (P.y.n+1)) : 0 ≤ P.y.width j :=
    sub_nonneg.mpr (P.y.increasing (Fin.castSucc_lt_succ (i := j))).le
  have hs : ∑ j, P.y.width j = 1 := by
    unfold TaggedPartition.width
    rw [sum_endpoint_differences, P.y.last, P.y.first, sub_zero]
  have hc (j : Fin (P.y.n+1)) : |(X j).riemannSum f - I| < ε/2 :=
    hfine (X j) ((le_max_left _ _).trans_lt hP)
  have he : Ch13.rectangleSum (fun z => f z.1) P - I =
      ∑ j, ((X j).riemannSum f - I) * P.y.width j := by
    simp only [Ch13.rectangleSum, TaggedPartition.riemannSum, sub_mul, Finset.sum_sub_distrib,
      Finset.sum_mul, ← Finset.mul_sum, hs, mul_one, X, mul_assoc]
    rw [Finset.sum_comm]
    rfl
  rw [he]
  calc
    _ ≤ ∑ j, |((X j).riemannSum f - I) * P.y.width j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (ε/2) * P.y.width j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hw j)]
      exact mul_le_mul_of_nonneg_right (hc j).le (hw j)
    _ = ε/2 := by rw [← Finset.mul_sum, hs, mul_one]
    _ < ε := by linarith

/-- No continuity or measurability assumption on the original representative is needed. -/
theorem tagged_measure_agreement {f : ℝ → ℝ} {a b I : ℝ} (hab : a < b)
    (h : HasTaggedIntegral f a b I) :
    IntervalIntegrable f volume a b ∧ (∫ x in a..b, f x) = I := by
  obtain ⟨M,_,hf⟩ := tagged_integrable_bounded hab h
  obtain ⟨hi,hval⟩ := Ch13.tagged_rectangle_measure_agreement hab zero_lt_one
    (fun z => f z.1) M (fun z hz => hf z.1 hz.1) (tagged_lift_unit_rectangle h)
  have hp : Integrable (fun z : ℝ × ℝ => f z.1)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hi
  have hne : NeZero (volume.restrict (Icc (0:ℝ) 1)) := ⟨by
    intro hz
    have hz' := congrArg (fun μ : Measure ℝ => μ univ) hz
    simpa [Measure.restrict_apply MeasurableSet.univ, Real.volume_Icc] using hz'⟩
  have h1 : IntegrableOn f (Icc a b) := by
    obtain ⟨y,hy⟩ := hp.prod_left_ae.exists
    exact hy
  have hv : (∫ x in Icc a b, f x) = I := by
    rw [setIntegral_prod _ hi] at hval
    simpa [setIntegral_const, Measure.real_def, Real.volume_Icc] using hval
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (h1.mono_set Ioc_subset_Icc_self), ?_⟩
  rwa [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]

end Ch09
