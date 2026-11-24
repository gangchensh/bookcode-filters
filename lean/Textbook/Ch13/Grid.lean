import Textbook.Ch13.Darboux

namespace Ch13
open MeasureTheory Set
open scoped BigOperators ENNReal

def gridCell {a b c d : ℝ} (P : RectPartition a b c d)
    (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) : Set (ℝ × ℝ) :=
  Ioc (P.x.points i.castSucc) (P.x.points i.succ) ×ˢ
    Ioc (P.y.points j.castSucc) (P.y.points j.succ)

def closedGridCell {a b c d : ℝ} (P : RectPartition a b c d)
    (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) : Set (ℝ × ℝ) :=
  Icc (P.x.points i.castSucc) (P.x.points i.succ) ×ˢ
    Icc (P.y.points j.castSucc) (P.y.points j.succ)

theorem gridCell_measurable {a b c d : ℝ} (P : RectPartition a b c d)
    (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) : MeasurableSet (gridCell P i j) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem gridCell_volume {a b c d : ℝ} (P : RectPartition a b c d)
    (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) :
    (volume.prod volume).real (gridCell P i j) = P.x.width i * P.y.width j := by
  rw [gridCell, measureReal_prod_prod, Real.volume_real_Ioc_of_le, Real.volume_real_Ioc_of_le]
  · rfl
  · exact (P.y.increasing (Fin.castSucc_lt_succ (i := j))).le
  · exact (P.x.increasing (Fin.castSucc_lt_succ (i := i))).le

noncomputable def gridStep {a b c d : ℝ} (P : RectPartition a b c d)
    (coeff : Fin (P.x.n+1) → Fin (P.y.n+1) → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑ i, ∑ j, (gridCell P i j).indicator (fun _ => coeff i j) z

theorem gridStep_measurable {a b c d : ℝ} (P : RectPartition a b c d)
    (coeff : Fin (P.x.n+1) → Fin (P.y.n+1) → ℝ) : Measurable (gridStep P coeff) := by
  unfold gridStep
  exact Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => measurable_const.indicator (gridCell_measurable P i j)))

theorem grid_indicator_integrable {a b c d : ℝ} (P : RectPartition a b c d)
    (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) (v : ℝ) :
    Integrable ((gridCell P i j).indicator (fun _ => v)) (volume.prod volume) := by
  apply (integrable_indicator_iff (gridCell_measurable P i j)).2
  apply integrableOn_const _ (by finiteness)
  rw [gridCell, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem gridStep_integral {a b c d : ℝ} (P : RectPartition a b c d)
    (coeff : Fin (P.x.n+1) → Fin (P.y.n+1) → ℝ) :
    (∫ z, gridStep P coeff z ∂volume.prod volume) =
      ∑ i, ∑ j, coeff i j * (P.x.width i * P.y.width j) := by
  unfold gridStep
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    grid_indicator_integrable P i j (coeff i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => grid_indicator_integrable P i j (coeff i j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (gridCell_measurable P i j), setIntegral_const, gridCell_volume]
  exact mul_comm _ _

theorem tagged_half_open_cover {a b : ℝ} (P : Ch09.TaggedPartition a b)
    {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ i : Fin (P.n+1), x ∈ Ioc (P.points i.castSucc) (P.points i.succ) := by
  let p : ℕ → ℝ := fun k => if h : k < P.n+2 then P.points ⟨k,h⟩ else b
  have hp (k : ℕ) (hk : k < P.n+2) : p k = P.points ⟨k,hk⟩ := by simp [p,hk]
  have h0 : p 0 = a := (hp 0 (by omega)).trans P.first
  have hn : p (P.n+1) = b := (hp (P.n+1) (by omega)).trans P.last
  have hm : x ∈ Ioc (p 0) (p (P.n+1)) := by simpa only [h0,hn] using hx
  have hu := Ioc_subset_biUnion_Ioc (P.n+1) p hm
  obtain ⟨k,hk⟩ := mem_iUnion.mp hu
  obtain ⟨hk,hxk⟩ := mem_iUnion.mp hk
  have hkn := Finset.mem_range.mp hk
  rw [hp k (by omega), hp (k+1) (by omega)] at hxk
  exact ⟨⟨k,hkn⟩, hxk⟩

theorem tagged_half_open_unique {a b : ℝ} (P : Ch09.TaggedPartition a b)
    {x : ℝ} {i j : Fin (P.n+1)}
    (hi : x ∈ Ioc (P.points i.castSucc) (P.points i.succ))
    (hj : x ∈ Ioc (P.points j.castSucc) (P.points j.succ)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hle : i.succ ≤ j.castSucc := by
      change i.val+1 ≤ j.val
      exact Nat.succ_le_of_lt h
    exact False.elim (not_lt_of_ge (hi.2.trans (P.increasing.monotone hle)) hj.1)
  · exact h
  · have hle : j.succ ≤ i.castSucc := by
      change j.val+1 ≤ i.val
      exact Nat.succ_le_of_lt h
    exact False.elim (not_lt_of_ge (hj.2.trans (P.increasing.monotone hle)) hi.1)

theorem gridStep_on_cell {a b c d : ℝ} (P : RectPartition a b c d)
    (coeff : Fin (P.x.n+1) → Fin (P.y.n+1) → ℝ)
    {z : ℝ × ℝ} {i : Fin (P.x.n+1)} {j : Fin (P.y.n+1)}
    (hz : z ∈ gridCell P i j) : gridStep P coeff z = coeff i j := by
  classical
  unfold gridStep
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · exact indicator_of_mem hz _
    · intro k _ hk
      exact indicator_of_notMem (fun h => hk (tagged_half_open_unique P.y h.2 hz.2)) _
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro m _
    exact indicator_of_notMem (fun h => hk (tagged_half_open_unique P.x h.1 hz.1)) _
  · simp

noncomputable def gridLower {a b c d : ℝ} (P : RectPartition a b c d)
    (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  gridStep P (fun i j => sInf (f '' closedGridCell P i j))

noncomputable def gridUpper {a b c d : ℝ} (P : RectPartition a b c d)
    (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  gridStep P (fun i j => sSup (f '' closedGridCell P i j))

theorem grid_bounds {a b c d : ℝ} (P : RectPartition a b c d) (f : ℝ × ℝ → ℝ)
    (M : ℝ) (hf : ∀ z ∈ Icc a b ×ˢ Icc c d, |f z| ≤ M)
    {z : ℝ × ℝ} (hz : z ∈ Ioc a b ×ˢ Ioc c d) :
    gridLower P f z ≤ f z ∧ f z ≤ gridUpper P f z := by
  obtain ⟨i,hi⟩ := tagged_half_open_cover P.x hz.1
  obtain ⟨j,hj⟩ := tagged_half_open_cover P.y hz.2
  have hc : z ∈ gridCell P i j := ⟨hi,hj⟩
  have hz' : f z ∈ f '' closedGridCell P i j :=
    mem_image_of_mem f ⟨Ioc_subset_Icc_self hi,Ioc_subset_Icc_self hj⟩
  have hbound : ∀ x ∈ f '' closedGridCell P i j, -M ≤ x ∧ x ≤ M := by
    rintro _ ⟨p,hp,rfl⟩
    exact abs_le.mp (hf p ⟨P.x.subinterval_subset i hp.1,P.y.subinterval_subset j hp.2⟩)
  unfold gridLower gridUpper
  rw [gridStep_on_cell P _ hc, gridStep_on_cell P _ hc]
  exact ⟨csInf_le ⟨-M,fun x hx => (hbound x hx).1⟩ hz',
    le_csSup ⟨M,fun x hx => (hbound x hx).2⟩ hz'⟩

theorem gridStep_integrable {a b c d : ℝ} (P : RectPartition a b c d)
    (coeff : Fin (P.x.n+1) → Fin (P.y.n+1) → ℝ) :
    Integrable (gridStep P coeff) (volume.prod volume) := by
  unfold gridStep
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    grid_indicator_integrable P i j (coeff i j)))

theorem gridCell_subset_rectangle {a b c d : ℝ} (P : RectPartition a b c d)
    (i : Fin (P.x.n+1)) (j : Fin (P.y.n+1)) :
    gridCell P i j ⊆ Ioc a b ×ˢ Ioc c d := by
  intro z hz
  have hx := P.x.subinterval_subset i (Ioc_subset_Icc_self hz.1)
  have hy := P.y.subinterval_subset j (Ioc_subset_Icc_self hz.2)
  have hlx : a ≤ P.x.points i.castSucc := P.x.first.ge.trans (P.x.increasing.monotone (Fin.zero_le _))
  have hly : c ≤ P.y.points j.castSucc := P.y.first.ge.trans (P.y.increasing.monotone (Fin.zero_le _))
  exact ⟨⟨hlx.trans_lt hz.1.1,hx.2⟩,⟨hly.trans_lt hz.2.1,hy.2⟩⟩

theorem gridStep_off_rectangle {a b c d : ℝ} (P : RectPartition a b c d)
    (coeff : Fin (P.x.n+1) → Fin (P.y.n+1) → ℝ)
    {z : ℝ × ℝ} (hz : z ∉ Ioc a b ×ˢ Ioc c d) : gridStep P coeff z = 0 := by
  unfold gridStep
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact indicator_of_notMem (fun h => hz (gridCell_subset_rectangle P i j h)) _

theorem grid_bounds_zero_extended {a b c d : ℝ} (P : RectPartition a b c d)
    (f : ℝ × ℝ → ℝ) (M : ℝ) (hf : ∀ z ∈ Icc a b ×ˢ Icc c d, |f z| ≤ M)
    (z : ℝ × ℝ) :
    gridLower P f z ≤ (Ioc a b ×ˢ Ioc c d).indicator f z ∧
      (Ioc a b ×ˢ Ioc c d).indicator f z ≤ gridUpper P f z := by
  by_cases hz : z ∈ Ioc a b ×ˢ Ioc c d
  · rw [indicator_of_mem hz]
    exact grid_bounds P f M hf hz
  · simp [indicator_of_notMem hz, gridLower, gridUpper, gridStep_off_rectangle P _ hz]

end Ch13
