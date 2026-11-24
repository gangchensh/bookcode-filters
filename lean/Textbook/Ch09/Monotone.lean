import Textbook.Ch09.Tagged

namespace Ch09

open MeasureTheory Set
open scoped Interval

theorem monotone_tagged_integral {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hf : MonotoneOn f (Icc a b)) :
    HasTaggedIntegral f a b (∫ x in a..b, f x) := by
  have hvar : 0 ≤ f b - f a := sub_nonneg.mpr
    (hf (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab.le)
  apply (tagged_integral_iff _ _ _ _).2
  intro ε hε
  let δ := ε/(f b - f a + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  refine ⟨δ,hδ,?_⟩
  intro P hP
  let A (t : ℝ) := ∫ x in a..t, f x
  have hint {l r : ℝ} (hlr : l ≤ r) (hsub : Icc l r ⊆ Icc a b) :
      IntervalIntegrable f volume l r := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hlr]
    exact hf.mono hsub
  have hcell (i : Fin (P.n+1)) :
      |f (P.tag i)*P.width i - (A (P.points i.succ)-A (P.points i.castSucc))| ≤
        (f (P.points i.succ)-f (P.points i.castSucc))*P.mesh := by
    let l := P.points i.castSucc
    let r := P.points i.succ
    have hlr : l ≤ r := (P.increasing (Fin.castSucc_lt_succ (i := i))).le
    have hsub : Icc l r ⊆ Icc a b := P.subinterval_subset i
    have hal := (hsub (left_mem_Icc.mpr hlr)).1
    have hlb := (hsub (left_mem_Icc.mpr hlr)).2
    have hi := hint hlr hsub
    have hA : A r - A l = ∫ x in l..r, f x := by
      have he := intervalIntegral.integral_add_adjacent_intervals
        (hint hal (Icc_subset_Icc_right hlb)) hi
      dsimp [A]
      linarith
    have hfl := hf (hsub (left_mem_Icc.mpr hlr)) (hsub (right_mem_Icc.mpr hlr)) hlr
    have hbound : ∀ x ∈ Ι l r, ‖f (P.tag i)-f x‖ ≤ f r-f l := by
      rw [uIoc_of_le hlr]
      intro x hx
      have htx := P.tag_mem i
      have hxx : x ∈ Icc l r := Ioc_subset_Icc_self hx
      rw [Real.norm_eq_abs, abs_le]
      have hleft (y : ℝ) (hy : y ∈ Icc l r) : f l ≤ f y :=
        hf (hsub (left_mem_Icc.mpr hlr)) (hsub hy) hy.1
      have hright (y : ℝ) (hy : y ∈ Icc l r) : f y ≤ f r :=
        hf (hsub hy) (hsub (right_mem_Icc.mpr hlr)) hy.2
      exact ⟨by linarith [hleft _ htx, hright _ hxx], by linarith [hright _ htx, hleft _ hxx]⟩
    change |f (P.tag i)*(r-l) - (A r-A l)| ≤ _
    rw [hA, mul_comm (f (P.tag i)), ← integral_constant,
      ← intervalIntegral.integral_sub intervalIntegrable_const hi]
    refine (by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlr), mul_comm] using
        intervalIntegral.norm_integral_le_of_norm_le_const hbound :
      _ ≤ (f r-f l)*(r-l)).trans ?_
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' P.width (Finset.mem_univ i))
      (sub_nonneg.mpr hfl)
  have hA := sum_endpoint_differences (A ∘ P.points)
  simp only [Function.comp_apply, P.first, P.last, A, intervalIntegral.integral_same,
    sub_zero] at hA
  change |P.riemannSum f - (∫ x in a..b, f x)| < ε
  rw [← hA, TaggedPartition.riemannSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |f (P.tag i)*P.width i - (A (P.points i.succ)-A (P.points i.castSucc))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (f (P.points i.succ)-f (P.points i.castSucc))*P.mesh :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = (f b-f a)*P.mesh := by
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Function.comp_apply, P.first, P.last] using sum_endpoint_differences (f ∘ P.points)
    _ ≤ (f b-f a)*δ := mul_le_mul_of_nonneg_left hP.le hvar
    _ < ε := by
      have hδeq : δ*(f b-f a+1) = ε := div_mul_cancel₀ _ (by linarith)
      linarith

theorem antitone_tagged_integral {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hf : AntitoneOn f (Icc a b)) :
    HasTaggedIntegral f a b (∫ x in a..b, f x) := by
  have hm : MonotoneOn (fun x => -f x) (Icc a b) :=
    fun _ hx _ hy hxy => neg_le_neg (hf hx hy hxy)
  have h := monotone_tagged_integral hab hm
  simpa [intervalIntegral.integral_neg] using
    tagged_integral_linear h (tagged_constant_integral (a := a) (b := b) 0) (-1) 0

end Ch09
