import Textbook.Ch09.Tagged

namespace Ch09

open MeasureTheory Set
open scoped Interval

theorem lipschitz_tagged_sum_error {a b K : ℝ} (hK : 0 ≤ K)
    (f : ℝ → ℝ)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x-f y| ≤ K*|x-y|)
    (P : TaggedPartition a b) :
    |P.riemannSum f - (∫ x in a..b, f x)| ≤ K*P.mesh*(b-a) := by
  have hLip' : LipschitzOnWith ⟨K,hK⟩ f (Icc a b) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [Real.dist_eq, Real.dist_eq]
      change |f x-f y| ≤ K*|x-y|
      exact hLip x hx y hy
  have hf := hLip'.continuousOn
  let A (t : ℝ) := ∫ x in a..t, f x
  have hcell (i : Fin (P.n+1)) :
      |f (P.tag i)*P.width i-(A (P.points i.succ)-A (P.points i.castSucc))| ≤
        (K*P.mesh)*P.width i := by
    let l := P.points i.castSucc
    let r := P.points i.succ
    have hlr : l ≤ r := (P.increasing (Fin.castSucc_lt_succ (i := i))).le
    have hsub : Icc l r ⊆ Icc a b := P.subinterval_subset i
    have hi : IntervalIntegrable f volume l r := (hf.mono hsub).intervalIntegrable_of_Icc hlr
    have hl : l ∈ Icc a b := hsub (left_mem_Icc.mpr hlr)
    have hA : A r-A l = ∫ x in l..r, f x := by
      have he := intervalIntegral.integral_add_adjacent_intervals
        ((hf.mono (Icc_subset_Icc_right hl.2)).intervalIntegrable_of_Icc hl.1) hi
      dsimp [A]
      linarith
    have hb : ∀ x ∈ Ι l r, ‖f (P.tag i)-f x‖ ≤ K*P.mesh := by
      rw [uIoc_of_le hlr]
      intro x hx
      have ht := P.tag_mem i
      have hx' : x ∈ Icc l r := Ioc_subset_Icc_self hx
      have hd : |P.tag i - x| ≤ r-l := by
        rw [abs_le]
        exact ⟨by linarith [ht.1,hx'.2],by linarith [ht.2,hx'.1]⟩
      rw [Real.norm_eq_abs]
      exact (hLip _ (hsub ht) _ (hsub hx')).trans (mul_le_mul_of_nonneg_left
        (hd.trans (Finset.le_sup' P.width (Finset.mem_univ i))) hK)
    change |f (P.tag i)*(r-l)-(A r-A l)| ≤ (K*P.mesh)*(r-l)
    rw [hA,mul_comm (f (P.tag i)),← integral_constant,
      ← intervalIntegral.integral_sub intervalIntegrable_const hi]
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlr), mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have ht := sum_endpoint_differences (A ∘ P.points)
  simp only [Function.comp_apply,P.first,P.last,A,intervalIntegral.integral_same,sub_zero] at ht
  have hw : ∑ i, P.width i = b-a := by
    unfold TaggedPartition.width
    rw [sum_endpoint_differences,P.first,P.last]
  rw [← ht, TaggedPartition.riemannSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |f (P.tag i)*P.width i-(A (P.points i.succ)-A (P.points i.castSucc))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (K*P.mesh)*P.width i := Finset.sum_le_sum fun i _ => hcell i
    _ = _ := by rw [← Finset.mul_sum,hw]

theorem square_sampling_budget {T σ η : ℝ} (hT : 0 < T) (P : TaggedPartition 0 T)
    (data : Fin (P.n+1) → ℝ) (hdata : ∀ i, |data i - (P.tag i)^2| ≤ σ)
    (hmesh : P.mesh ≤ (η-σ*T)/(2*T^2)) :
    |(∑ i, data i*P.width i) - (∫ x in (0:ℝ)..T, x^2)| ≤ η := by
  have hl (x : ℝ) (hx : x ∈ Icc 0 T) (y : ℝ) (hy : y ∈ Icc 0 T) :
      |x^2-y^2| ≤ (2*T)*|x-y| := by
    rw [show x^2-y^2 = (x-y)*(x+y) by ring, abs_mul, abs_of_nonneg (add_nonneg hx.1 hy.1)]
    rw [mul_comm (2*T)]
    exact mul_le_mul_of_nonneg_left (by linarith [hx.2,hy.2]) (abs_nonneg _)
  have hq := lipschitz_tagged_sum_error (by positivity : 0 ≤ 2*T)
    (fun x => x^2) hl P
  have hw : ∑ i, P.width i = T := by
    unfold TaggedPartition.width
    rw [sum_endpoint_differences,P.first,P.last,sub_zero]
  have hd : |(∑ i, data i * P.width i) - P.riemannSum (fun x => x^2)| ≤ σ*T := by
    rw [TaggedPartition.riemannSum,← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    calc
      _ ≤ ∑ i, |(data i-(P.tag i)^2)*P.width i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, σ*P.width i := by
        apply Finset.sum_le_sum
        intro i _
        have hn : 0 ≤ P.width i :=
          sub_nonneg.mpr (P.increasing (Fin.castSucc_lt_succ (i := i))).le
        rw [abs_mul,abs_of_nonneg hn]
        exact mul_le_mul_of_nonneg_right (hdata i) hn
      _ = σ*T := by rw [← Finset.mul_sum,hw]
  have hm := (le_div_iff₀ (by positivity : 0 < 2*T^2)).mp hmesh
  have he := (abs_sub_le _ (P.riemannSum fun x => x^2) _).trans (add_le_add hd hq)
  refine he.trans ?_
  calc
    _ = P.mesh*(2*T^2) + σ*T := by ring
    _ ≤ η := by linarith

theorem square_uniform_sampling_budget {T σ η : ℝ} (hT : 0 < T) (n : ℕ)
    (hbudget : σ*T < η) (hcount : 2*T^3/(η-σ*T) ≤ (n:ℝ)+1)
    (data : Fin (n+1) → ℝ)
    (hdata : ∀ i, |data i - ((uniformPartition hT n).tag i)^2| ≤ σ) :
    |(∑ i, data i*(uniformPartition hT n).width i) -
        (∫ x in (0:ℝ)..T, x^2)| ≤ η := by
  apply square_sampling_budget hT (uniformPartition hT n) data hdata
  rw [uniform_mesh,sub_zero]
  apply (div_le_div_iff₀ (by positivity : 0 < (n:ℝ)+1)
    (by positivity : 0 < 2*T^2)).2
  have he := (div_le_iff₀ (sub_pos.mpr hbudget)).mp hcount
  nlinarith

end Ch09
