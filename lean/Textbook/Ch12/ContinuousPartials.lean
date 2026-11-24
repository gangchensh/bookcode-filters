import Textbook.Ch12.Audit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace Ch12

open Set

private theorem abs_le_of_mem_uIcc_zero {u t : ℝ} (ht : t ∈ uIcc 0 u) :
    |t| ≤ |u| := by
  apply abs_le.mpr
  exact uIcc_subset_Icc (by simp [abs_nonneg u])
    ⟨neg_abs_le u, le_abs_self u⟩ ht

theorem continuous_partials_total {f p q : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {a : ℝ × ℝ} (hU : IsOpen U) (ha : a ∈ U)
    (hp : ∀ z ∈ U, HasDerivAt (fun x => f (x,z.2)) (p z) z.1)
    (hq : ∀ z ∈ U, HasDerivAt (fun y => f (z.1,y)) (q z) z.2)
    (hcp : ContinuousAt p a) (hcq : ContinuousAt q a) :
    HasBookTotalDerivative f a (linearModel (p a) (q a)) := by
  apply (total_remainder _ _ _).2
  intro ε hε
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU a ha
  obtain ⟨rp,hrp,hpδ⟩ := Metric.continuousAt_iff.mp hcp (ε/2) (by positivity)
  obtain ⟨rq,hrq,hqδ⟩ := Metric.continuousAt_iff.mp hcq (ε/2) (by positivity)
  refine ⟨min r (min rp rq), lt_min hr (lt_min hrp hrq), fun h hh => ?_⟩
  have hbound₁ : |h.1| ≤ ‖h‖ := by rw [Prod.norm_def,Real.norm_eq_abs]; exact le_max_left _ _
  have hbound₂ : |h.2| ≤ ‖h‖ := by rw [Prod.norm_def,Real.norm_eq_abs]; exact le_max_right _ _
  have near (u v : ℝ) (hu : |u| ≤ ‖h‖) (hv : |v| ≤ ‖h‖) :
      dist (a.1+u,a.2+v) a < min r (min rp rq) := by
    rw [dist_eq_norm,Prod.norm_def]
    change max ‖a.1+u-a.1‖ ‖a.2+v-a.2‖ < _
    simpa only [add_sub_cancel_left,Real.norm_eq_abs] using (max_le hu hv).trans_lt hh
  let H := fun t : ℝ => f (a.1+t,a.2+h.2) - p a*t
  let V := fun t : ℝ => f (a.1,a.2+t) - q a*t
  have dh (t : ℝ) (ht : t ∈ uIcc 0 h.1) :
      HasDerivAt H (p (a.1+t,a.2+h.2)-p a) t := by
    have hn := near t h.2 ((abs_le_of_mem_uIcc_zero ht).trans hbound₁) hbound₂
    have hz := hball (show (a.1+t,a.2+h.2) ∈ Metric.ball a r from hn.trans_le (min_le_left _ _))
    have hcomp : HasDerivAt (fun s => f (a.1+s,a.2+h.2)) (p (a.1+t,a.2+h.2)) t :=
      HasDerivAt.comp_const_add a.1 t (hp _ hz)
    have hlin : HasDerivAt (fun s => p a*s) (p a) t := by
      simpa using (hasDerivAt_id' t).const_mul (p a)
    exact hcomp.fun_sub hlin
  have dv (t : ℝ) (ht : t ∈ uIcc 0 h.2) :
      HasDerivAt V (q (a.1,a.2+t)-q a) t := by
    have hn := near 0 t (by simp) ((abs_le_of_mem_uIcc_zero ht).trans hbound₂)
    simp only [add_zero] at hn
    have hz := hball (show (a.1,a.2+t) ∈ Metric.ball a r from hn.trans_le (min_le_left _ _))
    have hcomp : HasDerivAt (fun s => f (a.1,a.2+s)) (q (a.1,a.2+t)) t :=
      HasDerivAt.comp_const_add a.2 t (hq _ hz)
    have hlin : HasDerivAt (fun s => q a*s) (q a) t := by
      simpa using (hasDerivAt_id' t).const_mul (q a)
    exact hcomp.fun_sub hlin
  have bh : ‖H h.1-H 0‖ ≤ ε/2*‖h.1-0‖ :=
    (convex_uIcc 0 h.1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (dh t ht).hasDerivWithinAt) (fun t ht => by
        rw [← dist_eq_norm]
        exact (hpδ ((near t h.2 ((abs_le_of_mem_uIcc_zero ht).trans hbound₁) hbound₂).trans_le
          ((min_le_right _ _).trans (min_le_left _ _)))).le) left_mem_uIcc right_mem_uIcc
  have bv : ‖V h.2-V 0‖ ≤ ε/2*‖h.2-0‖ :=
    (convex_uIcc 0 h.2).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (dv t ht).hasDerivWithinAt) (fun t ht => by
        rw [← dist_eq_norm]
        have hn := near 0 t (by simp) ((abs_le_of_mem_uIcc_zero ht).trans hbound₂)
        simp only [add_zero] at hn
        exact (hqδ (hn.trans_le ((min_le_right _ _).trans (min_le_right _ _)))).le)
      left_mem_uIcc right_mem_uIcc
  have he : f (a+h)-f a-linearModel (p a) (q a) h =
      (H h.1-H 0)+(V h.2-V 0) := by
    rcases a with ⟨a₁,a₂⟩
    rcases h with ⟨h₁,h₂⟩
    simp [H,V,linearModel_apply,Prod.mk_add_mk]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [sub_zero,Real.norm_eq_abs] at bh bv
  calc
    _ ≤ ε/2*|h.1|+ε/2*|h.2| := add_le_add bh bv
    _ ≤ ε*‖h‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hbound₁ (show 0 ≤ ε/2 by positivity),
        mul_le_mul_of_nonneg_left hbound₂ (show 0 ≤ ε/2 by positivity)]

end Ch12
