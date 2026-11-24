import Textbook.Ch13.CurveGeometry

namespace Ch13

open scoped Interval

noncomputable def helix (R c t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![R * Real.cos t, R * Real.sin t, c*t]

noncomputable def helixVelocity (R c t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![-R * Real.sin t, R * Real.cos t, c]

theorem helix_hasDerivAt (R c t : ℝ) : HasDerivAt (helix R c) (helixVelocity R c t) t := by
  have h : HasDerivAt (fun s => (![R * Real.cos s, R * Real.sin s, c*s] : Fin 3 → ℝ))
      ![-R * Real.sin t, R * Real.cos t, c] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [mul_neg, neg_mul] using (Real.hasDerivAt_cos t).const_mul R
    · simpa using (Real.hasDerivAt_sin t).const_mul R
    · simpa using (hasDerivAt_id t).const_mul c
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h

theorem helix_speed (R c t : ℝ) : ‖helixVelocity R c t‖ = Real.sqrt (R^2 + c^2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_three]
  change ‖-R * Real.sin t‖^2 + ‖R * Real.cos t‖^2 + ‖c‖^2 = _
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [congrArg (fun x : ℝ => R^2*x) (Real.sin_sq_add_cos_sq t)]

theorem helix_length (R c : ℝ) :
    HasPolygonalLength (Ch09.TaggedPartition.mesh (a := 0) (b := 2*Real.pi))
      (polygonalSum (helix R c)) (2*Real.pi*Real.sqrt (R^2+c^2)) := by
  have hv : Continuous (helixVelocity R c) := by
    unfold helixVelocity
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.mul Real.continuous_sin
    · exact continuous_const.mul Real.continuous_cos
    · exact continuous_const
  have hg : Continuous (helix R c) :=
    continuous_iff_continuousAt.mpr fun t => (helix_hasDerivAt R c t).continuousAt
  have h := length_of_continuous_velocity (helix R c) (helixVelocity R c)
    (a := 0) (b := 2*Real.pi) (by positivity) hv.continuousOn hg.continuousOn
    (fun t _ => helix_hasDerivAt R c t)
  simpa only [helix_speed, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

end Ch13
