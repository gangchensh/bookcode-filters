import Textbook.Ch13.Bridges
import Textbook.Ch13.Applications
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace Ch13

open MeasureTheory Set
open scoped Interval

/-- A continuous extension of the interior derivative supplies the endpoint velocities. -/
def CurveVelocity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ v : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn γ (Icc a b) ∧ ContinuousOn v (Icc a b) ∧
    ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t

/-- At a break point the adjacent pieces may have different limiting velocities. -/
def PiecewiseCurveVelocity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (B : Ch09.TaggedPartition a b) (γ : ℝ → E)
    (v : Fin (B.n+1) → ℝ → E) : Prop :=
  ∀ i, CurveVelocity γ (v i) (B.points i.castSucc) (B.points i.succ)

noncomputable def curveSpeed {E : Type*} [NormedAddCommGroup E]
    (v : ℝ → E) (t : ℝ) : ℝ := ‖v t‖

/-- Apply the chain rule and the fundamental theorem on one smooth piece. -/
theorem gradient_work_piece {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) {γ v : ℝ → E} (hγ : CurveVelocity γ v a b)
    {U : E → ℝ} {F : E → E} (hU : Continuous U) (hF : Continuous F)
    (hgrad : ∀ t ∈ Ioo a b, HasGradientAt U (F (γ t)) (γ t)) :
    lineWork γ v F a b = U (γ b) - U (γ a) := by
  unfold lineWork
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := U ∘ γ) hab
  · exact hU.comp_continuousOn hγ.1
  · intro t ht
    simpa [InnerProductSpace.toDual_apply_apply] using
      (hgrad t ht).hasFDerivAt.comp_hasDerivAt t (hγ.2.2 t ht)
  · exact (hF.comp_continuousOn hγ.1 |>.inner hγ.2.1).intervalIntegrable_of_Icc hab

/-- The potential differences on consecutive pieces telescope. -/
theorem gradient_piecewise_work {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (B : Ch09.TaggedPartition a b) {γ : ℝ → E}
    {v : Fin (B.n+1) → ℝ → E} (hγ : PiecewiseCurveVelocity B γ v)
    {U : E → ℝ} {F : E → E} (hU : Continuous U) (hF : Continuous F)
    (hgrad : ∀ t ∈ Icc a b, HasGradientAt U (F (γ t)) (γ t)) :
    (∑ i, lineWork γ (v i) F (B.points i.castSucc) (B.points i.succ)) =
      U (γ b) - U (γ a) := by
  classical
  calc
    _ = ∑ i : Fin (B.n+1), ((U ∘ γ ∘ B.points) i.succ -
        (U ∘ γ ∘ B.points) i.castSucc) := by
      apply Finset.sum_congr rfl
      intro i _
      apply gradient_work_piece (B.increasing.monotone (Fin.castSucc_le_succ i)) (hγ i) hU hF
      intro t ht
      apply hgrad t
      have hl := B.increasing.monotone (Fin.zero_le i.castSucc)
      have hr := B.increasing.monotone (Fin.le_last i.succ)
      rw [B.first] at hl
      rw [B.last] at hr
      exact ⟨hl.trans ht.1.le,
        ht.2.le.trans hr⟩
    _ = _ := by simpa only [Function.comp_apply, B.first, B.last] using
      Ch09.sum_endpoint_differences (U ∘ γ ∘ B.points)

end Ch13
