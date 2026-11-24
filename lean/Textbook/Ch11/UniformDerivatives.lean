import Textbook.Ch11.Audit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

namespace Ch11

open Filter MeasureTheory Set
open scoped Topology Interval

theorem uniform_derivative_limit {F D : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {a b x₀ c : ℝ}
    (hab : a < b) (hx₀ : x₀ ∈ Icc a b)
    (hd : ∀ n x, x ∈ Ioo a b → HasDerivAt (F n) (D n x) x)
    (hF : ∀ n, ContinuousOn (F n) (Icc a b))
    (hD : ∀ n, ContinuousOn (D n) (Icc a b))
    (hu : TendstoUniformlyOn D g atTop (Icc a b))
    (hanchor : Tendsto (fun n => F n x₀) atTop (𝓝 c)) :
    TendstoUniformlyOn F (fun x => c + ∫ t in x₀..x, g t) atTop (Icc a b) ∧
    ∀ x ∈ Ioo a b, HasDerivAt (fun x => c + ∫ t in x₀..x, g t) (g x) x := by
  have hg : ContinuousOn g (Icc a b) :=
    hu.continuousOn (Eventually.of_forall hD).frequently
  have hidentity (n : ℕ) (x : ℝ) (hx : x ∈ Icc a b) :
      F n x = F n x₀ + ∫ t in x₀..x, D n t := by
    have localFTC (y z : ℝ) (hy : a ≤ y) (hz : z ≤ b) (hyz : y ≤ z) :
        (∫ t in y..z, D n t) = F n z - F n y := by
      have hsub : Icc y z ⊆ Icc a b := Icc_subset_Icc hy hz
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyz ((hF n).mono hsub)
        (fun t ht => hd n t ⟨hy.trans_lt ht.1,ht.2.trans_le hz⟩)
        (((hD n).mono hsub).intervalIntegrable_of_Icc hyz)
    rcases le_total x₀ x with h | h
    · rw [localFTC x₀ x hx₀.1 hx.2 h]
      ring
    · rw [intervalIntegral.integral_symm x x₀,localFTC x x₀ hx.1 hx₀.2 h]
      ring
  have hlimit : TendstoUniformlyOn F (fun x => c + ∫ t in x₀..x, g t) atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let η := ε/(2*(b-a+1))
    have hη : 0 < η := div_pos hε (by linarith)
    filter_upwards [(Metric.tendsto_nhds.mp hanchor) (ε/2) (by positivity),
      (Metric.tendstoUniformlyOn_iff.mp hu) η hη] with n hn hd' x hx
    have hsub : uIcc x₀ x ⊆ Icc a b := uIcc_subset_Icc hx₀ hx
    have hdi : IntervalIntegrable (D n) volume x₀ x := ((hD n).mono hsub).intervalIntegrable
    have hgi : IntervalIntegrable g volume x₀ x := (hg.mono hsub).intervalIntegrable
    have hbnd : ∀ t ∈ Ι x₀ x, ‖D n t-g t‖ ≤ η := by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (by simpa [Real.dist_eq, abs_sub_comm] using (hd' t (hsub (uIoc_subset_uIcc ht))).le)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [Real.norm_eq_abs,intervalIntegral.integral_sub hdi hgi] at hI
    have hwidth : |x-x₀| ≤ b-a := abs_le.mpr
      ⟨by linarith [hx.1,hx₀.2],by linarith [hx.2,hx₀.1]⟩
    have hmul : η*(2*(b-a+1)) = ε := div_mul_cancel₀ _ (by linarith)
    have hsmall := hI.trans (mul_le_mul_of_nonneg_left hwidth hη.le)
    have htail : |(∫ t in x₀..x, D n t)-(∫ t in x₀..x, g t)| < ε/2 := by
      nlinarith
    rw [Real.dist_eq] at hn ⊢
    rw [abs_sub_comm]
    rw [hidentity n x hx]
    rw [show F n x₀ + (∫ t in x₀..x, D n t) - (c + ∫ t in x₀..x, g t) =
      (F n x₀-c) + ((∫ t in x₀..x, D n t)-(∫ t in x₀..x, g t)) by ring]
    exact (abs_add_le _ _).trans_lt (by linarith)
  refine ⟨hlimit,fun x hx => ?_⟩
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hu.mono Ioo_subset_Icc_self)
    (Eventually.of_forall hd) (fun t ht => hlimit.tendsto_at (Ioo_subset_Icc_self ht)) hx

end Ch11
