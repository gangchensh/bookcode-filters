import Textbook.Ch12.Multivariable

namespace Ch12

open Filter Set
open scoped Topology

theorem compact_extrema {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} {f : E → ℝ}
    (hne : K.Nonempty) (hc : IsClosed K) (hb : Bornology.IsBounded K)
    (hf : ContinuousOn f K) :
    (∃ x ∈ K, IsMinOn f K x) ∧ (∃ y ∈ K, IsMaxOn f K y) ∧ UniformContinuousOn f K := by
  have hK := Metric.isCompact_of_isClosed_isBounded hc hb
  exact ⟨hK.exists_isMinOn hne hf, hK.exists_isMaxOn hne hf,
    hK.uniformContinuousOn_of_continuous hf⟩

section Linear

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem finite_dimensional_linear_bound [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] G) :
    ∃ C ≥ 0, ∀ h, ‖L h‖ ≤ C * ‖h‖ := by
  let A : E →L[ℝ] G := ⟨L, L.continuous_of_finiteDimensional⟩
  exact ⟨‖A‖, norm_nonneg _, A.le_opNorm⟩

theorem operator_norm_least (L : E →L[ℝ] G) :
    IsLeast {c | 0 ≤ c ∧ ∀ h, ‖L h‖ ≤ c * ‖h‖} ‖L‖ :=
  L.isLeast_opNorm

theorem general_linear_combination {f g : E → ℝ} {a : E}
    {L M : E →L[ℝ] ℝ} (hf : HasFDerivAt f L a)
    (hg : HasFDerivAt g M a) (c d : ℝ) :
    HasFDerivAt (fun x => c * f x + d * g x) (c • L + d • M) a :=
  (hf.const_mul c).add (hg.const_mul d)

theorem general_product_rule {f g : E → ℝ} {a : E}
    {L M : E →L[ℝ] ℝ} (hf : HasFDerivAt f L a)
    (hg : HasFDerivAt g M a) :
    HasFDerivAt (fun x => f x * g x) (f a • M + g a • L) a :=
  hf.mul hg

theorem local_extremum_derivative {f : E → ℝ} {a : E}
    {L : E →L[ℝ] ℝ} (hf : HasFDerivAt f L a) (h : IsLocalExtr f a) :
    L = 0 := by
  rw [← hf.fderiv]
  exact h.fderiv_eq_zero

theorem convex_mean_value {F : E → G} {U : Set E} {DF : E → E →L[ℝ] G}
    {M : ℝ} (hU : Convex ℝ U) (hF : ∀ z ∈ U, HasFDerivAt F (DF z) z)
    (hM : ∀ z ∈ U, ‖DF z‖ ≤ M) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖F y - F x‖ ≤ M * ‖y-x‖ :=
  hU.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hF z hz).hasFDerivWithinAt) hM hx hy

end Linear

end Ch12
