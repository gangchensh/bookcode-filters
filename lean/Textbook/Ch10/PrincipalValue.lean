import Textbook.Ch10.Audit

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem inverse_singular_truncations {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in (-1:ℝ)..(-α), 1/x) = Real.log α ∧
      (∫ x in β..(1:ℝ), 1/x) = -Real.log β := by
  constructor
  · rw [integral_one_div_of_neg (by norm_num) (neg_lt_zero.mpr hα)]
    congr 1
    ring
  · rw [integral_one_div_of_pos hβ zero_lt_one,one_div,Real.log_inv]

theorem inverse_singular_principal_value :
    (∀ ε > 0, (∫ x in (-1:ℝ)..(-ε), 1/x) + (∫ x in ε..(1:ℝ), 1/x) = 0) ∧
      Tendsto (fun ε : ℝ => ∫ x in (-1:ℝ)..(-ε), 1/x) (𝓝[>] 0) atBot ∧
      Tendsto (fun ε : ℝ => ∫ x in ε..(1:ℝ), 1/x) (𝓝[>] 0) atTop := by
  refine ⟨fun ε hε => ?_, ?_, ?_⟩
  · rw [(inverse_singular_truncations hε hε).1,(inverse_singular_truncations hε hε).2,add_neg_cancel]
  · apply Real.tendsto_log_nhdsGT_zero.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (inverse_singular_truncations hε hε).1.symm
  · apply (tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (inverse_singular_truncations hε hε).2.symm

theorem inverse_asymmetric_cutoffs {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ x in (-1:ℝ)..(-α), 1/x) + (∫ x in β..(1:ℝ), 1/x) = Real.log (α/β) := by
  rw [(inverse_singular_truncations hα hβ).1,(inverse_singular_truncations hα hβ).2,
    Real.log_div hα.ne' hβ.ne',sub_eq_add_neg]

theorem square_substitution_not_injective_across_zero :
    ¬ InjOn (fun x : ℝ => x^2) (Icc (-1:ℝ) 1) ∧
      HasDerivAt (fun x : ℝ => x^2) 0 0 := by
  refine ⟨fun h => ?_,?_⟩
  · have he := h (by norm_num : (-1:ℝ) ∈ Icc (-1:ℝ) 1)
      (by norm_num : (1:ℝ) ∈ Icc (-1:ℝ) 1) (by norm_num)
    norm_num at he
  · simpa using (hasDerivAt_id' (0:ℝ)).fun_pow 2

end Ch10
