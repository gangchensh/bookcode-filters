import Textbook.Ch11.PowerOperations
import Textbook.Ch11.ApproximationExamples
import Textbook.Ch11.RadiusExamples

namespace Ch11

open Filter MeasureTheory Set
open scoped Topology Interval

theorem logarithm_series_by_integration {x : ℝ} (hx : |x| < 1) :
    (∫ t in (0:ℝ)..x, 1/(1-t)) = ∑' n : ℕ, x^(n+1)/(n+1:ℝ) := by
  have hr : ((|x-0|:ℝ):WithTop ℝ) < convergenceRadius (fun _ => 1) := by
    rw [geometric_radius]
    exact WithTop.coe_lt_coe.mpr (by simpa using hx)
  have h := (power_series_operations hr).2
  have hi : (∫ t in (0:ℝ)..x, ∑' n, powerSeriesTerm (fun _ => 1) 0 t n) =
      ∫ t in (0:ℝ)..x, 1/(1-t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hsub : uIcc (0:ℝ) x ⊆ Ioo (-1:ℝ) 1 :=
      (show OrdConnected (Ioo (-1:ℝ) 1) by infer_instance).uIcc_subset
        (by norm_num) (abs_lt.mp hx)
    have ht' : |t| < 1 := abs_lt.mpr (hsub ht)
    have hg := hasSum_geometric_of_norm_lt_one (show ‖t‖ < 1 by simpa [Real.norm_eq_abs] using ht')
    simpa only [powerSeriesTerm,sub_zero,one_mul,one_div] using hg.tsum_eq
  rw [hi] at h
  simp only [sub_zero,mul_comm] at h
  simpa only [one_div,div_eq_mul_inv,one_mul] using h

theorem logarithm_shifted_center {x : ℝ} (hx : |x-2| < 3) :
    SeriesHasSum (fun n : ℕ => (x-2)^(n+1)/((n+1:ℝ)*3^(n+1)))
      (-Real.log ((5-x)/3)) := by
  let y := (x-2)/3
  have hy : |y| < 1 := by
    dsimp [y]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 3)]
    exact (div_lt_one (by norm_num)).2 hx
  have h := logarithm_series hy
  have he : 1-y = (5-x)/3 := by dsimp [y]; ring
  rw [he] at h
  convert h using 1
  funext n
  dsimp [y]
  rw [div_pow,div_div,mul_comm ((3:ℝ)^(n+1))]

theorem logarithm_shifted_radius :
    convergenceRadius (fun n => 1/((n:ℝ)*3^n)) = (3:WithTop ℝ) := by
  simpa only [pow_one,WithTop.coe_ofNat] using polynomial_denominator_radius (R := 3) (by norm_num) 1

private theorem negative_alternating_harmonic :
    SeriesHasSum (fun n : ℕ => -((-1:ℝ)^n/(n+1:ℝ))) (-Real.log 2) := by
  have h := alternating_harmonic.1.neg
  change Tendsto (fun N => -(∑ n ∈ Finset.range N, (-1:ℝ)^n/(n+1:ℝ)))
    atTop (𝓝 (-Real.log 2)) at h
  change Tendsto (fun N => ∑ n ∈ Finset.range N, -((-1:ℝ)^n/(n+1:ℝ)))
    atTop (𝓝 (-Real.log 2))
  simpa only [Finset.sum_neg_distrib] using h

theorem logarithm_shifted_endpoints :
    SeriesHasSum (fun n : ℕ => ((-1:ℝ)-2)^(n+1)/((n+1:ℝ)*3^(n+1))) (-Real.log 2) ∧
    ¬ SeriesConverges (fun n : ℕ => ((5:ℝ)-2)^(n+1)/((n+1:ℝ)*3^(n+1))) := by
  have he : (fun n : ℕ => ((-1:ℝ)-2)^(n+1)/((n+1:ℝ)*3^(n+1))) =
      fun n : ℕ => -((-1:ℝ)^n/(n+1:ℝ)) := by
    funext n
    rw [show (-1:ℝ)-2 = (-1)*3 by norm_num,mul_pow,pow_succ (-1:ℝ)]
    field_simp
  have hf : (fun n : ℕ => ((5:ℝ)-2)^(n+1)/((n+1:ℝ)*3^(n+1))) =
      fun n : ℕ => 1/(n+1:ℝ) := by
    funext n
    norm_num only
    field_simp
  rw [he,hf]
  constructor
  · exact negative_alternating_harmonic
  · simpa only [Nat.cast_add,Nat.cast_one] using harmonic_counterexample.2

theorem three_unit_radius_examples :
    convergenceRadius (fun _ => 1) = (1:WithTop ℝ) ∧
    convergenceRadius (fun n => 1/(n:ℝ)) = (1:WithTop ℝ) ∧
    convergenceRadius (fun n => 1/(n:ℝ)^2) = (1:WithTop ℝ) ∧
    (∀ x : ℝ, |x| = 1 → ¬ SeriesConverges (fun n => x^n)) ∧
    (¬ SeriesConverges (fun n : ℕ => 1/(n+1:ℝ))) ∧
    SeriesHasSum (fun n : ℕ => (-1:ℝ)^(n+1)/(n+1:ℝ)) (-Real.log 2) ∧
    (∀ x : ℝ, |x| = 1 → AbsolutelyConvergent (fun n : ℕ => x^(n+1)/(n+1:ℝ)^2)) := by
  have ha : SeriesConverges (fun n : ℕ => 1/(n+1:ℝ)^2) := by
    simpa only [Nat.cast_add,Nat.cast_one,Real.rpow_two] using (p_series_criterion 2).2 (by norm_num)
  refine ⟨geometric_radius, ?_,?_,fun x hx => geometric_nonconvergence hx.ge,?_ ,?_,?_⟩
  · simpa only [pow_one,one_pow,mul_one,WithTop.coe_one] using
      polynomial_denominator_radius (R := 1) one_pos 1
  · simpa only [one_pow,mul_one,WithTop.coe_one] using polynomial_denominator_radius (R := 1) one_pos 2
  · simpa only [Nat.cast_add,Nat.cast_one] using harmonic_counterexample.2
  · simpa only [pow_succ (-1:ℝ),mul_neg,mul_one,neg_div] using negative_alternating_harmonic
  · intro x hx
    have he : (fun n : ℕ => |x^(n+1)/(n+1:ℝ)^2|) = fun n : ℕ => 1/(n+1:ℝ)^2 := by
      funext n
      rw [abs_div,abs_pow,hx,one_pow,abs_of_nonneg (sq_nonneg _)]
    unfold AbsolutelyConvergent
    rwa [he]

end Ch11
