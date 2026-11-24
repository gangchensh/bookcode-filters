import Textbook.Ch13.LaminaEstimates
import Textbook.Ch13.SimpleRegions

namespace Ch13

open MeasureTheory Set
open scoped Interval

theorem triangular_lamina_error (ρ : ℝ × ℝ → ℝ)
    (hρ : IntegrableOn ρ unitTriangle)
    (hx : IntegrableOn (fun p => p.1 * ρ p) unitTriangle)
    (hy : IntegrableOn (fun p => p.2 * ρ p) unitTriangle)
    (h : ∀ p ∈ unitTriangle, |ρ p - 2*p.1| ≤ 1/100) :
    197/600 ≤ laminaMass unitTriangle ρ ∧
      |(laminaCentroid unitTriangle ρ).1 - 1/2| ≤ 9/394 ∧
      |(laminaCentroid unitTriangle ρ).2 - 1/4| ≤ 15/788 := by
  have hD : MeasurableSet unitTriangle :=
    (isClosed_le continuous_const continuous_fst).measurableSet.inter
      ((isClosed_le continuous_const continuous_snd).measurableSet.inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const).measurableSet)
  have coords (p : ℝ × ℝ) (hp : p ∈ unitTriangle) :
      (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1) := by
    rcases hp with ⟨h₁,h₂,h₃⟩
    exact ⟨⟨h₁,by linarith⟩,⟨h₂,by linarith⟩⟩
  have bridge (f : ℝ × ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
      (hb : ∀ p ∈ unitTriangle, |f p| ≤ M) {I : ℝ}
      (hi : HasRegionIntegral 0 1 0 1 unitTriangle f I) :
      IntegrableOn f unitTriangle ∧ (∫ p in unitTriangle, f p) = I := by
    rw [Measure.volume_eq_prod]
    exact tagged_region_measure_agreement zero_lt_one zero_lt_one unitTriangle hD f M hb hM hi
  have area := bridge (fun _ => 1) 1 zero_le_one (by simp) triangle_region_area
  have harea : volume.real unitTriangle = 1/2 := by
    simpa [setIntegral_const] using area.2
  have hfinite : volume unitTriangle < ⊤ := by
    by_contra! hn
    have ht : volume unitTriangle = ⊤ := top_unique hn
    simp [Measure.real_def, ht] at harea
  have mass := (triangle_region_both_orders (fun p => 2*p.1) (by fun_prop)).1
  have mx := (triangle_region_both_orders (fun p => p.1*(2*p.1)) (by fun_prop)).1
  have my := (triangle_region_both_orders (fun p => p.2*(2*p.1)) (by fun_prop)).1
  rw [triangle_mass] at mass
  rw [triangle_moment_x] at mx
  rw [triangle_moment_y] at my
  have eM := bridge _ 2 (by norm_num) (fun p hp => by
    have hp₀ := (coords p hp).1.1
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*p.1)]
    linarith [(coords p hp).1.2]) mass
  have eX := bridge _ 2 (by norm_num) (fun p hp => by
    have hp' := (coords p hp).1
    have hp₀ := hp'.1
    rw [abs_of_nonneg (by positivity : 0 ≤ p.1*(2*p.1))]
    exact (mul_le_mul_of_nonneg_right hp'.2 (by positivity)).trans (by linarith)) mx
  have eY := bridge _ 2 (by norm_num) (fun p hp => by
    have hp' := coords p hp
    have hp₁ := hp'.1.1
    have hp₂ := hp'.2.1
    rw [abs_of_nonneg (by positivity : 0 ≤ p.2*(2*p.1))]
    exact (mul_le_mul_of_nonneg_right hp'.2.2 (by positivity)).trans (by linarith [hp'.1.2])) my
  have dM := density_error unitTriangle (fun p => 2*p.1) ρ (1/100) hfinite eM.1 hρ h
  have weighted (k : ℝ × ℝ → ℝ) (hk : ∀ p ∈ unitTriangle, 0 ≤ k p ∧ k p ≤ 1)
      (p : ℝ × ℝ) (hp : p ∈ unitTriangle) : |k p * ρ p - k p * (2*p.1)| ≤ 1/100 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (hk p hp).1]
    exact (mul_le_mul_of_nonneg_right (hk p hp).2 (abs_nonneg _)).trans (by simpa using h p hp)
  have dX := density_error unitTriangle (fun p => p.1*(2*p.1)) (fun p => p.1*ρ p)
    (1/100) hfinite eX.1 hx (weighted Prod.fst (fun p hp => (coords p hp).1))
  have dY := density_error unitTriangle (fun p => p.2*(2*p.1)) (fun p => p.2*ρ p)
    (1/100) hfinite eY.1 hy (weighted Prod.snd (fun p hp => (coords p hp).2))
  unfold laminaMass at dM dX dY
  rw [eM.2, harea] at dM
  rw [eX.2, harea] at dX
  rw [eY.2, harea] at dY
  norm_num at dM dX dY
  exact triangular_centroid_error_bounds _ _ _ dM dX dY

end Ch13
