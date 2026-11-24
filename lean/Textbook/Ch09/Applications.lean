import Textbook.Ch09.Examples

namespace Ch09

open MeasureTheory Set
open scoped Interval

private theorem affine_integral (a b m c : ℝ) :
    (∫ x in a..b, m*x+c) = m*((b^2-a^2)/2)+c*(b-a) := by
  have h : IntervalIntegrable (fun x : ℝ => m*x) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ => m*x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem displacement_and_distance :
    (∫ t in (0:ℝ)..2, t-1) = 0 ∧ (∫ t in (0:ℝ)..2, |t-1|) = 1 := by
  constructor
  · convert affine_integral 0 2 1 (-1) using 1 <;> norm_num [sub_eq_add_neg]
  · have h (a b : ℝ) : IntervalIntegrable (fun t : ℝ => |t-1|) volume a b :=
      (by fun_prop : Continuous (fun t : ℝ => |t-1|)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (h 0 1) (h 1 2)]
    have hl : (∫ t in (0:ℝ)..1, |t-1|) = 1/2 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        (g := fun t => (-1:ℝ)*t+1) (fun t ht => by rw [abs_of_nonpos (sub_nonpos.mpr ht.2.le)]; ring),
        affine_integral]
      norm_num
    have hr : (∫ t in (1:ℝ)..2, |t-1|) = 1/2 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (1:ℝ) ≤ 2)
        (g := fun t => 1*t+(-1)) (fun t ht => by rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)]; ring),
        affine_integral]
      norm_num
    rw [hl,hr]
    norm_num

theorem linear_density_centroid (L ρ α : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hα : -1 ≤ α) :
    (∫ x in (0:ℝ)..L, x*(ρ*(1+α*x/L))) = ρ*L^2*(1/2+α/3) ∧
    (∫ x in (0:ℝ)..L, x*(ρ*(1+α*x/L))) /
      (∫ x in (0:ℝ)..L, ρ*(1+α*x/L)) = L*(1/2+α/3)/(1+α/2) := by
  have he (x : ℝ) : x*(ρ*(1+α*x/L)) = ρ*x+(ρ*α/L)*x^2 := by ring
  have hv : (∫ x in (0:ℝ)..L, x*(ρ*(1+α*x/L))) = ρ*L^2*(1/2+α/3) := by
    simp_rw [he]
    have h₁ : IntervalIntegrable (fun x : ℝ => ρ*x) volume 0 L :=
      (by fun_prop : Continuous (fun x : ℝ => ρ*x)).intervalIntegrable _ _
    have h₂ : IntervalIntegrable (fun x : ℝ => (ρ*α/L)*x^2) volume 0 L :=
      (by fun_prop : Continuous (fun x : ℝ => (ρ*α/L)*x^2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h₁ h₂, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
    field_simp
  refine ⟨hv,?_⟩
  rw [hv,linear_density_mass L ρ α hL]
  have hh : 0 < 1+α/2 := by linarith
  field_simp

end Ch09
