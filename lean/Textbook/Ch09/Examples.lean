import Textbook.Ch09.Consequences
import Textbook.Ch09.FiniteChange
import Textbook.Ch09.Monotone

namespace Ch09

open MeasureTheory Set
open scoped Interval

theorem variable_upper_endpoint {f u : ℝ → ℝ} {a x d : ℝ}
    (hf : Continuous f) (hu : HasDerivAt u d x) :
    HasDerivAt (fun y => ∫ t in a..(u y), f t) (f (u x)*d) x :=
  (accumulation_derivative f hf a (u x)).comp x hu

theorem linear_accumulation (x : ℝ) :
    (∫ t in (0:ℝ)..x, (2*t+1)) = x^2+x ∧
      HasDerivAt (fun y => ∫ t in (0:ℝ)..y, (2*t+1)) (2*x+1) x := by
  refine ⟨?_, accumulation_derivative _ (by fun_prop) _ _⟩
  have hd (t : ℝ) : HasDerivAt (fun z => z^2+z) (2*t+1) t := by
    convert ((hasDerivAt_id' t).fun_pow 2).add (hasDerivAt_id' t) using 1
    norm_num
  have hi : IntervalIntegrable (fun t : ℝ => 2*t+1) volume 0 x :=
    (by fun_prop : Continuous (fun t : ℝ => 2*t+1)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  norm_num

theorem moving_square_interval (x : ℝ) :
    HasDerivAt (fun y => ∫ t in y..(y^2), t^2) (2*x^5-x^2) x := by
  have he (y : ℝ) : (∫ t in y..(y^2), t^2) = y^6/3-y^3/3 := by
    rw [integral_pow]
    push_cast
    ring
  simp_rw [he]
  convert (((hasDerivAt_id' x).pow 6).div_const 3).sub
    (((hasDerivAt_id' x).pow 3).div_const 3) using 1
  norm_num
  ring

theorem spring_work (k L : ℝ) :
    (∫ x in (0:ℝ)..L, k*x) = k*L^2/2 ∧
      (∫ x in L..(0:ℝ), k*x) = -(k*L^2/2) := by
  have h : (∫ x in (0:ℝ)..L, k*x) = k*L^2/2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  exact ⟨h, by rw [intervalIntegral.integral_symm 0 L, h]⟩

theorem linear_density_mass (L ρ α : ℝ) (hL : 0 < L) :
    (∫ x in (0:ℝ)..L, ρ*(1+α*x/L)) = ρ*L*(1+α/2) := by
  have he (x : ℝ) : ρ*(1+α*x/L) = ρ + (ρ*α/L)*x := by ring
  simp_rw [he]
  have hi : IntervalIntegrable (fun x : ℝ => (ρ*α/L)*x) volume 0 L :=
    (by fun_prop : Continuous (fun x : ℝ => (ρ*α/L)*x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const hi, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, smul_eq_mul, zero_pow (by decide : 2 ≠ 0)]
  field_simp

end Ch09
