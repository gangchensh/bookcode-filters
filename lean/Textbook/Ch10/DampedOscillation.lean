import Textbook.Ch10.LimitExchange

namespace Ch10

open Filter MeasureTheory Set
open scoped Topology Interval

theorem damped_truncations (ω T : ℝ) :
    (∫ x in (0:ℝ)..T, Real.exp (-x)*Real.cos (ω*x)) =
        (1+Real.exp (-T)*(-Real.cos (ω*T)+ω*Real.sin (ω*T)))/(1+ω^2) ∧
    (∫ x in (0:ℝ)..T, Real.exp (-x)*Real.sin (ω*x)) =
        (ω+Real.exp (-T)*(-Real.sin (ω*T)-ω*Real.cos (ω*T)))/(1+ω^2) := by
  have he (x : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-x)) x := by
    simpa only [id_eq,Pi.neg_apply,neg_one_mul,mul_neg,mul_one,neg_neg] using
      ((hasDerivAt_id x).neg.exp).fun_neg
  have hl (x : ℝ) : HasDerivAt (fun t : ℝ => ω*t) ω x := by
    simpa using (hasDerivAt_id x).const_mul ω
  have hc := integration_by_parts
    (u := fun x => Real.cos (ω*x)) (v := fun x => -Real.exp (-x))
    (u' := fun x => -Real.sin (ω*x)*ω) (v' := fun x => Real.exp (-x))
    (a := 0) (b := T) (by fun_prop) (by fun_prop)
    (fun x _ => (hl x).cos) (fun x _ => he x)
    ((by fun_prop : Continuous (fun x : ℝ => -Real.sin (ω*x)*ω)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => Real.exp (-x))).intervalIntegrable _ _)
  have hs := integration_by_parts
    (u := fun x => Real.sin (ω*x)) (v := fun x => -Real.exp (-x))
    (u' := fun x => Real.cos (ω*x)*ω) (v' := fun x => Real.exp (-x))
    (a := 0) (b := T) (by fun_prop) (by fun_prop)
    (fun x _ => (hl x).sin) (fun x _ => he x)
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos (ω*x)*ω)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => Real.exp (-x))).intervalIntegrable _ _)
  have hc' : (∫ x in (0:ℝ)..T, Real.exp (-x)*Real.cos (ω*x)) =
      1-Real.exp (-T)*Real.cos (ω*T) -
        ω * ∫ x in (0:ℝ)..T, Real.exp (-x)*Real.sin (ω*x) := by
    rw [← intervalIntegral.integral_const_mul]
    simpa [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hc
  have hs' : (∫ x in (0:ℝ)..T, Real.exp (-x)*Real.sin (ω*x)) =
      -Real.exp (-T)*Real.sin (ω*T) +
        ω * ∫ x in (0:ℝ)..T, Real.exp (-x)*Real.cos (ω*x) := by
    rw [← intervalIntegral.integral_const_mul]
    simp only [mul_zero,Real.sin_zero,neg_zero,Real.exp_zero,zero_mul,sub_zero] at hs
    simp only [mul_neg,intervalIntegral.integral_neg,sub_neg_eq_add] at hs
    simpa [mul_comm, mul_left_comm, mul_assoc,neg_mul] using hs
  have hp : 0 < 1+ω^2 := by positivity
  constructor <;> apply (eq_div_iff hp.ne').2 <;> nlinarith [hc',hs',
    congrArg (ω*·) hc', congrArg (ω*·) hs']

private theorem damped_product_zero {f : ℝ → ℝ} {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    Tendsto (fun x => Real.exp (-x)*f x) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero (fun _ => abs_nonneg _) (fun x => ?_)
    (show Tendsto (fun x : ℝ => Real.exp (-x)*M) atTop (𝓝 0) by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const M)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb x) (Real.exp_pos _).le

theorem damped_oscillation (ω : ℝ) :
    ImproperRight (fun x => Real.exp (-x)*Real.cos (ω*x)) 0 (1/(1+ω^2)) ∧
    ImproperRight (fun x => Real.exp (-x)*Real.sin (ω*x)) 0 (ω/(1+ω^2)) ∧
    AbsolutelyImproperRight (fun x => Real.exp (-x)*Real.cos (ω*x)) 0 ∧
    AbsolutelyImproperRight (fun x => Real.exp (-x)*Real.sin (ω*x)) 0 := by
  have hci : LocallyIntervalIntegrable (fun x => Real.exp (-x)*Real.cos (ω*x)) 0 :=
    fun T _ => (by fun_prop : Continuous _).intervalIntegrable 0 T
  have hsi : LocallyIntervalIntegrable (fun x => Real.exp (-x)*Real.sin (ω*x)) 0 :=
    fun T _ => (by fun_prop : Continuous _).intervalIntegrable 0 T
  have hc := damped_product_zero (fun x => Real.abs_cos_le_one (ω*x))
  have hs := damped_product_zero (fun x => Real.abs_sin_le_one (ω*x))
  have hcb (x : ℝ) : |Real.exp (-x)*Real.cos (ω*x)| ≤ Real.exp (-x) := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (ω*x)) (Real.exp_pos _).le
  have hsb (x : ℝ) : |Real.exp (-x)*Real.sin (ω*x)| ≤ Real.exp (-x) := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (ω*x)) (Real.exp_pos _).le
  have hg : ImproperRight (fun x : ℝ => Real.exp (-x)) 0 1 :=
    by simpa using scaled_decay_improper (by norm_num : (0:ℝ) < 1) 1
  refine ⟨⟨hci,?_⟩,⟨hsi,?_⟩,(dominated_improper hci hg (fun x _ => hcb x)).1,
    (dominated_improper hsi hg (fun x _ => hsb x)).1⟩
  · have hl := (((hc.neg.add (hs.const_mul ω)).const_add 1).div_const (1+ω^2))
    simp only [mul_zero,neg_zero,add_zero] at hl
    apply hl.congr
    intro T
    rw [(damped_truncations ω T).1]
    ring
  · have hl := (((hs.neg.sub (hc.const_mul ω)).const_add ω).div_const (1+ω^2))
    simp only [mul_zero,neg_zero,sub_zero,add_zero] at hl
    apply hl.congr
    intro T
    rw [(damped_truncations ω T).2]
    ring

end Ch10
