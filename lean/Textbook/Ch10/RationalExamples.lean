import Textbook.Ch10.Comparison

namespace Ch10

open Filter MeasureTheory Set
open scoped Topology Interval

theorem partial_fractions {x : ℝ} (h₁ : x ≠ 1) (h₂ : x ≠ -1) :
    1/(x^2-1) = (1/2:ℝ)*(1/(x-1)-1/(x+1)) := by
  have hp : x^2-1 = (x-1)*(x+1) := by ring
  have hsub : x-1 ≠ 0 := sub_ne_zero.mpr h₁
  have hadd : x+1 ≠ 0 := by intro h; apply h₂; linarith
  rw [hp]
  field_simp
  ring

theorem partial_fractions_integral :
    (∫ x in (2:ℝ)..3, 1/(x^2-1)) = (1/2:ℝ)*Real.log (3/2) := by
  have hi (c : ℝ) (hc : c < 2) :
      IntervalIntegrable (fun x : ℝ => 1/(x-c)) volume 2 3 :=
    (continuousOn_const.div (by fun_prop) (fun x (hx : x ∈ Icc (2:ℝ) 3) =>
      (sub_pos.mpr (hc.trans_le hx.1)).ne')).intervalIntegrable_of_Icc (by norm_num)
  have hlog (c : ℝ) (hc : c < 2) :
      (∫ x in (2:ℝ)..3, 1/(x-c)) = Real.log (3-c) - Real.log (2-c) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => Real.log (x-c)) ?_ (hi c hc)
    intro x hx
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] at hx
    have hpos := (sub_pos.mpr (hc.trans_le hx.1)).ne'
    simpa only [id_eq,one_div,Function.comp_def,mul_one] using
      ((hasDerivAt_id x).sub_const c).log hpos
  calc
    _ = ∫ x in (2:ℝ)..3, (1/2:ℝ)*(1/(x-1)-1/(x-(-1))) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)]
      intro x hx
      simpa only [sub_neg_eq_add] using partial_fractions
        (by linarith [hx.1]) (by linarith [hx.1])
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hi 1 (by norm_num))
        (hi (-1) (by norm_num)),hlog 1 (by norm_num),hlog (-1) (by norm_num)]
      norm_num [Real.log_div,Real.log_one]
      rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
      ring

theorem rational_infinity_comparison :
    (∀ x ≥ (1:ℝ), 0 ≤ 1/(1+x^2) ∧ 1/(1+x^2) ≤ 1/x^2) ∧
      ImproperRight (fun x => 1/(1+x^2)) 1 (Real.pi/4) := by
  refine ⟨fun x hx => ⟨by positivity,one_div_le_one_div_of_le (by positivity) (by linarith)⟩,?_⟩
  have hi : Continuous (fun x : ℝ => 1/(1+x^2)) :=
    continuous_const.div (by fun_prop) (fun _ => by positivity)
  refine ⟨fun T _ => hi.intervalIntegrable 1 T,?_⟩
  have h := (Real.tendsto_arctan_atTop.mono_right
    (nhdsWithin_le_nhds : (𝓝[<] (Real.pi/2)) ≤ 𝓝 (Real.pi/2))).sub_const (Real.arctan 1)
  rw [Real.arctan_one] at h
  have hl : Real.pi/2-Real.pi/4 = Real.pi/4 := by ring
  rw [hl] at h
  apply h.congr
  intro T
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => Real.hasDerivAt_arctan x) (hi.intervalIntegrable 1 T), Real.arctan_one]

theorem rational_origin_comparison :
    (∀ x ∈ Ioc (0:ℝ) 1, 0 ≤ 1/(Real.sqrt x*(1+x)) ∧
      1/(Real.sqrt x*(1+x)) ≤ 1/Real.sqrt x) ∧
    ImproperEndpointLeft (fun x => 1/(Real.sqrt x*(1+x))) 0 1 (Real.pi/2) := by
  have hc : ContinuousOn (fun x : ℝ => 1/(Real.sqrt x*(1+x))) (Ioi 0) :=
    continuousOn_const.div (by fun_prop) (fun x hx => by
      have hx' : 0 < x := hx
      positivity)
  refine ⟨fun x hx => ⟨by have := hx.1; positivity,?_⟩,?_⟩
  · apply one_div_le_one_div_of_le (Real.sqrt_pos_of_pos hx.1)
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) hx.1.le]
  · refine ⟨fun c hc₀ hc₁ => (hc.mono (fun _ hx => hc₀.trans_le hx.1)).intervalIntegrable_of_Icc hc₁,?_⟩
    have hprim (c : ℝ) (hc₀ : 0 < c) (hc₁ : c ≤ 1) :
        (∫ x in c..(1:ℝ), 1/(Real.sqrt x*(1+x))) =
          2*Real.arctan (Real.sqrt 1)-2*Real.arctan (Real.sqrt c) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x => 2*Real.arctan (Real.sqrt x)) ?_
        ((hc.mono (fun _ hx => hc₀.trans_le hx.1)).intervalIntegrable_of_Icc hc₁)
      intro x hx
      rw [uIcc_of_le hc₁] at hx
      have hx₀ : 0 < x := hc₀.trans_le hx.1
      have h := ((Real.hasDerivAt_arctan (Real.sqrt x)).comp x (Real.hasDerivAt_sqrt hx₀.ne')).const_mul 2
      have he : 2 * (1/(1+(Real.sqrt x)^2) * (1/(2*Real.sqrt x))) =
          1/(Real.sqrt x*(1+x)) := by
        rw [Real.sq_sqrt hx₀.le]
        have hs := (Real.sqrt_pos_of_pos hx₀).ne'
        field_simp
      simpa only [Function.comp_def,he] using h
    have hcont : Continuous (fun x : ℝ => 2*Real.arctan (Real.sqrt x)) := by fun_prop
    have hl := (tendsto_const_nhds (x := 2*Real.arctan (Real.sqrt 1))).sub
      ((hcont.continuousAt (x := (0:ℝ))).continuousWithinAt (s := Ioi 0))
    have hl' : Tendsto (fun c : ℝ => 2*Real.arctan (Real.sqrt 1)-2*Real.arctan (Real.sqrt c))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.pi/2)) := by
      convert hl using 1
      simp [Real.arctan_one]
      ring
    apply hl'.congr'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with c hc
    exact (hprim c hc.1 hc.2.le).symm

end Ch10
