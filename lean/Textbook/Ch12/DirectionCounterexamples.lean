import Textbook.Ch12.Audit

namespace Ch12

open Filter Set
open scoped Topology

noncomputable def cubicDirection (z : ℝ × ℝ) : ℝ := z.1^3/(z.1^2+z.2^2)
noncomputable def curvedRemainder (z : ℝ × ℝ) : ℝ := z.1^3*z.2/(z.1^4+z.2^2)

private theorem fst_abs_le (z : ℝ × ℝ) : |z.1| ≤ ‖z‖ := by
  simp only [Prod.norm_def,Real.norm_eq_abs]
  exact le_max_left _ _

private theorem continuous_from_bound {f : ℝ × ℝ → ℝ} (h0 : f 0 = 0)
    (hb : ∀ z, |f z| ≤ ‖z‖) : ContinuousAt f 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε,hε,fun z hz => ?_⟩
  rw [dist_zero_right] at hz
  rw [Real.dist_eq,h0,sub_zero]
  exact (hb z).trans_lt hz

theorem nonlinear_direction_example :
    ContinuousAt cubicDirection 0 ∧
    (∀ v : ℝ × ℝ, HasBookDirectionalDerivative cubicDirection 0 v (cubicDirection v)) ∧
    cubicDirection (1,0) = 1 ∧ cubicDirection (0,1) = 0 ∧ cubicDirection (1,1) = 1/2 := by
  have hzero : cubicDirection 0 = 0 := by simp [cubicDirection]
  refine ⟨continuous_from_bound hzero (fun z => ?_),fun v => ?_,by norm_num [cubicDirection],
    by norm_num [cubicDirection],by norm_num [cubicDirection]⟩
  · apply le_trans _ (fst_abs_le z)
    by_cases h : z.1^2+z.2^2 = 0
    · simp [cubicDirection,h]
    have hden : 0 < z.1^2+z.2^2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [cubicDirection,abs_div,abs_of_pos hden,abs_pow,div_le_iff₀ hden]
    have hh := mul_le_mul_of_nonneg_left
      (show z.1^2 ≤ z.1^2+z.2^2 by linarith [sq_nonneg z.2]) (abs_nonneg z.1)
    rw [pow_succ,sq_abs]
    nlinarith
  · apply (directional_epsilon _ _ _ _).2
    intro ε hε
    refine ⟨1,one_pos,fun t ht _ => ?_⟩
    have ht₀ : t ≠ 0 := abs_pos.mp ht
    have he : directionalQuotient cubicDirection 0 v t = cubicDirection v := by
      simp only [directionalQuotient,zero_add,hzero,sub_zero]
      change (t*v.1)^3/((t*v.1)^2+(t*v.2)^2)/t = v.1^3/(v.1^2+v.2^2)
      by_cases h : v.1^2+v.2^2 = 0
      · have h' : (t*v.1)^2+(t*v.2)^2 = 0 := by linear_combination t^2*h
        simp [h,h']
      have h' : (t*v.1)^2+(t*v.2)^2 ≠ 0 := by
        rw [show (t*v.1)^2+(t*v.2)^2 = t^2*(v.1^2+v.2^2) by ring]
        exact mul_ne_zero (pow_ne_zero _ ht₀) h
      field_simp
    simpa [he] using hε

private theorem curved_bound (z : ℝ × ℝ) : |curvedRemainder z| ≤ |z.1|/2 := by
  by_cases h : z.1^4+z.2^2 = 0
  · simp [curvedRemainder,h,div_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
  have hp : 0 < z.1^4+z.2^2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  have he : 2*(z.1^2*|z.2|) ≤ z.1^4+z.2^2 := by
    nlinarith [sq_nonneg (z.1^2-|z.2|),sq_abs z.2]
  rw [curvedRemainder,abs_div,abs_of_pos hp,abs_mul,abs_pow,div_le_iff₀ hp]
  have hm := mul_le_mul_of_nonneg_left he (abs_nonneg z.1)
  rw [pow_succ,sq_abs]
  nlinarith

theorem linear_directions_not_differentiable :
    ContinuousAt curvedRemainder 0 ∧
    (∀ v : ℝ × ℝ, HasBookDirectionalDerivative curvedRemainder 0 v 0) ∧
    ¬ DifferentiableAt ℝ curvedRemainder 0 := by
  have h0 : curvedRemainder 0 = 0 := by simp [curvedRemainder]
  have hc := continuous_from_bound h0 (fun z =>
    (curved_bound z).trans (by linarith [fst_abs_le z,abs_nonneg z.1]))
  have hd (v : ℝ × ℝ) : HasBookDirectionalDerivative curvedRemainder 0 v 0 := by
    by_cases hv : v.2 = 0
    · unfold HasBookDirectionalDerivative
      apply (tendsto_const_nhds (x := (0:ℝ))).congr
      intro t
      simp [directionalQuotient,h0,curvedRemainder,Prod.snd_smul,hv]
    have hfun : ContinuousAt (fun t : ℝ => t*v.1^3*v.2/(t^2*v.1^4+v.2^2)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num; positivity)
    unfold HasBookDirectionalDerivative
    have hl : Tendsto (fun t : ℝ => t*v.1^3*v.2/(t^2*v.1^4+v.2^2))
        (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have h := hfun.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
      change Tendsto _ _ (𝓝 ((0:ℝ)*v.1^3*v.2/(0^2*v.1^4+v.2^2))) at h
      simpa only [zero_mul,zero_div] using h
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht₀ : t ≠ 0 := ht
    have h₁ : 0 < (t*v.1)^4+(t*v.2)^2 := by positivity
    have h₂ : 0 < t^2*v.1^4+v.2^2 := by positivity
    simp only [directionalQuotient,zero_add,h0,sub_zero]
    change t*v.1^3*v.2/(t^2*v.1^4+v.2^2) =
      (t*v.1)^3*(t*v.2)/((t*v.1)^4+(t*v.2)^2)/t
    field_simp
  refine ⟨hc,hd,?_⟩
  rintro ⟨L,hL⟩
  have hL0 (v : ℝ × ℝ) : L v = 0 := by
    exact tendsto_nhds_unique (total_decides_direction hL v) (hd v)
  have hrem := (total_remainder _ _ _).1 ((total_native _ _ _).2 hL)
  obtain ⟨δ,hδ,hest⟩ := hrem (1/4) (by norm_num)
  let t := min δ 1 / 2
  have ht : 0 < t := div_pos (lt_min hδ one_pos) (by norm_num)
  have ht1 : t < 1 := by dsimp [t]; linarith [min_le_right δ (1:ℝ)]
  have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ (1:ℝ)]
  have hn : ‖(t,t^2)‖ = t := by
    change max |t| |t^2| = t
    rw [abs_of_pos ht,abs_of_nonneg (sq_nonneg t)]
    exact max_eq_left (by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1.le)])
  have hv : curvedRemainder (t,t^2) = t/2 := by
    unfold curvedRemainder
    have hpos : 0 < t^4+(t^2)^2 := by positivity
    field_simp
    ring
  have he := hest (t,t^2) (by rwa [hn])
  rw [zero_add,h0,hL0,sub_zero,sub_zero,hv,Real.norm_eq_abs,abs_of_pos (by positivity),hn] at he
  linarith

end Ch12
