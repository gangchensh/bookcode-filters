import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Textbook.Ch12.SensorBudget

namespace Ch12

open Set Filter
open scoped Topology

theorem two_output_composition (x y : ℝ) :
    sensor (x,y) = (x^2+y,x*y) ∧
    sensorCombination (x,y) = 3*(x^2+y)-x*y := ⟨by simp [sensor,pow_two],by simp [sensorCombination,sensor,pow_two]⟩

noncomputable def polarExample (z : ℝ × ℝ) : ℝ := z.1^2*z.2/(z.1^2+z.2^2)

theorem polar_example_formula {r θ : ℝ} (hr : 0 < r) :
    polarExample (r*Real.cos θ,r*Real.sin θ) = r*(Real.cos θ)^2*Real.sin θ ∧
    |polarExample (r*Real.cos θ,r*Real.sin θ)| ≤ r := by
  have he : (r*Real.cos θ)^2+(r*Real.sin θ)^2 = r^2 := by
    linear_combination r^2*Real.sin_sq_add_cos_sq θ
  have hv : polarExample (r*Real.cos θ,r*Real.sin θ) = r*(Real.cos θ)^2*Real.sin θ := by
    change (r*Real.cos θ)^2*(r*Real.sin θ)/((r*Real.cos θ)^2+(r*Real.sin θ)^2) = _
    rw [he]
    field_simp
  refine ⟨hv,?_⟩
  rw [hv,abs_mul,abs_mul,abs_of_pos hr,abs_of_nonneg (sq_nonneg (Real.cos θ))]
  have hc : (Real.cos θ)^2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg (Real.sin θ)]
  exact (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one θ)).trans
    (mul_le_of_le_one_right hr.le hc)

theorem polar_example_limit : HasMultivariableLimit polarExample 0 0 := by
  apply (punctured_limit_norm_iff _ _ _).2
  intro ε hε
  refine ⟨ε,hε,fun z hz => ?_⟩
  simp only [sub_zero,Real.norm_eq_abs] at hz ⊢
  have hb : |polarExample z| ≤ |z.2| := by
    by_cases h : z.1^2+z.2^2 = 0
    · simp [polarExample,h]
    have hp : 0 < z.1^2+z.2^2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [polarExample,abs_div,abs_mul,abs_of_nonneg (sq_nonneg z.1),abs_of_pos hp,div_le_iff₀ hp]
    nlinarith [mul_nonneg (sq_nonneg z.2) (abs_nonneg z.2)]
  have hn : |z.2| ≤ ‖z‖ := by
    simp only [Prod.norm_def,Real.norm_eq_abs]
    exact le_max_right _ _
  exact (hb.trans hn).trans_lt hz.2

noncomputable def elliptical (x : ℝ × ℝ) : ℝ := x.1^2+3*x.2^2

theorem ellipse_derivative (a : ℝ × ℝ) :
    HasFDerivAt elliptical (linearModel (2*a.1) (6*a.2)) a := by
  have hx : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) a :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hy : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) a :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have h := (hx.pow 2).add ((hy.pow 2).const_mul 3)
  have he : (fun x : ℝ × ℝ => x.1 ^ 2) + (fun x => 3*x.2^2) = elliptical := rfl
  rw [he] at h
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [linearModel_apply,smul_apply]
  ring

theorem ellipse_remainder (a h : ℝ × ℝ) :
    elliptical (a+h)-elliptical a-linearModel (2*a.1) (6*a.2) h = h.1^2+3*h.2^2 ∧
    0 ≤ h.1^2+3*h.2^2 ∧ h.1^2+3*h.2^2 ≤ 3*(h.1^2+h.2^2) ∧
    (h.1^2+h.2^2 ≤ (1/100:ℝ)^2 → h.1^2+3*h.2^2 ≤ 3/10000) := by
  refine ⟨?_,by positivity,by linarith [sq_nonneg h.1],fun hsmall => ?_⟩
  · rcases a with ⟨a₁,a₂⟩
    rcases h with ⟨h₁,h₂⟩
    simp [elliptical,linearModel_apply,Prod.mk_add_mk]
    ring
  · linarith [sq_nonneg h.1]

noncomputable def tangentHeight (f : (ℝ × ℝ) → ℝ) (a x : ℝ × ℝ) : ℝ :=
  f a + fderiv ℝ f a (x-a)

theorem tangent_plane_formula {f : (ℝ × ℝ) → ℝ} {a : ℝ × ℝ} {p q : ℝ}
    (hf : HasFDerivAt f (linearModel p q) a) (x : ℝ × ℝ) :
    tangentHeight f a x = f a+p*(x.1-a.1)+q*(x.2-a.2) := by
  rw [tangentHeight,hf.fderiv,linearModel_apply]
  rcases x with ⟨x₁,x₂⟩
  rcases a with ⟨a₁,a₂⟩
  change f (a₁,a₂)+(p*(x₁-a₁)+q*(x₂-a₂)) = _
  ring

noncomputable def temperature (x : ℝ × ℝ) : ℝ := 20+elliptical x

theorem temperature_direction :
    HasBookDirectionalDerivative temperature (1,1) (3/5,4/5) 6 ∧
    ∀ t : ℝ, temperature ((1,1)+t • (3/5,4/5)) - temperature (1,1) =
      6*t+57/25*t^2 := by
  have hd := (ellipse_derivative (1,1)).const_add (20:ℝ)
  have hv := total_decides_direction hd ((3/5:ℝ),(4/5:ℝ))
  refine ⟨?_,fun t => ?_⟩
  · have he : linearModel (2*(1:ℝ)) (6*(1:ℝ)) ((3/5:ℝ),(4/5:ℝ)) = 6 := by
      norm_num [linearModel_apply]
    change HasBookDirectionalDerivative (fun x => 20+elliptical x) (1,1) (3/5,4/5) 6
    simpa only [he] using hv
  · change 20+((1+t*(3/5))^2+3*(1+t*(4/5))^2)-(20+(1^2+3*1^2)) = _
    ring

noncomputable def polarCoordinates (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1*Real.cos z.2,z.1*Real.sin z.2)

theorem polar_jacobian (r θ : ℝ) :
    HasFDerivAt polarCoordinates
      ((linearModel (Real.cos θ) (-r*Real.sin θ)).prod
        (linearModel (Real.sin θ) (r*Real.cos θ))) (r,θ) ∧
    HasFDerivAt (elliptical ∘ polarCoordinates)
      (linearModel (2*r*(Real.cos θ)^2+6*r*(Real.sin θ)^2)
        (4*r^2*Real.sin θ*Real.cos θ)) (r,θ) := by
  have hx : HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (r,θ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hy : HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (r,θ) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hp : HasFDerivAt polarCoordinates
      ((linearModel (Real.cos θ) (-r*Real.sin θ)).prod
        (linearModel (Real.sin θ) (r*Real.cos θ))) (r,θ) := by
    have h := (hx.mul hy.cos).prodMk (hx.mul hy.sin)
    change HasFDerivAt (fun z : ℝ × ℝ => (z.1*Real.cos z.2,z.1*Real.sin z.2)) _ _
    convert h using 1
    all_goals first | rfl | (apply ContinuousLinearMap.ext; intro v; apply Prod.ext <;> simp [linearModel_apply,smul_apply] <;> ring)
  refine ⟨hp,?_⟩
  have h := (ellipse_derivative (polarCoordinates (r,θ))).comp (r,θ) hp
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [polarCoordinates,linearModel_apply]
  ring

theorem temperature_steepest :
    (∀ v : ℝ × ℝ, v.1^2+v.2^2 = 1 → 2*v.1+6*v.2 ≤ Real.sqrt 40) ∧
    let v : ℝ × ℝ := (1/Real.sqrt 10,3/Real.sqrt 10)
    v.1^2+v.2^2 = 1 ∧ 2*v.1+6*v.2 = Real.sqrt 40 := by
  have h10 : (Real.sqrt 10)^2 = 10 := Real.sq_sqrt (by norm_num)
  have h40 : (Real.sqrt 40)^2 = 40 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 10 := Real.sqrt_pos_of_pos (by norm_num)
  have he : Real.sqrt 40 = 2*Real.sqrt 10 := by
    have h₀ := Real.sqrt_nonneg 40
    nlinarith [sq_nonneg (Real.sqrt 40-2*Real.sqrt 10)]
  constructor
  · intro v hv
    have hq : (2*v.1+6*v.2)^2 ≤ 40 := by
      nlinarith [sq_nonneg (6*v.1-2*v.2)]
    nlinarith [Real.sqrt_nonneg 40]
  · dsimp
    constructor
    · field_simp [hs.ne']
      nlinarith
    · rw [he]
      field_simp [hs.ne']
      nlinarith

theorem polar_jacobian_geometry (r θ : ℝ) :
    Real.cos θ*(-r*Real.sin θ)+Real.sin θ*(r*Real.cos θ) = 0 ∧
    (Real.cos θ)^2+(Real.sin θ)^2 = 1 ∧
    (-r*Real.sin θ)^2+(r*Real.cos θ)^2 = r^2 := by
  refine ⟨by ring,by nlinarith [Real.sin_sq_add_cos_sq θ],?_⟩
  linear_combination r^2*Real.sin_sq_add_cos_sq θ

end Ch12
