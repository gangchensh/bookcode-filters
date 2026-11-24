import Textbook.Ch12.Audit
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

namespace Ch12

open Filter Set
open scoped Topology RealInnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_direction {f : E → ℝ} {a v : E} (hf : DifferentiableAt ℝ f a) :
    HasBookDirectionalDerivative f a v ⟪gradient f a,v⟫ := by
  rw [inner_gradient_left]
  exact total_decides_direction hf.hasFDerivAt v

theorem steepest_unit_direction {f : E → ℝ} {a : E}
    (hg : gradient f a ≠ 0) :
    (∀ v : E, ‖v‖ = 1 → |⟪gradient f a,v⟫| ≤ ‖gradient f a‖) ∧
    ∃ v : E, ‖v‖ = 1 ∧ ⟪gradient f a,v⟫ = ‖gradient f a‖ ∧
      ‖-v‖ = 1 ∧ ⟪gradient f a,-v⟫ = -‖gradient f a‖ := by
  let g := gradient f a
  have hp : 0 < ‖g‖ := norm_pos_iff.mpr hg
  refine ⟨fun v hv => by simpa only [hv,mul_one] using abs_real_inner_le_norm g v,
    ‖g‖⁻¹ • g, ?_,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp,inv_mul_cancel₀ hp.ne']
  · rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp <;> ring
  · rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp,inv_mul_cancel₀ hp.ne']
  · rw [inner_neg_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp <;> ring

theorem curve_derivative {f : (ℝ × ℝ) → ℝ} {x y : ℝ → ℝ} {t dx dy p q : ℝ}
    (hf : HasFDerivAt f (linearModel p q) (x t,y t))
    (hx : HasDerivAt x dx t) (hy : HasDerivAt y dy t) :
    HasDerivAt (fun s => f (x s,y s)) (p*dx+q*dy) t := by
  simpa only [linearModel_apply,Function.comp_def] using hf.comp_hasDerivAt t (hx.prodMk hy)

theorem level_curve_gradient {f : E → ℝ} {γ : ℝ → E} {t : ℝ} {v : E}
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : HasDerivAt γ v t)
    (hc : (fun s => f (γ s)) =ᶠ[𝓝 t] fun _ => f (γ t)) :
    ⟪gradient f (γ t),v⟫ = 0 := by
  rw [inner_gradient_left]
  have h := hf.hasFDerivAt.comp_hasDerivAt t hγ
  exact (h.congr_of_eventuallyEq hc.symm).unique (hasDerivAt_const t (f (γ t)))

theorem squared_distance_model (a : E) :
    HasFDerivAt (fun x : E => ‖x‖^2) (2 • innerSL ℝ a) a ∧
    ∀ h : E, ‖a+h‖^2-‖a‖^2 = 2*⟪a,h⟫+‖h‖^2 := by
  refine ⟨(hasStrictFDerivAt_norm_sq a).hasFDerivAt,fun h => ?_⟩
  simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right]
  rw [real_inner_comm a h]
  ring

noncomputable def radialOutput (x : E) : ℝ := Real.sqrt (1+‖x‖^2)

theorem radial_output_derivative (a : E) :
    HasFDerivAt radialOutput ((radialOutput a)⁻¹ • innerSL ℝ a) a := by
  have hp : 0 < 1+‖a‖^2 := by positivity
  have hd := ((squared_distance_model a).1.const_add (1:ℝ)).sqrt hp.ne'
  have he : (1/(2*Real.sqrt (1+‖a‖^2)) : ℝ) • (2 • innerSL ℝ a) =
      (radialOutput a)⁻¹ • innerSL ℝ a := by
    ext z
    simp [ContinuousLinearMap.smul_apply, two_nsmul, smul_eq_mul]
    unfold radialOutput
    have hs := (Real.sqrt_pos_of_pos hp).ne'
    field_simp <;> ring
  change HasFDerivAt (fun x : E => Real.sqrt (1+‖x‖^2)) _ a
  rw [he] at hd
  exact hd

theorem radial_origin_bound (h : E) :
    HasFDerivAt radialOutput (0 : E →L[ℝ] ℝ) 0 ∧
    radialOutput h-1 = ‖h‖^2/(radialOutput h+1) ∧
    0 ≤ radialOutput h-1 ∧ radialOutput h-1 ≤ ‖h‖^2/2 := by
  have hp : 0 ≤ 1+‖h‖^2 := by positivity
  have hs : (radialOutput h)^2 = 1+‖h‖^2 := Real.sq_sqrt hp
  have hn : 0 ≤ radialOutput h := Real.sqrt_nonneg _
  have h₁ : 1 ≤ radialOutput h := by nlinarith [sq_nonneg ‖h‖]
  refine ⟨by simpa using radial_output_derivative (0:E),?_,by linarith,?_⟩
  · apply (eq_div_iff (by linarith : radialOutput h+1 ≠ 0)).2
    nlinarith
  · nlinarith [sq_nonneg (radialOutput h-1)]

theorem radial_operator_norm (z : E) :
    ‖fderiv ℝ radialOutput z‖ = ‖z‖ / radialOutput z ∧
      ‖fderiv ℝ radialOutput z‖ ≤ 1 := by
  have hp : 0 < radialOutput z := Real.sqrt_pos_of_pos (by positivity)
  have hs : (radialOutput z)^2 = 1+‖z‖^2 := Real.sq_sqrt (by positivity)
  have hz : ‖z‖ ≤ radialOutput z := by nlinarith [norm_nonneg z]
  have he := (radial_output_derivative z).fderiv
  have hnorm : ‖fderiv ℝ radialOutput z‖ = ‖z‖ / radialOutput z := by
    rw [he,norm_smul,innerSL_apply_norm,Real.norm_eq_abs,abs_inv,abs_of_pos hp,inv_mul_eq_div]
  refine ⟨hnorm,?_⟩
  rw [hnorm]
  exact (div_le_one hp).2 hz

theorem radial_global_lipschitz (x y : E) :
    |radialOutput y-radialOutput x| ≤ ‖y-x‖ := by
  have hb (z : E) : ‖(radialOutput z)⁻¹ • innerSL ℝ z‖ ≤ 1 := by
    rw [← (radial_output_derivative z).fderiv]
    exact (radial_operator_norm z).2
  have h := (convex_univ (𝕜 := ℝ) (E := E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (radial_output_derivative z).hasFDerivWithinAt) (fun z _ => hb z)
    (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs,one_mul] using h

end Ch12
