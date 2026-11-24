import Textbook.Ch12.Audit

namespace Ch12

theorem sensor_center_expansion (h : ℝ × ℝ) :
    sensor (1,2) = (3,2) ∧
    sensorDifferential (1,2) h = (2*h.1+h.2,2*h.1+h.2) ∧
    sensor ((1,2)+h) = (3,2) + (2*h.1+h.2,2*h.1+h.2) + (h.1^2,h.1*h.2) := by
  constructor
  · norm_num [sensor]
  constructor <;> apply Prod.ext <;> simp [sensor,sensorDifferential,linearModel_apply] <;> ring

theorem sensor_component_budget (h : ℝ × ℝ) {η₁ η₂ : ℝ}
    (h₁ : |h.1| ≤ η₁) (h₂ : |h.2| ≤ η₂) :
    |(sensor ((1,2)+h)).1-(sensor (1,2)).1| ≤ 2*η₁+η₂+η₁^2 ∧
    |(sensor ((1,2)+h)).2-(sensor (1,2)).2| ≤ 2*η₁+η₂+η₁*η₂ := by
  have he := sensor_center_expansion h
  rw [he.1,he.2.2]
  simp only [Prod.fst_add,Prod.snd_add]
  rw [show 3+(2*h.1+h.2)+h.1^2-3 = (2*h.1+h.2)+h.1^2 by ring,
    show 2+(2*h.1+h.2)+h.1*h.2-2 = (2*h.1+h.2)+h.1*h.2 by ring]
  have hb : |2*h.1+h.2| ≤ 2*η₁+η₂ := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  constructor
  · apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg h.1),← sq_abs h.1]
    exact add_le_add hb (pow_le_pow_left₀ (abs_nonneg _) h₁ 2)
  · apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add hb (mul_le_mul h₁ h₂ (abs_nonneg _) ((abs_nonneg _).trans h₁))

noncomputable def sensorCombination (x : ℝ × ℝ) : ℝ := 3*(sensor x).1-(sensor x).2

theorem sensor_combination_budget (h : ℝ × ℝ) {η : ℝ} (h₁ : |h.1| ≤ η) (h₂ : |h.2| ≤ η) :
    sensorCombination ((1,2)+h)-sensorCombination (1,2) = 4*h.1+2*h.2+3*h.1^2-h.1*h.2 ∧
    |sensorCombination ((1,2)+h)-sensorCombination (1,2)| ≤ 6*η+4*η^2 ∧
    |sensorCombination ((1,2)+h)-sensorCombination (1,2)-(4*h.1+2*h.2)| ≤ 4*η^2 := by
  have he : sensorCombination ((1,2)+h)-sensorCombination (1,2) =
      4*h.1+2*h.2+3*h.1^2-h.1*h.2 := by simp [sensorCombination,sensor]; ring
  have hη := (abs_nonneg h.1).trans h₁
  have hl : |4*h.1+2*h.2| ≤ 6*η := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hr : |3*h.1^2-h.1*h.2| ≤ 4*η^2 := by
    rw [sub_eq_add_neg]
    apply (abs_add_le _ _).trans
    rw [abs_neg,abs_of_nonneg (by positivity : 0 ≤ 3*h.1^2),abs_mul]
    have hsq := pow_le_pow_left₀ (abs_nonneg h.1) h₁ 2
    rw [sq_abs] at hsq
    have hm := mul_le_mul h₁ h₂ (abs_nonneg h.2) hη
    linarith
  refine ⟨he,?_,?_⟩
  · rw [he,show 4*h.1+2*h.2+3*h.1^2-h.1*h.2 =
      (4*h.1+2*h.2)+(3*h.1^2-h.1*h.2) by ring]
    exact (abs_add_le _ _).trans (add_le_add hl hr)
  · rw [he,show 4*h.1+2*h.2+3*h.1^2-h.1*h.2-(4*h.1+2*h.2) =
      3*h.1^2-h.1*h.2 by ring]
    exact hr

theorem sensor_numeric_budget (h : ℝ × ℝ)
    (h₁ : |h.1| ≤ 1/100) (h₂ : |h.2| ≤ 1/100) :
    |(sensor ((1,2)+h)).1-(sensor (1,2)).1| ≤ 301/10000 ∧
    |(sensor ((1,2)+h)).2-(sensor (1,2)).2| ≤ 301/10000 ∧
    |(sensor ((1,2)+h)).1-(sensor (1,2)).1-(sensorDifferential (1,2) h).1| ≤ 1/10000 ∧
    |(sensor ((1,2)+h)).2-(sensor (1,2)).2-(sensorDifferential (1,2) h).2| ≤ 1/10000 := by
  have hb := sensor_component_budget h h₁ h₂
  have hr := sensor_remainder_estimate (1,2) h (1/100) (by norm_num) h₁ h₂
  norm_num at hb hr ⊢
  exact ⟨hb.1,hb.2,hr.1,hr.2⟩

theorem sensor_combination_tolerance (h : ℝ × ℝ) (h₁ : |h.1| ≤ 1/200)
    (h₂ : |h.2| ≤ 1/200) :
    |sensorCombination ((1,2)+h)-sensorCombination (1,2)-(4*h.1+2*h.2)| ≤ 1/10000 := by
  exact (sensor_combination_budget h h₁ h₂).2.2.trans (by norm_num)

theorem scaled_model_derivative {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E → G} {a : E} {L : E →L[ℝ] G}
    (h : HasFDerivAt F L a) (Λ : E →L[ℝ] E) (Γinv : G →L[ℝ] G) :
    HasFDerivAt (fun ξ => Γinv (F (a+Λ ξ)-F a)) (Γinv.comp (L.comp Λ)) 0 := by
  have hi : HasFDerivAt (fun ξ => a+Λ ξ) Λ (0:E) :=
    Λ.hasFDerivAt.const_add a
  have ho : HasFDerivAt (fun z => F z-F a) L (a+Λ (0:E)) := by
    rw [map_zero,add_zero]
    exact h.sub_const (F a)
  have hc := ho.comp (0:E) hi
  exact Γinv.hasFDerivAt.comp (0:E) hc

end Ch12
