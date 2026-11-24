import Textbook.Ch13.Applications

namespace Ch13

open MeasureTheory

noncomputable def laminaInertiaAt (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ)
    (P : ℝ × ℝ) : ℝ :=
  laminaMoment D ρ (fun x => (x.1-P.1)^2+(x.2-P.2)^2)

/-- Expand around the centroid; its two centered first moments vanish. -/
theorem parallel_axis (D : Set (ℝ × ℝ)) (ρ : ℝ × ℝ → ℝ) (P : ℝ × ℝ)
    (hM : 0 < laminaMass D ρ)
    (hρ : IntegrableOn ρ D)
    (hx : IntegrableOn (fun x => x.1 * ρ x) D)
    (hy : IntegrableOn (fun x => x.2 * ρ x) D)
    (h₂ : IntegrableOn (fun x => ((x.1-(laminaCentroid D ρ).1)^2 +
      (x.2-(laminaCentroid D ρ).2)^2) * ρ x) D) :
    laminaInertiaAt D ρ P = laminaInertiaAt D ρ (laminaCentroid D ρ) +
      laminaMass D ρ * ((P.1-(laminaCentroid D ρ).1)^2+(P.2-(laminaCentroid D ρ).2)^2) := by
  let C := laminaCentroid D ρ
  let X (x : ℝ × ℝ) := x.1 * ρ x - C.1 * ρ x
  let Y (x : ℝ × ℝ) := x.2 * ρ x - C.2 * ρ x
  have hX : IntegrableOn X D := hx.sub (hρ.const_mul _)
  have hY : IntegrableOn Y D := hy.sub (hρ.const_mul _)
  have hX₀ : (∫ x in D, X x) = 0 := by
    unfold X
    rw [integral_sub hx (hρ.const_mul _), integral_const_mul]
    change laminaMoment D ρ Prod.fst -
      (laminaMoment D ρ Prod.fst / laminaMass D ρ) * laminaMass D ρ = 0
    rw [div_mul_cancel₀ _ hM.ne', sub_self]
  have hY₀ : (∫ x in D, Y x) = 0 := by
    unfold Y
    rw [integral_sub hy (hρ.const_mul _), integral_const_mul]
    change laminaMoment D ρ Prod.snd -
      (laminaMoment D ρ Prod.snd / laminaMass D ρ) * laminaMass D ρ = 0
    rw [div_mul_cancel₀ _ hM.ne', sub_self]
  let A (x : ℝ × ℝ) := ((x.1-C.1)^2+(x.2-C.2)^2)*ρ x
  let c := (P.1-C.1)^2+(P.2-C.2)^2
  have expand (x : ℝ × ℝ) : ((x.1-P.1)^2+(x.2-P.2)^2)*ρ x =
      ((A x + (2*(C.1-P.1))*X x) + (2*(C.2-P.2))*Y x) + c*ρ x := by
    dsimp only [A, c, X, Y]
    ring
  unfold laminaInertiaAt laminaMoment
  change (∫ x in D, ((x.1-P.1)^2+(x.2-P.2)^2)*ρ x) =
    (∫ x in D, A x) + laminaMass D ρ * c
  simp_rw [expand]
  have ha : IntegrableOn A D := h₂
  have hx' := hX.const_mul (2*(C.1-P.1))
  have hy' := hY.const_mul (2*(C.2-P.2))
  have hc := hρ.const_mul c
  have hsum := integral_add ((ha.add hx').add hy') hc
  have hsum₂ := integral_add (ha.add hx') hy'
  have hsum₃ := integral_add ha hx'
  simp only [Pi.add_apply] at hsum hsum₂ hsum₃
  rw [hsum, hsum₂, hsum₃]
  simp only [integral_const_mul, hX₀, hY₀, mul_zero, add_zero]
  exact congrArg (_ + ·) (mul_comm c (laminaMass D ρ))

/-- Error bounds for the normalized moments in the triangular lamina example. -/
theorem triangular_centroid_error_bounds (M Qx Qy : ℝ)
    (hM : |M - 1/3| ≤ 1/200) (hx : |Qx - 1/6| ≤ 1/200)
    (hy : |Qy - 1/12| ≤ 1/200) :
    197/600 ≤ M ∧ |Qx/M - 1/2| ≤ 9/394 ∧ |Qy/M - 1/4| ≤ 15/788 := by
  have hMl := (abs_le.mp hM).1
  have hMu := (abs_le.mp hM).2
  have hpos : 0 < M := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hpos]
      linarith [(abs_le.mp hx).1]
    · rw [sub_le_iff_le_add, div_le_iff₀ hpos]
      linarith [(abs_le.mp hx).2]
  · rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hpos]
      linarith [(abs_le.mp hy).1]
    · rw [sub_le_iff_le_add, div_le_iff₀ hpos]
      linarith [(abs_le.mp hy).2]

end Ch13
