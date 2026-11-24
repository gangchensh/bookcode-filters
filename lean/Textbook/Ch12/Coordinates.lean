import Textbook.Ch12.SensorBudget
import Textbook.Ch12.Audit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Ch12

open Set
open scoped Matrix RealInnerProductSpace

abbrev RealVector (n : ℕ) := Fin n → ℝ

theorem real_vector_operations {n : ℕ} (x y : RealVector n) (t : ℝ) (i : Fin n) :
    (x+y) i = x i+y i ∧ (t • x) i = t*x i ∧ (0 : RealVector n) i = 0 :=
  ⟨rfl,rfl,rfl⟩

noncomputable def euclideanSize {n : ℕ} (x : RealVector n) : ℝ := Real.sqrt (∑ i, (x i)^2)
noncomputable def maximumSize {n : ℕ} (x : RealVector n) : ℝ := ‖x‖

theorem euclidean_norm_coordinates {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ = euclideanSize (fun i => x i) := by
  rw [EuclideanSpace.norm_eq,euclideanSize]
  simp [Real.norm_eq_abs,sq_abs]

theorem maximum_norm_coordinates {n : ℕ} (x : RealVector n) {r : ℝ} (hr : 0 ≤ r) :
    maximumSize x ≤ r ↔ ∀ i, |x i| ≤ r := by
  simpa [maximumSize,Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg (x := x) hr)

theorem norm_comparison {n : ℕ} (x : RealVector n) :
    maximumSize x ≤ euclideanSize x ∧ euclideanSize x ≤ Real.sqrt n * maximumSize x := by
  have hn : 0 ≤ maximumSize x := norm_nonneg _
  have hsq : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  constructor
  · apply (maximum_norm_coordinates x (Real.sqrt_nonneg _)).2
    intro i
    apply (Real.le_sqrt (abs_nonneg _) hsq).2
    rw [sq_abs]
    exact Finset.single_le_sum (f := fun j => (x j)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  · rw [euclideanSize]
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hn,?_⟩
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ∑ _ : Fin n, (maximumSize x)^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (maximum_norm_coordinates x hn).1 le_rfl i
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hi 2
      _ = _ := by simp

noncomputable def coordinateInner {n : ℕ} (x y : RealVector n) : ℝ := ∑ i, x i*y i

theorem coordinate_inner_self {n : ℕ} (x : RealVector n) :
    coordinateInner x x = euclideanSize x ^ 2 := by
  rw [euclideanSize,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp [coordinateInner,pow_two]

noncomputable def coordinateMatrix {n m : ℕ} (L : RealVector n →ₗ[ℝ] RealVector m) :
    Matrix (Fin m) (Fin n) ℝ := LinearMap.toMatrix (Pi.basisFun ℝ _) (Pi.basisFun ℝ _) L

theorem matrix_column {n m : ℕ} (L : RealVector n →ₗ[ℝ] RealVector m)
    (i : Fin n) (j : Fin m) : coordinateMatrix L j i = L (Pi.single i 1) j := by
  simp [coordinateMatrix,LinearMap.toMatrix_apply,Pi.basisFun_apply]

theorem matrix_represents_linear_map {n m : ℕ} (L : RealVector n →ₗ[ℝ] RealVector m)
    (x : RealVector n) : (coordinateMatrix L).mulVec x = L x := by
  funext j
  have he := congrArg (fun f : RealVector m => f j)
    (LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) L x)
  simpa [coordinateMatrix, Matrix.mulVec, dotProduct, Pi.basisFun_repr] using he

noncomputable def jacobian {n m : ℕ} (F : RealVector n → RealVector m) (a : RealVector n) :
    Matrix (Fin m) (Fin n) ℝ := coordinateMatrix (fderiv ℝ F a).toLinearMap

theorem jacobian_column {n m : ℕ} {F : RealVector n → RealVector m}
    {a : RealVector n} {L : RealVector n →L[ℝ] RealVector m}
    (h : HasFDerivAt F L a) (i : Fin n) (j : Fin m) :
    jacobian F a j i = L (Pi.single i 1) j := by
  rw [jacobian,h.fderiv,matrix_column]
  rfl

theorem jacobian_chain {n m p : ℕ} {F : RealVector n → RealVector m}
    {G : RealVector m → RealVector p} {a : RealVector n}
    {L : RealVector n →L[ℝ] RealVector m} {M : RealVector m →L[ℝ] RealVector p}
    (hF : HasFDerivAt F L a) (hG : HasFDerivAt G M (F a)) :
    HasFDerivAt (G ∘ F) (M.comp L) a ∧ jacobian (G ∘ F) a = jacobian G (F a)*jacobian F a := by
  have h := hG.comp a hF
  refine ⟨h,?_⟩
  rw [jacobian,h.fderiv,jacobian,hG.fderiv,jacobian,hF.fderiv]
  exact LinearMap.toMatrix_comp _ _ _ _ _

theorem scaled_jacobian {n m : ℕ} {F : RealVector n → RealVector m}
    {a : RealVector n} {L : RealVector n →L[ℝ] RealVector m}
    (hF : HasFDerivAt F L a) (Λ : RealVector n →L[ℝ] RealVector n)
    (Γinv : RealVector m →L[ℝ] RealVector m) :
    jacobian (fun ξ => Γinv (F (a+Λ ξ)-F a)) 0 =
      coordinateMatrix Γinv.toLinearMap * jacobian F a * coordinateMatrix Λ.toLinearMap := by
  rw [jacobian,(scaled_model_derivative hF Λ Γinv).fderiv,jacobian,hF.fderiv]
  simp only [coordinateMatrix, ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.toMatrix_comp _ (Pi.basisFun ℝ (Fin m)) _ _ _,
    LinearMap.toMatrix_comp _ (Pi.basisFun ℝ (Fin n)) _ _ _, Matrix.mul_assoc]

def UniformRemainder {n m : ℕ} (input : RealVector n → ℝ) (output : RealVector m → ℝ)
    (R : RealVector n → RealVector m) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ h, input h < δ → output (R h) ≤ ε * input h

theorem equivalent_norm_remainders {n m : ℕ} (R : RealVector n → RealVector m) :
    UniformRemainder euclideanSize euclideanSize R ↔
      UniformRemainder maximumSize maximumSize R := by
  let C : ℝ := max 1 (Real.sqrt n)
  let D : ℝ := max 1 (Real.sqrt m)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hCn (h : RealVector n) : euclideanSize h ≤ C*maximumSize h :=
    (norm_comparison h).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hDm (h : RealVector m) : euclideanSize h ≤ D*maximumSize h :=
    (norm_comparison h).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  constructor
  · intro H ε hε
    obtain ⟨δ,hδ,hR⟩ := H (ε/C) (div_pos hε hC)
    refine ⟨δ/C,div_pos hδ hC,fun h hh => ?_⟩
    have ht : euclideanSize h < δ := (hCn h).trans_lt (by
      have h := (lt_div_iff₀ hC).1 hh
      rwa [mul_comm])
    calc
      maximumSize (R h) ≤ euclideanSize (R h) := (norm_comparison _).1
      _ ≤ ε/C * euclideanSize h := hR h ht
      _ ≤ ε/C * (C*maximumSize h) := mul_le_mul_of_nonneg_left (hCn h) (div_nonneg hε.le hC.le)
      _ = _ := by field_simp
  · intro H ε hε
    obtain ⟨δ,hδ,hR⟩ := H (ε/D) (div_pos hε hD)
    refine ⟨δ,hδ,fun h hh => ?_⟩
    have ht : maximumSize h < δ := (norm_comparison h).1.trans_lt hh
    calc
      euclideanSize (R h) ≤ D*maximumSize (R h) := hDm _
      _ ≤ D*(ε/D*maximumSize h) := mul_le_mul_of_nonneg_left (hR h ht) hD.le
      _ = ε*maximumSize h := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_comparison h).1 hε.le

noncomputable def partialGradient {n : ℕ} (f : RealVector n → ℝ) (a : RealVector n) :
    RealVector n := fun i => deriv (fun t : ℝ => f (a+t • Pi.single i 1)) 0

theorem partial_gradient_coordinate {n : ℕ} {f : RealVector n → ℝ} {a : RealVector n}
    {i : Fin n} {d : ℝ} (hd : HasDerivAt (fun t : ℝ => f (a+t • Pi.single i 1)) d 0) :
    partialGradient f a i = d := hd.deriv

theorem operator_norm_sup {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ‖L‖ = sSup {r : ℝ | ∃ v : E, ‖v‖ ≤ 1 ∧ r = ‖L v‖} := by
  let S := {r : ℝ | ∃ v : E, ‖v‖ ≤ 1 ∧ r = ‖L v‖}
  have h0 : (0 : ℝ) ∈ S := ⟨0, by simp, by simp⟩
  have hb : BddAbove S := ⟨‖L‖, fun r ⟨v,hv,hr⟩ => hr.symm ▸ L.unit_le_opNorm v hv⟩
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_csSup hb h0)
    intro v hv
    exact le_csSup hb ⟨v,hv.le,rfl⟩
  · exact csSup_le ⟨0,h0⟩ (fun r ⟨v,hv,hr⟩ => hr.symm ▸ L.unit_le_opNorm v hv)

end Ch12
