import Textbook.Ch13.Audit

namespace Ch13
open Set MeasureTheory
open scoped Interval Matrix

noncomputable def squareCoordinate (p : ℝ × ℝ) : ℝ × ℝ := (p.1^2,p.2)

theorem square_coordinate_image :
    squareCoordinate '' (Icc (-1) 1 ×ˢ Icc 0 1) = Icc 0 1 ×ˢ Icc 0 1 := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    have hq' : -1 ≤ q.1 ∧ q.1 ≤ 1 := hq.1
    have hp : 0 ≤ 1+q.1 := by linarith [hq'.1]
    have h := mul_nonneg (sub_nonneg.mpr hq'.2) hp
    exact ⟨⟨sq_nonneg _,show q.1^2 ≤ 1 by nlinarith⟩,hq.2⟩
  · intro hp
    have hx : 0 ≤ p.1 ∧ p.1 ≤ 1 := hp.1
    have hs := Real.sqrt_le_one.mpr hx.2
    exact ⟨(Real.sqrt p.1,p.2),⟨⟨by linarith [Real.sqrt_nonneg p.1],hs⟩,hp.2⟩,
      Prod.ext (Real.sq_sqrt hx.1) rfl⟩

theorem square_coordinate_two_preimages {x y : ℝ} (hx : x ∈ Ioc 0 1) (hy : y ∈ Icc 0 1) :
    ∃ p q : ℝ × ℝ, p ∈ Icc (-1) 1 ×ˢ Icc 0 1 ∧ q ∈ Icc (-1) 1 ×ˢ Icc 0 1 ∧
      p ≠ q ∧ squareCoordinate p = (x,y) ∧ squareCoordinate q = (x,y) ∧
      ∀ r : ℝ × ℝ, squareCoordinate r = (x,y) → r = p ∨ r = q := by
  have hp := Real.sqrt_pos.2 hx.1
  have hs := Real.sqrt_le_one.mpr hx.2
  have hsq := Real.sq_sqrt hx.1.le
  refine ⟨(Real.sqrt x,y),(-Real.sqrt x,y),⟨⟨by linarith,hs⟩,hy⟩,
    ⟨⟨by linarith,by linarith⟩,hy⟩,?_,Prod.ext hsq rfl,
    Prod.ext (show (-Real.sqrt x)^2 = x by simpa using hsq) rfl,?_⟩
  · intro h
    have he : Real.sqrt x = -Real.sqrt x := congrArg Prod.fst h
    linarith
  · intro r hr
    have h₁ : r.1^2 = x := congrArg Prod.fst hr
    have h₂ : r.2 = y := congrArg Prod.snd hr
    have hz : (r.1-Real.sqrt x)*(r.1+Real.sqrt x) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (Prod.ext (by linarith) h₂)
    · exact Or.inr (Prod.ext (by linarith) h₂)

theorem square_coordinate_inj_nonnegative :
    InjOn squareCoordinate (Icc 0 1 ×ˢ Icc 0 1) := by
  intro p hp q hq h
  have hs : p.1^2 = q.1^2 := congrArg Prod.fst h
  have hp' : 0 ≤ p.1 := hp.1.1
  have hq' : 0 ≤ q.1 := hq.1.1
  have hsnd' := congrArg (fun r : ℝ × ℝ => r.2) h
  have hsnd : p.2 = q.2 := hsnd'
  exact Prod.ext (le_antisymm ((sq_le_sq₀ hp' hq').mp hs.le)
    ((sq_le_sq₀ hq' hp').mp hs.ge)) hsnd

theorem square_coordinate_image_nonnegative :
    squareCoordinate '' (Icc 0 1 ×ˢ Icc 0 1) = Icc 0 1 ×ˢ Icc 0 1 := by
  apply le_antisymm
  · have h : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
    calc
      _ ⊆ squareCoordinate '' (Icc (-1) 1 ×ˢ Icc 0 1) :=
        image_mono (Set.prod_mono h Subset.rfl)
      _ = _ := square_coordinate_image
  · intro p hp
    exact ⟨(Real.sqrt p.1,p.2),⟨⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr hp.1.2⟩,hp.2⟩,
      Prod.ext (Real.sq_sqrt hp.1.1) rfl⟩

theorem square_coordinate_jacobian (u v : ℝ) :
    HasDerivAt (fun t => (squareCoordinate (t,v)).1) (2*u) u ∧
    HasDerivAt (fun t => (squareCoordinate (u,t)).1) 0 v ∧
    HasDerivAt (fun t => (squareCoordinate (t,v)).2) 0 u ∧
    HasDerivAt (fun t => (squareCoordinate (u,t)).2) 1 v ∧
    Matrix.det (!![2*u,0;0,1] : Matrix (Fin 2) (Fin 2) ℝ) = 2*u := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [squareCoordinate] using (hasDerivAt_id u).fun_pow 2
  · exact hasDerivAt_const v (u^2)
  · exact hasDerivAt_const u v
  · exact hasDerivAt_id v
  · simp [Matrix.det_fin_two]

theorem square_coordinate_area_values :
    (∫ u in (-1 : ℝ)..1, ∫ _v in (0 : ℝ)..1, |2*u|) = 2 ∧
    (∫ u in (0 : ℝ)..1, ∫ _v in (0 : ℝ)..1, |2*u|) = 1 ∧
    ((volume.prod volume) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) = 1 := by
  simp_rw [intervalIntegral.integral_const,smul_eq_mul,sub_zero,one_mul]
  have hp : (∫ u in (0 : ℝ)..1, |2*u|) = 1 := by
    calc
      _ = ∫ u in (0 : ℝ)..1, 2*u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le zero_le_one] at hu
        exact abs_of_nonneg (mul_nonneg (by norm_num) hu.1)
      _ = _ := by rw [intervalIntegral.integral_const_mul,Ch09.integral_linear]; norm_num
  have hn : (∫ u in (-1 : ℝ)..0, |2*u|) = 1 := by
    calc
      _ = ∫ u in (-1 : ℝ)..0, (-2)*u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hu
        change |2*u| = (-2)*u
        rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hu.2)]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul,integral_id]; norm_num
  have hc : Continuous (fun u : ℝ => |2*u|) := by fun_prop
  refine ⟨?_,hp,?_⟩
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1),hn,hp]
    norm_num
  · rw [Measure.prod_prod]
    simp only [Real.volume_Icc]
    norm_num

end Ch13
