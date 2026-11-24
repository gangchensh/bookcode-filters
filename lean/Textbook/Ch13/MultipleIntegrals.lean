import Textbook.Ch10.Methods

namespace Ch13
open MeasureTheory Set
open scoped Interval Matrix

-- BEGIN fubini
theorem product_fubini (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) :
    (∫ z, f z ∂volume.prod volume) =
      ∫ x : ℝ, ∫ y : ℝ, f (x, y) := by
  exact integral_prod f hf                         -- 绝对可积性保证区域积分等于迭代积分

theorem swap_integrals (f : ℝ → ℝ → ℝ)
    (hf : Integrable (Function.uncurry f) (volume.prod volume)) :
    (∫ x : ℝ, ∫ y : ℝ, f x y) = ∫ y : ℝ, ∫ x : ℝ, f x y := by
  exact integral_integral_swap hf                 -- 保留同一个二维被积函数
-- END fubini

-- BEGIN rectangle
theorem rectangle_integrable :
    Integrable (fun z : ℝ × ℝ => z.1 * z.2)
      ((volume.restrict (Ioc 0 1)).prod (volume.restrict (Ioc 0 1))) := by
  have h : IntegrableOn (fun x : ℝ => x) (Ioc 0 1) :=
    continuous_id.integrableOn_Ioc
  exact h.mul_prod h                              -- 两个一元可积函数的乘积可积

theorem rectangle_product :
    (∫ z : ℝ × ℝ in (Ioc (0 : ℝ) 1) ×ˢ (Ioc (0 : ℝ) 1),
      z.1 * z.2 ∂volume.prod volume) = 1 / 4 := by
  have hi : (∫ x : ℝ in Ioc (0 : ℝ) 1, x) = 1 / 2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Ch09.integral_linear
  calc
    _ = (∫ x : ℝ in Ioc (0 : ℝ) 1, x) * (∫ y : ℝ in Ioc (0 : ℝ) 1, y) :=
      setIntegral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y) _ _
    _ = 1/4 := by rw [hi]; norm_num  -- 两个1/2相乘得到1/4
-- END rectangle

-- BEGIN mass
theorem triangle_mass :
    (∫ x : ℝ in (0 : ℝ)..1, ∫ _y : ℝ in (0 : ℝ)..(1-x), 2*x) = 1/3 := by
  simp_rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hd : ∀ x : ℝ, HasDerivAt
      (fun t => t^2 - (2/3 : ℝ)*t^3) ((1-x)*(2*x)) x := by
    intro x
    convert ((hasDerivAt_id x).fun_pow 2).sub
      (((hasDerivAt_id x).fun_pow 3).const_mul (2/3 : ℝ)) using 1 <;>
      first | rfl
            | (funext t; dsimp; norm_num <;> ring)
            | (dsimp; norm_num <;> ring)           -- 核对原函数的导数系数
  have hi : IntervalIntegrable (fun x : ℝ => (1-x)*(2*x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [Ch09.primitive_integral (fun x _ => hd x) hi]
  norm_num                                        -- x²−2x³/3在0、1处的端点差
-- END mass

-- BEGIN moment
theorem triangle_moment_x :
    (∫ x : ℝ in (0 : ℝ)..1, ∫ _y : ℝ in (0 : ℝ)..(1-x), x*(2*x)) = 1/6 := by
  simp_rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hd : ∀ x : ℝ, HasDerivAt
      (fun t => (2/3 : ℝ)*t^3 - t^4/2) ((1-x)*(x*(2*x))) x := by
    intro x
    convert (((hasDerivAt_id x).fun_pow 3).const_mul (2/3 : ℝ)).sub
      (((hasDerivAt_id x).fun_pow 4).div_const 2) using 1 <;>
      first | rfl
            | (funext t; dsimp; norm_num <;> ring)
            | (dsimp; norm_num <;> ring)
  have hi : IntervalIntegrable (fun x : ℝ => (1-x)*(x*(2*x))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [Ch09.primitive_integral (fun x _ => hd x) hi]
  norm_num

theorem triangle_y_slice (x : ℝ) :
    (∫ y : ℝ in (0 : ℝ)..(1-x), y*(2*x)) = x*(1-x)^2 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun t => x*t^2) (y*(2*x)) y := by
    intro y
    convert ((hasDerivAt_id y).fun_pow 2).const_mul x using 1 <;>
      first | rfl | (funext t; dsimp; ring) | (dsimp; ring)
  have hi : IntervalIntegrable (fun y : ℝ => y*(2*x)) volume 0 (1-x) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [Ch09.primitive_integral (fun y _ => hd y) hi]
  simp

theorem triangle_moment_y :
    (∫ x : ℝ in (0 : ℝ)..1, ∫ y : ℝ in (0 : ℝ)..(1-x), y*(2*x)) = 1/12 := by
  simp_rw [triangle_y_slice]
  have hd : ∀ x : ℝ, HasDerivAt
      (fun t => t^2/2 - (2/3 : ℝ)*t^3 + t^4/4) (x*(1-x)^2) x := by
    intro x
    convert ((((hasDerivAt_id x).fun_pow 2).div_const 2).sub
      (((hasDerivAt_id x).fun_pow 3).const_mul (2/3 : ℝ))).add
      (((hasDerivAt_id x).fun_pow 4).div_const 4) using 1 <;>
      first | rfl
            | (funext t; dsimp; norm_num <;> ring)
            | (dsimp; norm_num <;> ring)
  have hi : IntervalIntegrable (fun x : ℝ => x*(1-x)^2) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [Ch09.primitive_integral (fun x _ => hd x) hi]
  norm_num
-- END moment

-- BEGIN centroid
theorem centroid_values :
    ((1/6 : ℝ)/(1/3) = 1/2) ∧ ((1/12 : ℝ)/(1/3) = 1/4) := by
  norm_num                                        -- 用正总质量归一化两个一阶矩
-- END centroid

-- BEGIN jacobian
theorem polar_determinant (r θ : ℝ) :
    Matrix.det (!![Real.cos θ, -r*Real.sin θ;
      Real.sin θ, r*Real.cos θ]) = r := by
  calc
    _ = r*(Real.sin θ^2+Real.cos θ^2) := by
      rw [Matrix.det_fin_two]
      change Real.cos θ*(r*Real.cos θ)-(-r*Real.sin θ)*Real.sin θ =
        r*(Real.sin θ^2+Real.cos θ^2)
      ring
    _ = r := by rw [Real.sin_sq_add_cos_sq]; ring  -- r(cos²θ+sin²θ)=r

theorem polar_area_factor (r θ : ℝ) (hr : 0 ≤ r) :
    |Matrix.det (!![Real.cos θ, -r*Real.sin θ;
      Real.sin θ, r*Real.cos θ])| = r := by
  rw [polar_determinant, abs_of_nonneg hr]          -- 面积因子使用行列式绝对值
-- END jacobian

-- BEGIN disk
theorem radial_integral (R : ℝ) :
    (∫ r : ℝ in (0 : ℝ)..R, r) = R^2/2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t => t^2/2) x x := by
    intro x
    convert ((hasDerivAt_id x).fun_pow 2).div_const 2 using 1 <;> simp <;> ring
  rw [Ch09.primitive_integral (fun x _ => hd x)
    (continuous_id.intervalIntegrable 0 R)]
  simp

theorem polar_disk_area (R : ℝ) :
    (∫ _θ : ℝ in (0 : ℝ)..(2*Real.pi), ∫ r : ℝ in (0 : ℝ)..R, r) =
      Real.pi * R^2 := by
  simp_rw [radial_integral]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  ring                                            -- 几何圆盘解释另要求R≥0
-- END disk

-- BEGIN work
theorem circle_work :
    (∫ t : ℝ in (0 : ℝ)..(2*Real.pi),
      (-Real.sin t)*(-Real.sin t)+Real.cos t*Real.cos t) = 2*Real.pi := by
  have h : (fun t : ℝ => (-Real.sin t)*(-Real.sin t)+Real.cos t*Real.cos t) =
      (fun _ => (1 : ℝ)) := by
    funext t
    nlinarith [Real.sin_sq_add_cos_sq t]            -- 圆周功的参数被积函数恒为1
  rw [h, intervalIntegral.integral_const]
  ring
-- END work

-- BEGIN flux
theorem plane_flux :
    (∫ _u : ℝ in (0 : ℝ)..1, ∫ _v : ℝ in (0 : ℝ)..1, (3 : ℝ)) = 3 := by
  simp                                            -- 向上定向平面上的常通量

theorem plane_area :
    (∫ _u : ℝ in (0 : ℝ)..1, ∫ _v : ℝ in (0 : ℝ)..1, Real.sqrt 6) =
      Real.sqrt 6 := by
  simp                                            -- 面积元为√6，不携带定向符号
-- END flux

-- BEGIN polar_region
theorem polar_region_change (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (f : ℝ × ℝ → ℝ) :
    (∫ p in D, f p) = ∫ q in polarCoord.target,
      q.1 * (D.indicator f) (polarCoord.symm q) := by
  rw [← integral_indicator hD]
  symm
  simpa only [smul_eq_mul] using
    integral_comp_polarCoord_symm (D.indicator f)    -- 区域限制随极坐标映射一起拉回
-- END polar_region

-- BEGIN plane_normal
theorem plane_cross_product :
    crossProduct (![1, 0, 1] : Fin 3 → ℝ) ![0, 1, 2] = ![-1, -2, 1] := by
  ext i
  fin_cases i <;> norm_num [crossProduct]           -- 三个分量分别核验向上叉积
-- END plane_normal

-- BEGIN gaussian
theorem gaussian_integrable : Integrable (fun x : ℝ => Real.exp (-(x^2))) := by
  simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)

theorem gaussian_integral :
    (∫ x : ℝ, Real.exp (-(x^2))) = Real.sqrt Real.pi := by
  simpa using integral_gaussian (1 : ℝ)            -- 参数b=1的原生Gaussian积分
-- END gaussian

theorem disk_region_polar (R : ℝ) (hR : 0 ≤ R) (f : ℝ × ℝ → ℝ) :
    (∫ p in {p : ℝ × ℝ | p.1^2 + p.2^2 ≤ R^2}, f p) =
      ∫ q in polarCoord.target,
        if q.1 ≤ R then q.1 * f (polarCoord.symm q) else 0 := by
  let D : Set (ℝ × ℝ) := {p | p.1^2 + p.2^2 ≤ R^2}
  have hD : MeasurableSet D := by
    apply IsClosed.measurableSet
    exact isClosed_le (by fun_prop) continuous_const
  rw [polar_region_change D hD f]
  apply setIntegral_congr_fun polarCoord.open_target.measurableSet
  rintro ⟨r, θ⟩ hq
  have hr : 0 < r := hq.1
  have hs : (polarCoord.symm (r, θ)).1^2 +
      (polarCoord.symm (r, θ)).2^2 = r^2 := by
    change (r * Real.cos θ)^2 + (r * Real.sin θ)^2 = r^2
    calc
      _ = r^2 * (Real.sin θ^2 + Real.cos θ^2) := by ring
      _ = r^2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hmem : polarCoord.symm (r, θ) ∈ D ↔ r ≤ R := by
    change ((polarCoord.symm (r, θ)).1^2 +
      (polarCoord.symm (r, θ)).2^2 ≤ R^2) ↔ r ≤ R
    rw [hs]
    exact sq_le_sq₀ (le_of_lt hr) hR
  change r * D.indicator f (polarCoord.symm (r, θ)) =
    if r ≤ R then r * f (polarCoord.symm (r, θ)) else 0
  by_cases h : r ≤ R
  · rw [Set.indicator_of_mem (hmem.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem (fun hm => h (hmem.mp hm))]
    simp [h]

end Ch13
