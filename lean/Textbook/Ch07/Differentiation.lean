import Textbook.Ch06.Derivatives

namespace Ch07
open Ch06 Set
open Ch02 Ch03 Ch03Approach Ch03Rules Ch04

-- BEGIN product_direct
theorem product_rule_direct {f g : ℝ → ℝ} {a df dg : ℝ}
    (hf : HasDerivative f a df) (hg : HasDerivative g a dg) :
    HasDerivative (fun x => f x * g x) a (df * g a + f a * dg) := by
  have hgc : Approaches g (punctured a) (neighborhoodFilter (g a)) :=
    approaches_within_source _ (derivative_continuous hg)
  have hsum := limit_add (limit_mul hgc hf) (limit_const_mul (f a) hg)
  have heq : Eventually (punctured a) (fun x =>
      g x * ((f x - f a) / (x - a)) + f a * ((g x - g a) / (x - a)) =
        (f x * g x - f a * g a) / (x - a)) := by
    apply (punctured a).upward (punctured_ne a)
    intro x hx
    have hden : x - a ≠ 0 := sub_ne_zero.mpr hx
    change g x * ((f x - f a) / (x - a)) + f a * ((g x - g a) / (x - a)) =
      (f x * g x - f a * g a) / (x - a)
    field_simp [hden]
    <;> ring                                   -- 同一去心范围内核对乘积差商
  have h := approaches_congr heq hsum           -- 用最终相等替换差商
  simpa [HasDerivative, mul_comm, add_comm] using h
-- END product_direct

-- BEGIN product
theorem product_rule {f g : ℝ → ℝ} {a df dg : ℝ}
    (hf : HasDerivative f a df) (hg : HasDerivative g a dg) :
    HasDerivative (fun x => f x * g x) a (df * g a + f a * dg) := by
  apply (derivative_mathlib _ _ _).2              -- 转换成Mathlib的导数命题
  exact ((derivative_mathlib _ _ _).1 hf).fun_mul
    ((derivative_mathlib _ _ _).1 hg)
-- END product

-- BEGIN chain
theorem chain_rule {f g : ℝ → ℝ} {a df dg : ℝ}
    (hf : HasDerivative f a df) (hg : HasDerivative g (f a) dg) :
    HasDerivative (fun x => g (f x)) a (dg * df) := by
  apply (derivative_mathlib _ _ _).2
  exact ((derivative_mathlib _ _ _).1 hg).comp a
    ((derivative_mathlib _ _ _).1 hf)             -- 中间点必须为f a
-- END chain

-- BEGIN mvt
theorem mean_value (f df : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x) :
    ∃ c ∈ Ioo a b, df c = (f b - f a) / (b - a) := by
  exact exists_hasDerivAt_eq_slope f df hab hc hd
-- END mvt

-- BEGIN sensitivity
theorem sensitivity_bound (f df : ℝ → ℝ) {a b M : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hM : ∀ x ∈ Ioo a b, |df x| ≤ M) :
    |f b - f a| ≤ M * (b - a) := by
  obtain ⟨c, hc', he⟩ := mean_value f df hab hc hd  -- 取得区间内的点c及斜率等式
  have heq : f b - f a = df c * (b - a) :=
    ((eq_div_iff (sub_ne_zero.mpr hab.ne')).1 he).symm
  rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hab)]  -- 把函数值差改写为导数乘区间长度
  exact mul_le_mul_of_nonneg_right (hM c hc')    -- 用c处的导数界控制乘积
    (sub_nonneg.mpr hab.le)
-- END sensitivity

-- BEGIN design
def cost (x : ℝ) : ℝ := (x - 3) ^ 2 + 2

theorem cost_derivative (a : ℝ) :
    HasDerivAt cost (2 * (a - 3)) a := by
  change HasDerivAt (fun x : ℝ => (x - 3) ^ 2 + 2) (2 * (a - 3)) a  -- 展开cost，显示待求导的函数
  apply (hasDerivAt_add_const_iff (2 : ℝ)).2  -- 去掉不影响导数的常数2
  simpa using ((hasDerivAt_id a).sub_const 3).fun_pow 2

theorem cost_minimum (x : ℝ) : 2 ≤ cost x := by
  unfold cost
  nlinarith [sq_nonneg (x - 3)]                   -- 对所有输入给出下界

theorem cost_eq_minimum (x : ℝ) : cost x = 2 ↔ x = 3 := by
  unfold cost
  constructor
  · intro h; nlinarith [sq_nonneg (x - 3)]  -- 由代价等于2推出x=3
  · intro h; simp [h]  -- 代入x=3验证等号
-- END design

-- BEGIN worked_chain
theorem fourth_power_derivative (a : ℝ) :
    HasDerivative (fun x => (x ^ 2) ^ 2) a (4 * a ^ 3) := by
  have hinner := derivative_square a               -- 内层在a处的导数为2a
  have houter := derivative_square (a ^ 2)         -- 外层在a²处的导数为2a²
  have h := chain_rule hinner houter               -- 合成后系数为2a²乘2a
  convert h using 1 <;> ring                       -- 核对系数等于4a³
-- END worked_chain

-- BEGIN perturbation
theorem perturbed_cost_bound (y eta actualY actual3 : ℝ)
    (hY : cost y ≤ actualY + eta)
    (hopt : actualY ≤ actual3)
    (h3 : actual3 ≤ cost 3 + eta) :
    (y - 3) ^ 2 ≤ 2 * eta := by
  have hc : cost 3 = 2 := by norm_num [cost]
  unfold cost at hY                                -- 代价差中出现(y-3)²
  linarith                                        -- 合并三条代价上界
-- END perturbation

-- BEGIN box_certificate
theorem box_identity (x r : ℝ) (hx : x ≠ 0) :
    x ^ 2 + 2 * r ^ 3 / x - 3 * r ^ 2 =
      (x - r) ^ 2 * (x + 2 * r) / x := by
  field_simp [hx]                                 -- 由x≠0清除分母
  <;> ring                                       -- 核对精确因式分解

theorem box_minimum (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    3 * r ^ 2 ≤ x ^ 2 + 2 * r ^ 3 / x := by
  apply sub_nonneg.mp
  rw [box_identity x r (ne_of_gt hx)]
  positivity                                     -- 平方、正因子与正分母保证非负
-- END box_certificate

end Ch07
