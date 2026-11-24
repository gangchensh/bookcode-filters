import Textbook.Ch04.OneSidedInfinity

namespace Ch04
open Ch02 Ch03 Ch03Approach Ch03Rules

variable {α : Type*} {F : BookFilter α} {f g h : α → ℝ} {a b c : ℝ}

theorem real_mathlib_iff (f : α → ℝ) (F : BookFilter α) (a : ℝ) :
    Approaches f F (neighborhoodFilter a) ↔
      Filter.Tendsto f (toMathlib F) (nhds a) := by
  rw [approaches_mathlib_iff, Ch03.toMathlib_neighborhood]

theorem limit_add                                      -- 共同源上的和极限
    (hf : Approaches f F (neighborhoodFilter a))
    (hg : Approaches g F (neighborhoodFilter b)) :
    Approaches (fun x => f x+g x) F (neighborhoodFilter (a+b)) := by
  apply (real_iff _ _ _).2                            -- 改证和的距离最终小于 ε
  intro ε hε
  apply F.upward (F.inter_mem
    ((real_iff _ _ _).1 hf (ε/2) (half_pos hε))
    ((real_iff _ _ _).1 hg (ε/2) (half_pos hε)))       -- 合并两个 ε/2 距离要求
  intro x hx
  have hxf : |f x-a| < ε/2 := hx.1
  have hxg : |g x-b| < ε/2 := hx.2
  change |f x+g x-(a+b)| < ε
  calc
    |f x+g x-(a+b)| = |(f x-a)+(g x-b)| := by congr 1; ring
    _ ≤ |f x-a|+|g x-b| := abs_add_le _ _
    _ < ε := by linarith                             -- 两个半精度相加得到 ε

theorem limit_neg                                      -- 取负号保持到目标的距离
    (hf : Approaches f F (neighborhoodFilter a)) :
    Approaches (fun x => -f x) F (neighborhoodFilter (-a)) := by
  apply (real_iff _ _ _).2
  intro ε hε
  apply F.upward ((real_iff _ _ _).1 hf ε hε)
  intro x hx
  have hd : |f x-a| < ε := hx
  change |-f x-(-a)| < ε
  simpa only [neg_sub_neg, abs_sub_comm] using hd     -- 用 |-u-(-v)|=|u-v|

theorem limit_sub
    (hf : Approaches f F (neighborhoodFilter a))
    (hg : Approaches g F (neighborhoodFilter b)) :
    Approaches (fun x => f x-g x) F (neighborhoodFilter (a-b)) := by
  simpa only [sub_eq_add_neg] using limit_add hf (limit_neg hg)

theorem limit_mul                                      -- 乘积极限需先控制一个因子的大小
    (hf : Approaches f F (neighborhoodFilter a))
    (hg : Approaches g F (neighborhoodFilter b)) :
    Approaches (fun x => f x*g x) F (neighborhoodFilter (a*b)) := by
  apply (real_iff _ _ _).2
  intro ε hε
  have hB : 0 < |b|+1 := by positivity
  have hA : 0 < |a|+1 := by positivity
  apply F.upward (F.inter_mem (Ch04Local.limit_eventually_bounded hg)
    (F.inter_mem
      ((real_iff _ _ _).1 hf (ε/(2*(|b|+1))) (by positivity))
      ((real_iff _ _ _).1 hg (ε/(2*(|a|+1))) (by positivity))))
  intro x hx                                         -- 同时取得有界与两个小距离
  have hbound : |g x| < |b|+1 := hx.1
  have hxf : |f x-a| < ε/(2*(|b|+1)) := hx.2.1
  have hxg : |g x-b| < ε/(2*(|a|+1)) := hx.2.2
  have hfsmall : |f x-a| *(2*(|b|+1)) < ε :=
    (lt_div_iff₀ (by positivity)).1 hxf
  have hgsmall : |g x-b| *(2*(|a|+1)) < ε :=
    (lt_div_iff₀ (by positivity)).1 hxg
  have hfirst : |f x-a| *|g x| ≤ |f x-a| *(|b|+1) :=
    mul_le_mul_of_nonneg_left (le_of_lt hbound) (abs_nonneg _)
  have hsecond : |a| *|g x-b| ≤ (|a|+1)*|g x-b| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  change |f x*g x-a*b| < ε
  calc
    |f x*g x-a*b| = |(f x-a)*g x+a*(g x-b)| := by congr 1; ring
    _ ≤ |(f x-a)*g x|+|a*(g x-b)| := abs_add_le _ _
    _ = |f x-a| *|g x|+|a| *|g x-b| := by rw [abs_mul, abs_mul]
    _ < ε := by nlinarith                            -- 两项分别小于 ε/2

theorem limit_const_mul (k : ℝ)
    (hf : Approaches f F (neighborhoodFilter a)) :
    Approaches (fun x => k*f x) F (neighborhoodFilter (k*a)) :=
  limit_mul (const_limit F k) hf

theorem limit_inv                                      -- 非零目标保证倒数连续
    (hf : Approaches f F (neighborhoodFilter a)) (ha : a ≠ 0) :
    Approaches (fun x => (f x)⁻¹) F (neighborhoodFilter a⁻¹) := by
  apply (real_mathlib_iff _ _ _).2
  exact ((real_mathlib_iff _ _ _).1 hf).inv₀ ha        -- 调用 Mathlib 的非零点倒数规则

theorem limit_div
    (hf : Approaches f F (neighborhoodFilter a))
    (hg : Approaches g F (neighborhoodFilter b)) (hb : b ≠ 0) :
    Approaches (fun x => f x/g x) F (neighborhoodFilter (a/b)) := by
  simpa only [div_eq_mul_inv] using limit_mul hf (limit_inv hg hb)

theorem limit_pow (n : ℕ)                              -- 自然数幂由乘法递推
    (hf : Approaches f F (neighborhoodFilter a)) :
    Approaches (fun x => (f x)^n) F (neighborhoodFilter (a^n)) := by
  induction n with
  | zero => simpa using const_limit F (1 : ℝ)
  | succ n ih => simpa only [pow_succ] using limit_mul ih hf

theorem limit_abs
    (hf : Approaches f F (neighborhoodFilter a)) :
    Approaches (fun x => |f x|) F (neighborhoodFilter |a|) := by
  apply (real_iff _ _ _).2
  intro ε hε
  apply F.upward ((real_iff _ _ _).1 hf ε hε)
  intro x hx
  have hd : |f x-a| < ε := hx
  change abs (abs (f x) - abs a) < ε
  exact lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) hd

theorem limit_max
    (hf : Approaches f F (neighborhoodFilter a))
    (hg : Approaches g F (neighborhoodFilter b)) :
    Approaches (fun x => max (f x) (g x)) F (neighborhoodFilter (max a b)) := by
  apply (real_mathlib_iff _ _ _).2
  exact ((real_mathlib_iff _ _ _).1 hf).max ((real_mathlib_iff _ _ _).1 hg)

theorem limit_min
    (hf : Approaches f F (neighborhoodFilter a))
    (hg : Approaches g F (neighborhoodFilter b)) :
    Approaches (fun x => min (f x) (g x)) F (neighborhoodFilter (min a b)) := by
  apply (real_mathlib_iff _ _ _).2
  exact ((real_mathlib_iff _ _ _).1 hf).min ((real_mathlib_iff _ _ _).1 hg)

theorem limit_le                                       -- 保序必须从共同成员取到实际的点
    (hF : IsProper F)
    (hf : Approaches f F (neighborhoodFilter a))
    (hg : Approaches g F (neighborhoodFilter b))
    (hfg : Eventually F (fun x => f x ≤ g x)) : a ≤ b := by
  by_contra hn
  have hab : b < a := lt_of_not_ge hn
  have hd : 0 < (a-b)/3 := by linarith
  rcases eventually_exists hF
    (eventually_and hfg (eventually_and
      ((real_iff _ _ _).1 hf _ hd)
      ((real_iff _ _ _).1 hg _ hd))) with ⟨x, hx, hxf, hxg⟩
  have hfsmall : |f x-a| < (a-b)/3 := hxf
  have hgsmall : |g x-b| < (a-b)/3 := hxg
  have hfa := (abs_lt.mp hfsmall).1                  -- f(x)>a-(a-b)/3
  have hgb := (abs_lt.mp hgsmall).2                  -- g(x)<b+(a-b)/3
  have horder : f x ≤ g x := hx
  linarith                                          -- 与 f(x)≤g(x) 矛盾

theorem limit_squeeze                                  -- 两侧同极限与最终夹住即可
    (hf : Approaches f F (neighborhoodFilter a))
    (hh : Approaches h F (neighborhoodFilter a))
    (hfg : Eventually F (fun x => f x ≤ g x))
    (hgh : Eventually F (fun x => g x ≤ h x)) :
    Approaches g F (neighborhoodFilter a) := by
  apply (real_iff _ _ _).2
  intro ε hε
  apply F.upward (F.inter_mem (F.inter_mem hfg hgh)
    (F.inter_mem ((real_iff _ _ _).1 hf ε hε)
      ((real_iff _ _ _).1 hh ε hε)))
  intro x hx
  have hlow : f x ≤ g x := hx.1.1
  have hupp : g x ≤ h x := hx.1.2
  have hfd : |f x-a| < ε := hx.2.1
  have hhd : |h x-a| < ε := hx.2.2
  change |g x-a| < ε
  exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hfd).1],
    by linarith [(abs_lt.mp hhd).2]⟩                 -- 得到 a-ε<g(x)<a+ε

theorem bounded_mul_zero (C : ℝ)                       -- 有界因子不必收敛
    (hC : 0 ≤ C) (hbound : Eventually F (fun x => |f x| ≤ C))
    (hg : Approaches g F (neighborhoodFilter 0)) :
    Approaches (fun x => f x*g x) F (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2
  intro ε hε
  apply F.upward (F.inter_mem hbound
    ((real_iff _ _ _).1 hg (ε/(C+1)) (by positivity)))
  intro x hx
  have hfC : |f x| ≤ C := hx.1
  have hgd : |g x-0| < ε/(C+1) := hx.2
  rw [sub_zero] at hgd
  have hsmall : |g x| *(C+1) < ε :=
    (lt_div_iff₀ (by positivity)).1 hgd
  have hprod : |f x| *|g x| ≤ C*|g x| :=
    mul_le_mul_of_nonneg_right hfC (abs_nonneg _)
  change |f x*g x-0| < ε
  rw [sub_zero, abs_mul]
  nlinarith [abs_nonneg (g x)]                       -- C|g|≤(C+1)|g|<ε

theorem upper_of_lower                                 -- 最终较大的函数继承正无穷
    (hf : Approaches f F (upperFilter ℝ))
    (hfg : Eventually F (fun x => f x ≤ g x)) :
    Approaches g F (upperFilter ℝ) := by
  apply (Ch04Infinity.upper_iff _ _).2
  intro M
  apply F.upward (F.inter_mem ((Ch04Infinity.upper_iff _ _).1 hf M) hfg)
  intro x hx
  have hM : M ≤ f x := hx.1
  have hfgx : f x ≤ g x := hx.2
  change M ≤ g x
  exact le_trans hM hfgx

theorem upper_add_finite
    (hf : Approaches f F (upperFilter ℝ))
    (hg : Approaches g F (neighborhoodFilter b)) :
    Approaches (fun x => f x+g x) F (upperFilter ℝ) := by
  apply (Ch04Infinity.upper_iff _ _).2
  intro M
  apply F.upward (F.inter_mem
    ((Ch04Infinity.upper_iff _ _).1 hf (M+|b|+1))
    (Ch04Local.limit_eventually_bounded hg))
  intro x hx
  have hfm : M+|b|+1 ≤ f x := hx.1
  have hgb : |g x| < |b|+1 := hx.2
  have hgl := (abs_lt.mp hgb).1
  change M ≤ f x+g x
  linarith

theorem quadratic_limit (s : ℝ)                        -- 组合规则代替重复半径估计
    : Approaches (fun x : ℝ => x^2+3*x-2)
      (punctured s) (neighborhoodFilter (s^2+3*s-2)) := by
  have hi : Approaches (fun x : ℝ => x) (punctured s) (neighborhoodFilter s) :=
    approaches_within_source _ (approaches_id _)
  exact limit_sub (limit_add (limit_pow 2 hi) (limit_const_mul 3 hi))
    (const_limit _ 2)

end Ch04
