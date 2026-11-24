import Textbook.Ch04.LocalLimits

namespace Ch04Infinity
open Ch02 Ch03 Ch03Approach Ch03Rules

theorem upper_iff {α : Type*}                                                   -- 正无穷的阈值判定
    (f : α → ℝ) (F : BookFilter α) :
    Approaches f F (upperFilter ℝ) ↔
      ∀ M : ℝ, Eventually F (fun x => M ≤ f x) := by
  constructor                                                                   -- 分两向；先证阈值最终满足
  · intro h M                                                                   -- 任取上阈值 M
    exact h {y | M ≤ y} ⟨M, fun y hy => hy⟩                                     -- 对目标上尾 [M,+∞) 取原像
  · intro h V hV                                                                -- 反向：任取目标成员 V
    rcases hV with ⟨M, hM⟩                                                      -- 取 M，使 [M,+∞) ⊆ V
    exact F.upward (h M) (fun x hx => hM _ hx)                                  -- 由 M≤f(x) 推出 f(x)∈V

theorem lower_iff {α : Type*}                                                   -- 负无穷的阈值判定
    (f : α → ℝ) (F : BookFilter α) :
    Approaches f F (lowerFilter ℝ) ↔
      ∀ M : ℝ, Eventually F (fun x => f x ≤ M) := by
  constructor                                                                   -- 分两向；先取目标下尾
  · intro h M                                                                   -- 任取下阈值 M
    exact h {y | y ≤ M} ⟨M, fun y hy => hy⟩                                     -- 对目标下尾 (-∞,M] 取原像
  · intro h V hV                                                                -- 反向：恢复任意目标成员
    rcases hV with ⟨M, hM⟩                                                      -- 取 M，使 (-∞,M] ⊆ V
    exact F.upward (h M) (fun x hx => hM _ hx)                                  -- 由 f(x)≤M 推出 f(x)∈V

theorem sides_iff {β : Type*} (f : ℝ → β) (a : ℝ)
    (G : BookFilter β) :                                                        -- 任意共同目标的双侧合并
    Approaches f (punctured a) G ↔
      Approaches f (leftNear a) G ∧ Approaches f (rightNear a) G := by
  constructor
  · intro h                                                                     -- 正向：分别提取左右成员关系
    exact ⟨fun V hV => ((punctured_iff_sides a _).1 (h V hV)).1,
      fun V hV => ((punctured_iff_sides a _).1 (h V hV)).2⟩
  · rintro ⟨hL, hR⟩ V hV                                                        -- 反向：给左右假设同一个 V
    exact (punctured_iff_sides a _).2 ⟨hL V hV, hR V hV⟩                        -- 合并两侧的原像成员关系

theorem upper_eventually_pos {α : Type*}                                        -- 正无穷保证最终严格正
    {f : α → ℝ} {F : BookFilter α}
    (hf : Approaches f F (upperFilter ℝ)) :
    Eventually F (fun x => 0 < f x) := by
  apply F.upward ((upper_iff _ _).1 hf 1)                                       -- 取阈值 1，留下点态蕴含
  intro x hx
  change 1 ≤ f x at hx                                                          -- 展开 hx：1≤f(x)
  change 0 < f x                                                                -- 子目标：f(x)>0
  linarith                                                                      -- 由 1≤f(x) 得严格正性

theorem neg_upper_iff {α : Type*}                                               -- 负号交换目标的无穷方向
    (f : α → ℝ) (F : BookFilter α) :
    Approaches (fun x => -f x) F (upperFilter ℝ) ↔
      Approaches f F (lowerFilter ℝ) := by
  rw [upper_iff, lower_iff]                                                     -- 两边改写为最终阈值要求
  constructor
  · intro h M
    apply F.upward (h (-M))
    intro x hx
    change -M ≤ -f x at hx                                                      -- 展开 hx：-M≤-f(x)
    change f x ≤ M                                                              -- 子目标：f(x)≤M
    linarith
  · intro h M
    apply F.upward (h (-M))
    intro x hx
    change f x ≤ -M at hx                                                       -- 反向展开 hx：f(x)≤-M
    change M ≤ -f x                                                             -- 子目标：M≤-f(x)
    linarith

theorem reciprocal_upper_zero {α : Type*} {f : α → ℝ} {F : BookFilter α}
    (hf : Approaches f F (upperFilter ℝ)) :                                     -- 正无穷的倒数趋于零
    Approaches (fun x => 1 / f x) F (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2                                                      -- 改证 |1/f(x)|<ε 最终成立
  intro ε hε                                                                    -- 任取 ε>0
  apply F.upward ((upper_iff _ _).1 hf (max 1 (2/ε)))
  intro x hx                                                                    -- hx：f(x)≥max(1,2/ε)
  have hpos : 0 < f x := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hx)
  have hlarge : 1/ε < f x := by                                                 -- 子目标：f(x)>1/ε
    have h := (le_max_right (1 : ℝ) (2/ε)).trans hx
    have : 0 < 1/ε := by positivity                                             -- positivity 核对倒数为正
    linarith [show 2/ε = 2*(1/ε) by ring]                                       -- 用 2/ε=2·(1/ε) 比较阈值
  have hsmall : 1 / f x < ε := (one_div_lt hpos hε).2 hlarge
  change |1/f x-0| < ε                                                          -- 恢复到 0 的距离子目标
  rw [sub_zero, abs_of_pos (one_div_pos.mpr hpos)]                              -- 用 z-0=z 与 |z|=z
  exact hsmall

theorem reciprocal_zero_upper {α : Type*} {f : α → ℝ} {F : BookFilter α}
    (hf : Approaches f F (neighborhoodFilter 0))
    (hp : Eventually F (fun x => 0 < f x)) :                                    -- 从正侧趋零才能得到正无穷
    Approaches (fun x => 1 / f x) F (upperFilter ℝ) := by
  apply (upper_iff _ _).2                                                       -- 改证 M≤1/f(x) 最终成立
  intro M                                                                       -- 任取目标阈值 M
  have hd : 0 < 1/(|M|+1) := by positivity                                      -- 选正距离界 1/(|M|+1)
  apply F.upward (F.inter_mem ((real_iff _ _ _).1 hf _ hd) hp)
  intro x hx                                                                    -- hx 同时保存小距离与正性
  have hp' : 0 < f x := hx.2                                                    -- 取交集中的 f(x)>0
  have hd' : |f x-0| < 1/(|M|+1) := hx.1                                        -- 取交集中的距离上界
  have hsmall : f x < 1/(|M|+1) := by                                           -- 子目标：分母为正且足够小
    simpa [abs_of_pos hp'] using hd'                                            -- 用 f(x)>0 去掉绝对值
  have hinv : |M|+1 < 1/f x := by                                               -- 取倒数后反转严格不等式
    have h := one_div_lt_one_div_of_lt hp' hsmall
    simpa using h
  exact (le_abs_self M).trans (by linarith)                                     -- 由 M≤|M| 推得目标阈值

theorem reciprocal_upper_right {α : Type*} {f : α → ℝ} {F : BookFilter α}
    (hf : Approaches f F (upperFilter ℝ)) :
    Approaches (fun x => 1/f x) F (rightNear 0) := by
  rintro V ⟨ε, hε, hV⟩                                                          -- 取 ε>0，使 (0,ε) ⊆ V
  apply F.upward (F.inter_mem                                                   -- 合并倒数趋零与分母正性
    ((real_iff _ _ _).1 (reciprocal_upper_zero hf) ε hε)
    (upper_eventually_pos hf))
  intro x hx
  have hpos : 0 < f x := hx.2                                                   -- 取交集中的分母正性
  have hrec : 0 < 1/f x := one_div_pos.mpr hpos                                 -- 正分母保证倒数严格正
  exact hV hx.1 hrec                                                            -- 倒数进入 (0,ε)，故属于 V

theorem square_upper :                                                          -- x趋于正无穷时x²趋于正无穷
    Approaches (fun x : ℝ => x^2) (upperFilter ℝ) (upperFilter ℝ) := by
  apply (upper_iff _ _).2                                                       -- 改证 x²≥M 最终成立
  intro M
  refine ⟨max 1 M, ?_⟩                                                          -- 选取阈值max(1,M)
  intro x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx                                -- 阈值的第一部分保证 x≥1
  have hxM : M ≤ x := (le_max_right _ _).trans hx                               -- 阈值的第二部分保证 x≥M
  have : 0 ≤ (x-1)*x := mul_nonneg (by linarith) (by linarith)
  change M ≤ x^2                                                                -- 子目标：M≤x²
  nlinarith                                                                     -- 由 x(x-1)≥0 得 x²≥x≥M

theorem square_lower :                                                          -- x趋于负无穷时x²仍趋于正无穷
    Approaches (fun x : ℝ => x^2) (lowerFilter ℝ) (upperFilter ℝ) := by
  have h := approaches_comp neg_atBot square_upper                              -- 先取负号，再复合平方增长
  simpa using h                                                                 -- 用 (-x)²=x² 识别复合函数

theorem inverse_square_both :                                                   -- 去心双侧的1/x²趋于正无穷
    Approaches (fun x : ℝ => 1/x^2) (punctured 0) (upperFilter ℝ) := by
  apply (upper_iff _ _).2                                                       -- 改证 M≤1/x² 最终成立
  intro M
  refine ⟨min 1 (1/(|M|+1)), by positivity, ?_⟩                                 -- 选半径 min(1,1/(|M|+1))
  intro x hx hne                                                                -- hx 为距离界，hne 排除 0
  change |x-0| < min 1 (1/(|M|+1)) at hx
  rw [sub_zero] at hx
  change M ≤ 1/x^2                                                              -- 当前目标：倒数超过 M
  have hx0 : 0 < |x| := abs_pos.mpr hne                                         -- 用 x≠0 得 |x|>0
  have hx1 : |x| < 1 := by simpa using (lt_of_lt_of_le hx (min_le_left _ _))
  have hxM : |x| < 1/(|M|+1) := by
    simpa using (lt_of_lt_of_le hx (min_le_right _ _))
  have hs : 0 < x^2 := sq_pos_of_ne_zero hne                                    -- 保证倒数比较的分母为正
  have hsq : x^2 < 1/(|M|+1) := by                                              -- 先证平方小于所选倒数界
    have : |x|^2 < |x| := by nlinarith                                          -- 由 0<|x|<1 得 |x|²<|x|
    nlinarith [sq_abs x]                                                        -- 用 |x|²=x² 连接平方估计
  have hi := one_div_lt_one_div_of_lt hs hsq                                    -- 对正数取倒数，反转大小
  have : |M|+1 < 1/x^2 := by simpa using hi                                     -- 化简 1/(1/(|M|+1))
  exact (le_abs_self M).trans (by linarith)                                     -- 由 M≤|M| 得 M≤1/x²

noncomputable def joinExample (x : ℝ) : ℝ :=                                    -- 左支x+1，右支1-x，中心值另定
  if x < 0 then x+1 else if x = 0 then 7 else 1-x

theorem join_left :                                                             -- 分段函数左侧趋于1
    Approaches joinExample (leftNear 0) (neighborhoodFilter 1) := by
  apply (real_iff _ _ _).2
  intro ε hε
  refine ⟨ε, hε, ?_⟩                                                            -- 选半径 δ=ε
  intro x hx hneg
  change |x-0| < ε at hx
  change x < 0 at hneg                                                          -- 左侧源给出 x<0
  simpa [joinExample, hneg] using hx                                            -- 选 x+1 分支，用 (x+1)-1=x

theorem join_right :                                                            -- 分段函数右侧趋于1
    Approaches joinExample (rightNear 0) (neighborhoodFilter 1) := by
  apply (real_iff _ _ _).2
  intro ε hε
  refine ⟨ε, hε, ?_⟩                                                            -- 选半径 δ=ε
  intro x hx hpos
  change |x-0| < ε at hx
  change 0 < x at hpos                                                          -- 右侧源给出 x>0
  have hne : x ≠ 0 := ne_of_gt hpos                                             -- 排除中心值 7 所在分支
  change |joinExample x-1| < ε
  rw [joinExample, ite_eq_right (not_lt.mpr (le_of_lt hpos)), ite_eq_right hne]
  have he : (1-x)-1 = -x := by ring                                             -- ring 核对右支减 1 等于 -x
  simpa [he, abs_neg] using hx                                                  -- 用 |(1-x)-1|=|-x|=|x|

theorem join_limit :                                                            -- 合并两个单侧极限得到去心极限
    Approaches joinExample (punctured 0) (neighborhoodFilter 1) :=
  (sides_iff _ _ _).2 ⟨join_left, join_right⟩                                   -- 两侧同趋于 1，合并去心极限

theorem horizontal_rational :                                                   -- (2x+1)/(x+1)在正无穷趋于2
    Approaches (fun x : ℝ => (2*x+1)/(x+1))
      (upperFilter ℝ) (neighborhoodFilter 2) := by
  apply (real_iff _ _ _).2                                                      -- 目标：到 2 的距离最终小于 ε
  intro ε hε
  refine ⟨max 1 (2/ε), ?_⟩                                                      -- 选源阈值 max(1,2/ε)
  intro x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxM : 2/ε ≤ x := (le_max_right _ _).trans hx
  have hd : 0 < x+1 := by linarith                                              -- 分母正，因此非零
  have he : (2*x+1)/(x+1)-2 = -(1/(x+1)) := by field_simp; ring
  have hb : 1/ε < x+1 := by                                                     -- 转为正分母的下界子目标
    have : 0 < 1/ε := by positivity
    linarith [show 2/ε = 2*(1/ε) by ring]                                       -- 用 x≥2/ε 与 ε>0 比较
  have hs : 1/(x+1) < ε := (one_div_lt hd hε).2 hb                              -- 正分母下，把下界转为倒数界
  change |(2*x+1)/(x+1)-2| < ε
  rw [he, abs_neg, abs_of_pos (one_div_pos.mpr hd)]                             -- 用距离等于 1/(x+1)
  exact hs

theorem oblique_residual :                                                      -- x+1+1/x与斜线x+1的差趋于零
    Approaches (fun x : ℝ => (x+1+1/x)-(x+1))
      (upperFilter ℝ) (neighborhoodFilter 0) := by
  have hi : Approaches (fun x : ℝ => x) (upperFilter ℝ) (upperFilter ℝ) :=
    approaches_id _                                                             -- 恒等函数保持正无穷趋近
  simpa only [add_sub_cancel_left] using reciprocal_upper_zero hi

theorem upper_mathlib_iff {α : Type*}                                           -- 本书上尾目标对应Mathlib的atTop
    (f : α → ℝ) (F : BookFilter α) :
    Approaches f F (upperFilter ℝ) ↔
      Filter.Tendsto f (toMathlib F) Filter.atTop := by
  rw [approaches_mathlib_iff, toMathlib_upper_real]                             -- 转换趋近关系及上尾目标

theorem right_mathlib_iff                                                       -- 右极限对应 Mathlib 的右侧源
    (f : ℝ → ℝ) (a b : ℝ) :
    Approaches f (rightNear a) (neighborhoodFilter b) ↔
      Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds b) := by
  rw [approaches_mathlib_iff]                                                   -- 先转换为 Mathlib 的 Tendsto
  change Filter.Tendsto f (toMathlib (nearWithin a (Set.Ioi a)))
      (toMathlib (neighborhoodFilter b)) ↔ _
  rw [toMathlib_nearWithin,
    Ch03.toMathlib_neighborhood]                                           -- 转换右侧源与有限目标

end Ch04Infinity
