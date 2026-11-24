import Textbook.Ch03.StandardFilters

namespace Ch03Approach
open Ch02 Ch03

def Approaches {α β : Type*} (f : α → β)                -- 用原像定义趋近关系
    (F : BookFilter α) (G : BookFilter β) : Prop :=     -- F、G指定输入与输出的趋近方式
  ∀ V, V ∈ G.sets → f ⁻¹' V ∈ F.sets                    -- G的每个成员V的原像都属于F

theorem map_members_iff {α β : Type*} (f : α → β)       -- Mathlib像滤子的成员由原像判定
    (F : BookFilter α) (V : Set β) :                    -- F是源滤子，V是目标空间的候选集合
    V ∈ Filter.map f (toMathlib F) ↔ f ⁻¹' V ∈ F.sets := by  -- V属于像滤子↔V的原像属于F
  rfl                                                   -- 展开map后都是原像属于F

theorem approaches_mathlib_iff {α β : Type*}                                     -- 本书趋近关系等价于Mathlib的Tendsto
    (f : α → β)
    (F : BookFilter α) (G : BookFilter β) :                                     -- F、G指定输入与输出的趋近方式
    Approaches f F G ↔ Filter.Tendsto f (toMathlib F) (toMathlib G) := by
  rfl                                                                           -- 两边展开定义后相同

theorem real_iff {α : Type*} (f : α → ℝ)                -- 趋于实数b的绝对值判定
    (F : BookFilter α) (b : ℝ) :                        -- F指定输入趋近方式，b是目标实数
    Approaches f F (neighborhoodFilter b) ↔             -- 左边：f沿F趋于b
      ∀ ε > 0, Eventually F (fun x => |f x - b| < ε) := by  -- 右边：任给ε>0，|f x-b|<ε最终成立
  constructor                                           -- 分两向；先由趋近关系推出基本邻域要求
  · intro h ε hε                                        -- 任取ε>0，h给出目标邻域的原像
    exact h {y | |y - b| < ε} ⟨ε, hε, fun y hy => hy⟩   -- 把基本邻域N_ε(b)交给趋近假设h
  · intro h V hV                                        -- 反向：任取b的邻域V
    rcases hV with ⟨ε, hε, hV⟩
    exact F.upward (h ε hε) (fun x hx => hV hx)         -- 把基本邻域的原像扩大到V的原像

theorem sequence_iff (u : ℕ → ℝ) (b : ℝ) :              -- 数列极限的阈值判定
    Approaches u tailFilter (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |u n - b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem punctured_real_iff (f : ℝ → ℝ) (a b : ℝ) :      -- 去心极限的半径判定
    Approaches f (punctured a) (neighborhoodFilter b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, |x-a| < δ → x ≠ a → |f x-b| < ε := by
  rw [real_iff]                                         -- 用real_iff：趋于b↔任给ε>0最终满足绝对值界
  rfl                                                   -- 两边展开定义后相同

theorem double_limit (a : ℝ) :                          -- 证明二倍函数的有限极限
    Approaches (fun x : ℝ => 2*x)
      (neighborhoodFilter a) (neighborhoodFilter (2*a)) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  refine ⟨ε/2, half_pos hε, ?_⟩                         -- 选取ε/2，留下其余证明任务
  intro x hx
  have hdist : |2*x-2*a| = 2*|x-a| := by
    rw [show 2*x-2*a = 2*(x-a) by ring, abs_mul]        -- 用2*x-2*a=2*(x-a)及|uv|=|u||v|
    norm_num                                            -- 核对具体数值运算
  change |2*x-2*a| < ε
  change |x-a| < ε/2 at hx
  rw [hdist]                                            -- 用hdist：|2*x-2*a|=2*|x-a|改写
  linarith                                              -- 核对线性实数不等式

theorem reciprocal_sequence :                           -- 证明倒数数列趋于零
    Approaches (fun n : ℕ => 1/((n : ℝ)+1))
      tailFilter (neighborhoodFilter 0) := by
  apply (sequence_iff _ _).2                            -- 将极限目标转为绝对值判定
  intro ε hε
  rcases Ch02Eventually.eventually_reciprocal ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩                                        -- 选取N，留下其余证明任务
  intro n hn
  rw [sub_zero, abs_of_pos (by positivity)]             -- 用z-0=z及z>0时|z|=z化简
  exact hN n hn

theorem double_atTop :                                  -- 二倍函数趋于正无穷
    Approaches (fun x : ℝ => 2*x) (upperFilter ℝ) (upperFilter ℝ) := by
  rintro V ⟨b, hb⟩
  refine ⟨b/2, ?_⟩                                      -- 选取b/2，留下其余证明任务
  intro x hx
  exact hb (2*x) (by linarith)

theorem neg_atBot :                                     -- 负号交换两种无穷方向
    Approaches (fun x : ℝ => -x) (lowerFilter ℝ) (upperFilter ℝ) := by
  rintro V ⟨b, hb⟩
  refine ⟨-b, ?_⟩                                       -- 选取-b，留下其余证明任务
  intro x hx
  exact hb (-x) (by linarith)

theorem reciprocal_right_atTop :                        -- 右侧倒数趋于正无穷
    Approaches (fun x : ℝ => 1/x) (rightNear 0) (upperFilter ℝ) := by
  rintro V ⟨b, hb⟩
  refine ⟨1/(|b|+1), by positivity, ?_⟩                 -- 选取1/(|b|+1)，留下其余证明任务
  intro x hx hxpos
  change 0 < x at hxpos
  change |x-0| < 1/(|b|+1) at hx
  have hxlt : x < 1/(|b|+1) := by
    simpa [abs_of_pos hxpos] using hx                   -- 化简后使用已有证明
  have hrecip : |b|+1 < 1/x := by
    have h := one_div_lt_one_div_of_lt hxpos hxlt
    simpa using h                                       -- 化简后使用已有证明
  exact hb (1/x) (by have h := le_abs_self b; linarith)

theorem approaches_sides_iff {β : Type*} (f : ℝ → β)    -- 双侧极限与两侧的对应
    (a : ℝ) (G : BookFilter β) :
    Approaches f (punctured a) G ↔
      Approaches f (leftNear a) G ∧ Approaches f (rightNear a) G := by
  constructor
  · intro h
    constructor
    · intro V hV
      exact ((punctured_iff_sides a _).1 (h V hV)).1
    · intro V hV
      exact ((punctured_iff_sides a _).1 (h V hV)).2
  · rintro ⟨hL, hR⟩ V hV
    exact (punctured_iff_sides a _).2 ⟨hL V hV, hR V hV⟩

end Ch03Approach
