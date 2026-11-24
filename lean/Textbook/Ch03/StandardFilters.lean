import Textbook.Ch02.Logic

namespace Ch03
open Ch02

def upperFilter (α : Type*) [LinearOrder α] [Nonempty α]
    : BookFilter α where                                                        -- 构造有序空间的上尾滤子
  sets := {A | ∃ b, ∀ x, b ≤ x → x ∈ A}                                         -- 指定滤子的成员集合族
  univ_mem := by                                                                -- 全空间属于集合族
    rcases ‹Nonempty α› with ⟨b⟩
    exact ⟨b, fun x hx => Set.mem_univ x⟩                                       -- 使用全空间性质
  inter_mem := by                                                               -- 验证有限交封闭性
    rintro A B ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨max b c, fun x hx =>
      ⟨hb x (le_trans (le_max_left b c) hx),                                    -- 由 x 不小于最大值推出第一个断言
       hc x (le_trans (le_max_right b c) hx)⟩⟩                                  -- 同样推出第二个断言并合并
  upward := by                                                                  -- 验证向上封闭性
    rintro A B ⟨b, hb⟩ hAB
    exact ⟨b, fun x hx => hAB (hb x hx)⟩

def lowerFilter (α : Type*) [LinearOrder α] [Nonempty α] : BookFilter α where  -- 构造有序空间的下尾滤子
  sets := {A | ∃ b, ∀ x, x ≤ b → x ∈ A}                 -- 指定滤子的成员集合族
  univ_mem := by                                        -- 全空间属于集合族
    rcases ‹Nonempty α› with ⟨b⟩
    exact ⟨b, fun x hx => Set.mem_univ x⟩               -- 使用全空间性质
  inter_mem := by                                       -- 验证有限交封闭性
    rintro A B ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨min b c, fun x hx =>
      ⟨hb x (le_trans hx (min_le_left b c)),            -- 由 x 不大于最小值推出第一个断言
       hc x (le_trans hx (min_le_right b c))⟩⟩          -- 同样推出第二个断言并合并
  upward := by                                          -- 验证向上封闭性
    rintro A B ⟨b, hb⟩ hAB
    exact ⟨b, fun x hx => hAB (hb x hx)⟩

theorem upper_proper (α : Type*) [LinearOrder α] [Nonempty α] :  -- 非空线性序上的上尾滤子不含空集
    IsProper (upperFilter α) := by
  rintro ⟨b, hb⟩
  exact hb b le_rfl

theorem lower_proper (α : Type*) [LinearOrder α] [Nonempty α] :  -- 非空线性序上的下尾滤子不含空集
    IsProper (lowerFilter α) := by
  rintro ⟨b, hb⟩
  exact hb b le_rfl

theorem eventually_upper_real_iff (P : ℝ → Prop) :           -- 上尾最终成立等价于存在阈值
    Eventually (upperFilter ℝ) P ↔ ∃ b, ∀ x, b ≤ x → P x := Iff.rfl  -- 两边展开定义后相同

theorem eventually_lower_iff (P : ℝ → Prop) :           -- 下尾最终成立等价于存在上阈值
    Eventually (lowerFilter ℝ) P ↔ ∃ b, ∀ x, x ≤ b → P x := Iff.rfl  -- 两边展开定义后相同

theorem nat_lower_iff (P : ℕ → Prop) :                  -- 自然数下尾最终成立等价于P在0处成立
    Eventually (lowerFilter ℕ) P ↔ P 0 := by
  constructor
  · rintro ⟨b, hb⟩
    exact hb 0 (Nat.zero_le b)
  · intro h
    refine ⟨0, ?_⟩                                      -- 选取0，留下其余证明任务
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    simpa [hn0] using h                                 -- 化简后使用已有证明

def within {α : Type*} (F : BookFilter α) (S : Set α) : BookFilter α where  -- 将滤子限制到给定集合
  sets := {A | {x | x ∈ S → x ∈ A} ∈ F.sets}            -- 指定滤子的成员集合族
  univ_mem := by                                        -- 全空间属于集合族
    apply F.upward F.univ_mem
    intro x hx hS
    exact Set.mem_univ x                                -- 使用全空间性质
  inter_mem := by                                       -- 验证有限交封闭性
    intro A B hA hB
    apply F.upward (F.inter_mem hA hB)
    intro x hx hS
    exact ⟨hx.1 hS, hx.2 hS⟩
  upward := by                                          -- 验证向上封闭性
    intro A B hA hAB
    apply F.upward hA
    intro x hx hS
    exact hAB (hx hS)

theorem eventually_within_iff {α : Type*} (F : BookFilter α)  -- 限制后最终成立等价于原滤子上的蕴含
    (S : Set α) (P : α → Prop) :
    Eventually (within F S) P ↔ Eventually F (fun x => x ∈ S → P x) := Iff.rfl  -- 两边展开定义后相同

theorem eventually_to_within {α : Type*} {F : BookFilter α}  -- 最终成立在限制滤子上仍成立
    {S : Set α} {P : α → Prop} (h : Eventually F P) :
    Eventually (within F S) P := by
  exact F.upward h (fun x hx hS => hx)                  -- 使用滤子的向上封闭性

theorem within_mono_set {α : Type*} {F : BookFilter α}  -- 缩小限制集合仍保持最终成立
    {S T : Set α} {P : α → Prop} (hST : T ⊆ S)
    (h : Eventually (within F S) P) : Eventually (within F T) P := by
  exact F.upward h (fun x hx hT => hx (hST hT))         -- 使用滤子的向上封闭性

def nearWithin (a : ℝ) (S : Set ℝ) : BookFilter ℝ :=    -- 构造集合内邻域滤子
  within (neighborhoodFilter a) S                       -- 把邻域滤子限制在集合 S 上

def punctured (a : ℝ) : BookFilter ℝ := nearWithin a {x | x ≠ a}  -- 排除中心点的邻域滤子
def rightNear (a : ℝ) : BookFilter ℝ := nearWithin a {x | a < x}  -- 限制到中心点右侧
def leftNear (a : ℝ) : BookFilter ℝ := nearWithin a {x | x < a}  -- 限制到中心点左侧

theorem eventually_nearWithin_iff (a : ℝ) (S : Set ℝ) (P : ℝ → Prop) :  -- 集合内最终成立的半径判定
    Eventually (nearWithin a S) P ↔
      ∃ δ > 0, ∀ x, |x - a| < δ → x ∈ S → P x := Iff.rfl  -- 两边展开定义后相同

theorem punctured_ne (a : ℝ) : Eventually (punctured a) (fun x => x ≠ a) := by  -- 去心邻域中x最终不等于a
  exact ⟨1, zero_lt_one, fun x hx hne => hne⟩

theorem right_proper (a : ℝ) : IsProper (rightNear a) := by  -- 右侧邻域滤子非平凡
  intro hempty
  rcases hempty with ⟨δ, hδ, hU⟩
  have hdist : |a + δ / 2 - a| < δ := by
    rw [show a + δ / 2 - a = δ / 2 by ring, abs_of_pos (half_pos hδ)]  -- 用a+δ/2-a=δ/2及|δ/2|=δ/2
    linarith                                            -- 核对线性实数不等式
  exact hU hdist (by change a < a + δ / 2; linarith)

theorem left_proper (a : ℝ) : IsProper (leftNear a) := by  -- 左侧邻域滤子非平凡
  rintro ⟨δ, hδ, hU⟩
  have hdist : |a - δ / 2 - a| < δ := by
    rw [show a - δ / 2 - a = -(δ / 2) by ring, abs_neg,  -- 用等式改写相应表达式
      abs_of_pos (half_pos hδ)]                         -- 用半径的一半为正化简绝对值
    linarith                                            -- 核对线性实数不等式
  exact hU hdist (by change a - δ / 2 < a; linarith)

theorem punctured_iff_sides (a : ℝ) (P : ℝ → Prop) :    -- 去心成立等价于两侧成立
    Eventually (punctured a) P ↔
      Eventually (leftNear a) P ∧ Eventually (rightNear a) P := by
  constructor
  · intro h
    constructor
    · exact within_mono_set (fun x hx => ne_of_lt hx) h
    · exact within_mono_set (fun x hx => ne_of_gt hx) h
  · rintro ⟨⟨δ, hδ, hL⟩, ⟨ε, hε, hR⟩⟩
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩                  -- 选取min δ ε，留下其余证明任务
    intro x hx hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hL (lt_of_lt_of_le hx (min_le_left δ ε)) hlt
    · exact hR (lt_of_lt_of_le hx (min_le_right δ ε)) hgt

theorem toMathlib_upper_real : toMathlib (upperFilter ℝ) = Filter.atTop := by  -- 实数上尾滤子转换后等于Mathlib atTop
  ext A                                                 -- 转为逐元素比较成员关系
  exact Filter.eventually_atTop.symm

theorem toMathlib_neighborhood (a : ℝ) : toMathlib (neighborhoodFilter a) = nhds a := by  -- 本书邻域滤子转换后等于Mathlib nhds
  ext A                                                 -- 转为逐元素比较成员关系
  change Ch02Neighborhoods.IsNeighborhoodR a A ↔ A ∈ nhds a
  rw [Metric.mem_nhds_iff]                              -- 使用Metric.mem_nhds_iff中的等式或等价式改写
  rfl                                                   -- 两边展开定义后相同

theorem upperFilter_nat_eq_tail : upperFilter ℕ = tailFilter := by  -- 自然数上尾滤子就是尾集滤子
  rfl                                                   -- 两边展开定义后相同

theorem toMathlib_lower_real : toMathlib (lowerFilter ℝ) = Filter.atBot := by  -- 实数下尾滤子转换后等于Mathlib atBot
  ext A                                                 -- 转为逐元素比较成员关系
  exact Filter.eventually_atBot.symm

theorem toMathlib_within {α : Type*} (F : BookFilter α) (S : Set α) :  -- 限制滤子转换后等于F与主滤子的下确界
    toMathlib (within F S) = toMathlib F ⊓ Filter.principal S := by
  ext U                                                 -- 转为逐元素比较成员关系
  exact (Filter.mem_inf_principal (f := toMathlib F)
    (s := U) (t := S)).symm

theorem toMathlib_nearWithin (a : ℝ) (S : Set ℝ) :      -- 集合内邻域转换后等于Mathlib nhdsWithin
    toMathlib (nearWithin a S) = nhdsWithin a S := by
  change toMathlib (within (neighborhoodFilter a) S) = nhdsWithin a S
  rw [toMathlib_within, toMathlib_neighborhood]         -- 按括号内列出的等式或等价式改写
  rfl                                                   -- 两边展开定义后相同

end Ch03
