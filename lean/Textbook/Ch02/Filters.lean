import Textbook.Ch02.Tail
import Textbook.Ch02.Neighborhoods

namespace Ch02

structure BookFilter (α : Type*) where                  -- 声明数据与证明字段
  sets : Set (Set α)                                    -- 指定滤子的成员集合族
  univ_mem : Set.univ ∈ sets                            -- 全空间属于集合族
  inter_mem : ∀ {A B}, A ∈ sets → B ∈ sets → A ∩ B ∈ sets  -- 验证有限交封闭性
  upward : ∀ {A B}, A ∈ sets → A ⊆ B → B ∈ sets         -- 验证向上封闭性

def IsProper {α : Type*} (F : BookFilter α) : Prop :=   -- 空集不属于滤子的条件
  (∅ : Set α) ∉ F.sets

def tailFilter : BookFilter ℕ where                     -- 构造自然数尾集滤子
  sets := {A | Ch02Eventually.EventualSet A}                 -- 指定滤子的成员集合族
  univ_mem := Ch02Eventually.EventualSet.univ                -- 全空间属于集合族
  inter_mem := by                                       -- 验证有限交封闭性
    intro A B hA hB
    exact Ch02Eventually.EventualSet.inter hA hB             -- 用第1章的交集性质合并hA、hB
  upward := by                                          -- 验证向上封闭性
    intro A B hA hAB
    exact Ch02Eventually.EventualSet.mono hA hAB             -- 用向上封闭性由hA推出B属于集合族

theorem tailFilter_proper : IsProper tailFilter := by   -- 自然数尾集滤子不含空集
  intro h
  rcases h with ⟨N, hN⟩
  exact hN N (Nat.le_refl N)

def principal {α : Type*} (S : Set α) : BookFilter α where  -- 构造固定集合的主滤子
  sets := {A | S ⊆ A}                                   -- 指定滤子的成员集合族
  univ_mem := Set.subset_univ S                         -- 全空间属于集合族
  inter_mem := by                                       -- 验证有限交封闭性
    intro A B hA hB x hx
    exact ⟨hA hx, hB hx⟩
  upward := by                                          -- 验证向上封闭性
    intro A B hA hAB x hx
    exact hAB (hA hx)

theorem principal_proper {α : Type*} {S : Set α}        -- 非空集合生成的主滤子不含空集
    (hS : S.Nonempty) : IsProper (principal S) := by
  rcases hS with ⟨x, hx⟩
  intro h
  exact h hx

def pointFilter {α : Type*} (a : α) : BookFilter α :=   -- 构造单点主滤子
  principal {a}                                         -- 用单点集合生成主滤子

theorem mem_pointFilter {α : Type*} (a : α) (A : Set α) :  -- 属于点主滤子等价于集合包含该点
    A ∈ (pointFilter a).sets ↔ a ∈ A := by
  change ({a} ⊆ A) ↔ a ∈ A
  exact Set.singleton_subset_iff

def neighborhoodFilter (a : ℝ) : BookFilter ℝ where     -- 构造实数邻域滤子
  sets := {U | Ch02Neighborhoods.IsNeighborhoodR a U}           -- 指定滤子的成员集合族
  univ_mem := by                                        -- 全空间属于集合族
    refine ⟨1, by norm_num, ?_⟩                         -- 选取1，留下其余证明任务
    intro x hx
    exact Set.mem_univ x                                -- 使用全空间性质
  inter_mem := by                                       -- 验证有限交封闭性
    intro A B hA hB
    rcases hA with ⟨ε, hε, hA⟩
    rcases hB with ⟨δ, hδ, hB⟩
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩                  -- 选取min ε δ，留下其余证明任务
    intro x hx
    constructor
    · exact hA (lt_of_lt_of_le hx (min_le_left ε δ))
    · exact hB (lt_of_lt_of_le hx (min_le_right ε δ))
  upward := by                                          -- 验证向上封闭性
    intro A B hA hAB
    rcases hA with ⟨ε, hε, hA⟩
    exact ⟨ε, hε, fun x hx => hAB (hA hx)⟩

theorem neighborhoodFilter_proper (a : ℝ) :             -- 实数邻域滤子不含空集
    IsProper (neighborhoodFilter a) := by
  intro h
  rcases h with ⟨ε, hε, hU⟩
  have ha : a ∈ Ch02Neighborhoods.epsNeighborhood a ε := by
    change |a - a| < ε
    simpa using hε                                      -- 化简后使用已有证明
  exact hU ha

def improperFilter (α : Type*) : BookFilter α where     -- 构造包含所有子集的滤子
  sets := Set.univ                                      -- 指定滤子的成员集合族
  univ_mem := Set.mem_univ _                            -- 全空间属于集合族
  inter_mem := by                                       -- 验证有限交封闭性
    intro A B hA hB
    exact Set.mem_univ _                                -- 使用全空间性质
  upward := by                                          -- 验证向上封闭性
    intro A B hA hAB
    exact Set.mem_univ _                                -- 使用全空间性质

theorem empty_mem_improper (α : Type*) :                -- 空集属于退化滤子
    (∅ : Set α) ∈ (improperFilter α).sets := by         -- 目标：空集属于退化滤子
  exact Set.mem_univ _                                  -- 退化滤子接受所有集合，包括空集

def Eventually {α : Type*} (F : BookFilter α)           -- 定义沿滤子的最终成立
    (P : α → Prop) : Prop :=
  {x | P x} ∈ F.sets                                    -- 以成员谓词描述集合

theorem eventually_tail_iff (P : ℕ → Prop) :            -- 尾集滤子最终成立等价于阈值判定
    Eventually tailFilter P ↔ Ch02Eventually.EventuallyNat P := by
  rfl                                                   -- 两边展开定义后相同

def toMathlib {α : Type*} (F : BookFilter α) : Filter α where  -- 转换为Mathlib滤子
  sets := F.sets                                        -- 指定滤子的成员集合族
  univ_sets := F.univ_mem                               -- 提供全空间性质的证明
  sets_of_superset := by                                -- 提供向上封闭的证明
    intro A B hA hAB
    exact F.upward hA hAB                               -- 使用滤子的向上封闭性
  inter_sets := by                                      -- 提供有限交性质的证明
    intro A B hA hB
    exact F.inter_mem hA hB                             -- 使用滤子的有限交性质

theorem toMathlib_tail : toMathlib tailFilter = Filter.atTop := by  -- 本书尾集滤子转换后等于Mathlib atTop
  ext A                                                 -- 转为逐元素比较成员关系
  exact Filter.eventually_atTop.symm

theorem toMathlib_principal {α : Type*} (S : Set α) :   -- 本书主滤子转换后等于Mathlib principal
    toMathlib (principal S) = Filter.principal S := by
  ext A                                                 -- 转为逐元素比较成员关系
  rfl                                                   -- 两边展开定义后相同

theorem toMathlib_neighborhood (a : ℝ) :                -- 本书邻域滤子转换后等于Mathlib nhds
    toMathlib (neighborhoodFilter a) = nhds a := by
  ext U                                                 -- 转为逐元素比较成员关系
  exact Ch02Neighborhoods.isNeighborhoodR_iff_mathlib a U

end Ch02
