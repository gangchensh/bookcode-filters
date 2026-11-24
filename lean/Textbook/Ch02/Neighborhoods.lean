import Mathlib

open scoped Topology

namespace Ch02Neighborhoods

def epsNeighborhood (a ε : ℝ) : Set ℝ :=                -- 定义以a为中心的ε-邻域
  {x | |x - a| < ε}                                     -- 以成员谓词描述集合

def IsNeighborhoodR                                     -- 一般邻域包含基本邻域
    (a : ℝ) (U : Set ℝ) : Prop :=
  ∃ ε > 0, epsNeighborhood a ε ⊆ U                      -- 要求存在一个合适的见证

def LocallyHolds                                        -- 定义在一点附近成立
    (a : ℝ) (P : ℝ → Prop) : Prop :=
  IsNeighborhoodR a {x | P x}                           -- 满足 P 的点组成 a 的一个邻域

def puncturedEpsNeighborhood
    (a ε : ℝ) : Set ℝ :=
  {x | 0 < |x - a| ∧ |x - a| < ε}                       -- 以成员谓词描述集合


theorem IsNeighborhoodR.inter {a : ℝ} {U V : Set ℝ}     -- 两个邻域的交仍是邻域
    (hU : IsNeighborhoodR a U) (hV : IsNeighborhoodR a V) :
    IsNeighborhoodR a (U ∩ V) := by
  rcases hU with ⟨ε₁, hε₁, hU⟩
  rcases hV with ⟨ε₂, hε₂, hV⟩
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩                -- 选取min ε₁ ε₂，留下其余证明任务
  intro x hx
  change |x - a| < min ε₁ ε₂ at hx
  constructor
  · apply hU
    exact lt_of_lt_of_le hx (min_le_left _ _)
  · apply hV
    exact lt_of_lt_of_le hx (min_le_right _ _)

theorem epsNeighborhood_eq_ball (a ε : ℝ) :             -- 基本邻域等于实数上的开球
    epsNeighborhood a ε = Metric.ball a ε := by
  ext x                                                 -- 转为逐元素比较成员关系
  simp [epsNeighborhood, Metric.mem_ball, Real.dist_eq]  -- 化简后使用已有证明

theorem isNeighborhoodR_iff_mathlib (a : ℝ) (U : Set ℝ) :  -- 本书邻域判定等价于Mathlib邻域成员
    IsNeighborhoodR a U ↔ U ∈ nhds a := by
  simpa only [IsNeighborhoodR, epsNeighborhood_eq_ball] using  -- 化简后使用已有证明
    (Metric.mem_nhds_iff (s := U) (x := a)).symm

theorem locallyHolds_iff_mathlib (a : ℝ) (P : ℝ → Prop) :  -- 局部成立等价于沿Mathlib邻域最终成立
    LocallyHolds a P ↔ ∀ᶠ x in nhds a, P x := by
  exact isNeighborhoodR_iff_mathlib a {x | P x}

end Ch02Neighborhoods
