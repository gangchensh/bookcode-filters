import Textbook.Ch02.Filters

namespace Ch02

variable {α β γ : Type*} {F : BookFilter α}

theorem eventually_of_forall {P : α → Prop}             -- 由处处成立推出最终成立
    (h : ∀ x, P x) : Eventually F P := by               -- h：P处处成立；目标：P最终成立
  change {x | P x} ∈ F.sets
  have hset : {x | P x} = Set.univ := Set.eq_univ_of_forall h
  rw [hset]                                             -- 用hset：{x | P x}=全集替换目标中的集合
  exact F.univ_mem                                      -- 使用全空间性质

theorem eventually_mono {P Q : α → Prop}                -- 沿逐点蕴含传递最终成立
    (hP : Eventually F P) (hPQ : ∀ x, P x → Q x) :      -- hP：P沿F最终成立
    Eventually F Q := by
  exact F.upward hP hPQ                                 -- 使用滤子的向上封闭性

theorem eventually_and {P Q : α → Prop}                 -- 合并两个最终断言
    (hP : Eventually F P) (hQ : Eventually F Q) :       -- hP：P沿F最终成立
    Eventually F (fun x => P x ∧ Q x) := by
  exact F.inter_mem hP hQ                               -- 使用滤子的有限交性质

theorem eventually_and_iff {P Q : α → Prop} :           -- 最终合取的双向判定
    Eventually F (fun x => P x ∧ Q x) ↔                 -- 左边：P∧Q最终成立
      Eventually F P ∧ Eventually F Q := by             -- 右边：P、Q分别最终成立
  constructor                                           -- 拆分↔为两个方向；先证左→右
  · intro h                                             -- 正向：假设P∧Q最终成立
    constructor                                         -- 把正向结论分成P、Q两个子目标
    · exact eventually_mono h (fun x hx => hx.1)        -- 证明子目标：P最终成立
    · exact eventually_mono h (fun x hx => hx.2)        -- 证明子目标：Q最终成立
  · intro h                                             -- 反向：假设P、Q分别最终成立
    exact eventually_and h.1 h.2                        -- 合并两个假设，证明右→左

theorem eventually_mp {P Q : α → Prop}                  -- 在共同区域使用蕴含
    (hPQ : Eventually F (fun x => P x → Q x))           -- hPQ：蕴含P x→Q x最终成立
    (hP : Eventually F P) : Eventually F Q := by        -- hP：P沿F最终成立
  apply eventually_mono (eventually_and hPQ hP)         -- 先合并最终成立的假设
  intro x hx
  exact hx.1 hx.2                                       -- 用当前点的蕴含和前提推出结论

theorem eventually_three {P Q R : α → Prop}             -- 合并三个最终断言
    (hP : Eventually F P) (hQ : Eventually F Q)         -- hP、hQ：P、Q分别沿F最终成立
    (hR : Eventually F R) :                             -- hR：R沿F最终成立
    Eventually F (fun x => P x ∧ Q x ∧ R x) := by       -- 目标：P∧Q∧R沿F最终成立
  exact eventually_and hP (eventually_and hQ hR)        -- 先合并Q与R，再与P合并

def EventuallyEq (F : BookFilter α) (f g : α → β) : Prop :=  -- 定义两个函数最终相等
  Eventually F (fun x => f x = g x)                     -- f与g沿F最终相等

theorem eventuallyEq_refl (f : α → β) : EventuallyEq F f f := by  -- 最终相等的自反性
  apply eventually_of_forall                            -- 归结为逐点证明f x=f x
  intro x
  rfl                                                   -- 等式两端都是f x

theorem eventuallyEq_symm {f g : α → β}                 -- 最终相等的对称性
    (hfg : EventuallyEq F f g) : EventuallyEq F g f := by  -- 由f =^F g证明g =^F f
  apply eventually_mono hfg                             -- 在f x=g x的最终区域交换等式两端
  intro x hx
  exact hx.symm                                         -- 把f x=g x反向写成g x=f x

theorem eventuallyEq_trans {f g h : α → β}              -- 最终相等的传递性
    (hfg : EventuallyEq F f g) (hgh : EventuallyEq F g h) :  -- hfg：f =^F g；hgh：g =^F h
    EventuallyEq F f h := by                            -- 目标：f =^F h
  apply eventually_mono (eventually_and hfg hgh)        -- 合并f=g与g=h的最终区域
  intro x hx
  exact hx.1.trans hx.2                                 -- 由f x=g x、g x=h x得到f x=h x

theorem eventuallyEq_congr {f g : α → β}                -- 将相等值代入同一函数
    (hfg : EventuallyEq F f g) (φ : β → γ) :            -- hfg：f与g沿F最终相等
    EventuallyEq F (fun x => φ (f x)) (fun x => φ (g x)) := by
  apply eventually_mono hfg                             -- 转为共同区域上的逐点推理
  intro x hx
  exact congrArg φ hx

theorem eventually_subst {f g : α → β} {P : β → Prop}   -- 用最终相等替换性质
    (hfg : EventuallyEq F f g)                          -- hfg：f =^F g
    (hP : Eventually F (fun x => P (f x))) :            -- hP：P(f x)沿F最终成立
    Eventually F (fun x => P (g x)) := by               -- 目标：P(g x)沿F最终成立
  apply eventually_mono (eventually_and hfg hP)         -- 合并f x=g x与P(f x)的最终区域
  intro x hx
  rw [← hx.1]                                           -- 由hx.1：f x=g x，把g x换成f x
  exact hx.2                                            -- 使用共同区域内的P(f x)

def changedAtZero (n : ℕ) : ℕ :=                        -- 只修改数列的第零项
  if n = 0 then 100 else n                              -- 仅在第零项取值 100

theorem changedAtZero_eventuallyEq :                    -- 修改第零项不改变最终相等
    EventuallyEq tailFilter changedAtZero (fun n => n) := by
  change Ch02Eventually.EventuallyNat _
  refine ⟨1, ?_⟩                                        -- 选取1，留下其余证明任务
  intro n hn
  have hne : n ≠ 0 := by omega
  simp [changedAtZero, hne]                             -- 化简后使用已有证明

def EventuallyLE (F : BookFilter α) (f g : α → ℝ) : Prop :=  -- 定义最终不等式
  Eventually F (fun x => f x ≤ g x)                     -- f≤g沿F最终成立

theorem eventuallyLE_trans {f g h : α → ℝ}              -- 最终不等式的传递性
    (hfg : EventuallyLE F f g) (hgh : EventuallyLE F g h) :  -- hfg：f≤g沿F最终成立
    EventuallyLE F f h := by
  apply eventually_mono (eventually_and hfg hgh)        -- 先合并最终成立的假设
  intro x hx
  exact le_trans hx.1 hx.2                              -- 连接已有关系完成目标

theorem eventuallyLE_antisymm {f g : α → ℝ}             -- 双向不等式推出最终相等
    (hfg : EventuallyLE F f g) (hgf : EventuallyLE F g f) :  -- hfg：f≤g沿F最终成立
    EventuallyEq F f g := by
  apply eventually_mono (eventually_and hfg hgf)        -- 先合并最终成立的假设
  intro x hx
  exact le_antisymm hx.1 hx.2

theorem eventuallyLE_add {f g u v : α → ℝ}              -- 相加两个最终不等式
    (hfg : EventuallyLE F f g) (huv : EventuallyLE F u v) :  -- hfg：f≤g沿F最终成立
    EventuallyLE F (fun x => f x + u x) (fun x => g x + v x) := by
  apply eventually_mono (eventually_and hfg huv)        -- 先合并最终成立的假设
  intro x hx
  exact add_le_add hx.1 hx.2

theorem eventually_abs_add_bound {f g : α → ℝ}          -- 由两个上界估计和的绝对值
    (hf : Eventually F (fun x => |f x| ≤ 1))
    (hg : Eventually F (fun x => |g x| ≤ 2)) :
    Eventually F (fun x => |f x + g x| ≤ 3) := by
  apply eventually_mono (eventually_and hf hg)          -- 先合并最终成立的假设
  intro x hx
  calc                                                  -- 开始逐步等式或不等式链
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ 1 + 2 := add_le_add hx.1 hx.2
    _ = 3 := by norm_num

theorem not_eventually_false (hF : IsProper F) :        -- 恒假不可能最终成立
    ¬ Eventually F (fun _ => False) := by
  exact hF                                              -- IsProper F正是排除恒假最终成立

theorem eventually_exists {P : α → Prop}                -- 非平凡性给出满足点
    (hF : IsProper F) (hP : Eventually F P) : ∃ x, P x := by  -- hF排除空集；hP给出P的最终区域
  classical                                             -- 启用经典逻辑工具
  by_contra hnone                                       -- 反设hnone：¬∃ x, P x
  apply hF                                              -- 应用IsProper F；子目标：恒假沿F最终成立
  apply eventually_mono hP                              -- 由P最终成立，归结为逐点P x→False
  intro x hx                                            -- 固定x，假设hx：P x
  exact hnone ⟨x, hx⟩                                   -- ⟨x,hx⟩与不存在满足点的hnone矛盾

theorem eventuallyEq_iff_mathlib (f g : α → β) :        -- 本书最终相等等价于Mathlib的最终相等
    EventuallyEq F f g ↔ f =ᶠ[toMathlib F] g := by
  rfl                                                   -- 两边展开定义后相同

theorem eventuallyLE_iff_mathlib (f g : α → ℝ) :        -- 本书最终不等式等价于Mathlib版本
    EventuallyLE F f g ↔ f ≤ᶠ[toMathlib F] g := by
  rfl                                                   -- 两边展开定义后相同

end Ch02
