import Mathlib
import Textbook.Ch02.Eventually

namespace Ch02Eventually

def tail (N : ℕ) : Set ℕ :=                             -- 定义自然数尾集
  {n | N ≤ n}                                           -- 以成员谓词描述集合


-- The eventual subsets of the natural numbers.
def EventualSet (A : Set ℕ) : Prop :=                   -- 定义包含尾集的集合
  EventuallyNat (fun n => n ∈ A)                        -- 集合 A 从某个阈值起包含所有自然数

theorem EventualSet.univ : EventualSet Set.univ := by   -- 自然数全集包含一个尾集
  refine ⟨0, ?_⟩                                        -- 选取0，留下其余证明任务
  intro n hn
  exact Set.mem_univ n                                  -- 使用全空间性质

theorem EventualSet.inter {A B : Set ℕ}                 -- 两个最终集合的交仍包含尾集
    (hA : EventualSet A) (hB : EventualSet B) :
    EventualSet (A ∩ B) := by
  exact EventuallyNat.and hA hB

theorem EventualSet.mono {A B : Set ℕ}                  -- 包含尾集的集合向上封闭
    (hA : EventualSet A) (hAB : A ⊆ B) :
    EventualSet B := by
  exact EventuallyNat.mono hA (fun n hn => hAB hn)

-- The library statement, specialized to natural-number indices.
example (P : ℕ → Prop) :
    (∀ᶠ n in Filter.atTop, P n) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P n := by               -- 要求存在一个合适的见证
  exact Filter.eventually_atTop

theorem eventuallyNat_iff_mathlib (P : ℕ → Prop) :      -- 本书最终成立等价于Mathlib自然数版本
    EventuallyNat P ↔ (∀ᶠ n in Filter.atTop, P n) := by
  exact Filter.eventually_atTop.symm

-- Start at n + 1 so that the denominator is positive even at n = 0.
theorem eventually_reciprocal (ε : ℝ) (hε : 0 < ε) :    -- 为倒数估计选择阈值
    EventuallyNat (fun n => 1 / ((n : ℝ) + 1) < ε) := by
  rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩                                        -- 选取N，留下其余证明任务
  intro n hn
  have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by           -- 由索引大小关系比较两个分母
    exact_mod_cast Nat.add_le_add_right hn 1            -- 将自然数不等式转成实数不等式
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by  -- 证明后一个倒数不大于阈值处的倒数
    apply one_div_le_one_div_of_le
    · positivity                                        -- 验证表达式的正性
    · exact hden
  exact lt_of_le_of_lt hle hN

-- The same proof with automated monotonicity bookkeeping.
theorem eventually_reciprocal_short (ε : ℝ) (hε : 0 < ε) :  -- 证明倒数的最终估计
    EventuallyNat (fun n => 1 / ((n : ℝ) + 1) < ε) := by
  rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩                                        -- 选取N，留下其余证明任务
  intro n hn
  apply lt_of_le_of_lt ?_ hN
  gcongr                                                -- 把倒数比较化为分母的比较

example : ∀ᶠ n : ℕ in Filter.atTop, 100 ≤ n := by
  exact Filter.eventually_ge_atTop 100

example {P Q : ℕ → Prop}
    (hP : ∀ᶠ n in Filter.atTop, P n)
    (hQ : ∀ᶠ n in Filter.atTop, Q n) :
    ∀ᶠ n in Filter.atTop, P n ∧ Q n := by
  exact hP.and hQ

end Ch02Eventually
