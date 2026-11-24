import Mathlib

namespace Ch01

-- BEGIN division
example : (1 : ℕ) / 2 = 0 := by                  -- 自然数除法取整数商
  decide

example : (1 : ℝ) / 0 = 0 := by                  -- 实数库约定除以0的值为0
  simp

theorem real_div_self (x : ℝ) (hx : x ≠ 0) :    -- 非零实数除以自身等于1
    x / x = 1 := by
  exact div_self hx                             -- 使用非零假设hx
-- END division

-- BEGIN function
def nextNat (n : ℕ) : ℕ := n + 1                -- 自然数的后继函数
def Positive (n : ℕ) : Prop := 0 < n             -- 自然数为正的谓词

example : nextNat 2 = 3 := by
  rfl                                           -- 两侧计算后都是3

example : Positive 3 := by
  change 0 < (3 : ℕ)                             -- 展开谓词Positive
  decide                                        -- 判定自然数不等式0 < 3
-- END function

-- BEGIN conjunction
theorem swap_and (P Q : Prop) :                 -- 交换合取中的两个命题
    P ∧ Q → Q ∧ P := by
  intro h                                       -- h : P ∧ Q，目标Q ∧ P
  constructor                                   -- 分别证明Q和P
  · exact h.2                                   -- h的第二部分是Q的证明
  · exact h.1                                   -- h的第一部分是P的证明
-- END conjunction

-- BEGIN quantifiers
theorem threshold_example :                    -- 选择阈值100后保持下界
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 100 ≤ n := by
  refine ⟨100, ?_⟩                              -- 取N = 100
  intro n hn                                    -- hn : 100 ≤ n
  exact hn
-- END quantifiers

-- BEGIN sets
def Upper100 : Set ℕ := {n | 100 ≤ n}            -- 自然数中不小于100的点集

theorem upper100_mem (n : ℕ) :                  -- 成员命题就是定义中的不等式
    n ∈ Upper100 ↔ 100 ≤ n := by
  rfl

theorem inter_left (A B : Set ℕ) :              -- 交集包含在左边的集合内
    A ∩ B ⊆ A := by
  intro n hn                                    -- hn : n ∈ A ∩ B
  exact hn.1                                    -- 取出n ∈ A的证明
-- END sets

-- BEGIN proof_term
theorem swap_and_term (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h =>
    let swapped : Q ∧ P := ⟨h.2, h.1⟩
    swapped
-- END proof_term

-- BEGIN record
structure ClosedBounds where                    -- 两个实数端点及其顺序证明
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper

def unitBounds : ClosedBounds where              -- 构造端点为0和1的记录
  lower := 0
  upper := 1
  ordered := zero_le_one
-- END record

-- BEGIN vacuous
theorem contradictory_premise (x : ℝ) (hneg : x < 0) (hpos : 0 < x) :
    x = 1 := by                                  -- 相互矛盾的前提可推出任意结论
  linarith
-- END vacuous

end Ch01
