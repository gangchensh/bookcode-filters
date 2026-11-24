import Std

namespace FilterCalculus

/-- A property holds from some natural-number index onwards. -/
def EventuallyNat (P : Nat → Prop) : Prop :=            -- 定义自然数上的最终成立
  ∃ N : Nat, ∀ n : Nat, N ≤ n → P n                     -- 要求存在一个合适的见证

theorem EventuallyNat.and {P Q : Nat → Prop}            -- 最终成立对有限合取封闭
    (hP : EventuallyNat P) (hQ : EventuallyNat Q) :
    EventuallyNat (fun n => P n ∧ Q n) := by
  rcases hP with ⟨NP, hP⟩
  rcases hQ with ⟨NQ, hQ⟩
  refine ⟨max NP NQ, ?_⟩                                -- 选取max NP NQ，留下其余证明任务
  intro n hn
  constructor
  · exact hP n (Nat.le_trans (Nat.le_max_left NP NQ) hn)  -- 连接已有关系完成目标
  · exact hQ n (Nat.le_trans (Nat.le_max_right NP NQ) hn)  -- 连接已有关系完成目标

end FilterCalculus
