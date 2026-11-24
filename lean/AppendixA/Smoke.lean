import Std

#eval 1 + 1                                             -- 计算表达式的值
#check Nat

def EventuallyNat (P : Nat → Prop) : Prop :=            -- 定义自然数上的最终成立
  ∃ N : Nat, ∀ n : Nat, N ≤ n → P n                     -- 要求存在一个合适的见证

example : EventuallyNat (fun n => 100 ≤ n) := by
  refine ⟨100, ?_⟩                                      -- 选取100，留下其余证明任务
  intro n hn
  exact hn
