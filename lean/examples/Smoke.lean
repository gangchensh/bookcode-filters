import Theories.Eventually

open FilterCalculus

#eval 1 + 1                                             -- 计算表达式的值
#check EventuallyNat.and

example : EventuallyNat (fun n => 100 ≤ n) := by
  refine ⟨100, ?_⟩                                      -- 选取100，留下其余证明任务
  intro n hn
  exact hn
