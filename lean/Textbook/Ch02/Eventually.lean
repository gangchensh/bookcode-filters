import Std

namespace Ch02Eventually

def EventuallyNat (P : Nat → Prop) : Prop :=            -- 定义自然数上的最终成立
  ∃ N : Nat, ∀ n : Nat, N ≤ n → P n                     -- 要求存在一个合适的见证

example :
   EventuallyNat (fun n => 100 ≤ n) := by
  refine ⟨100, ?_⟩                                      -- 选取100，留下其余证明任务
  intro n hn
  exact hn

theorem EventuallyNat.and                               -- 最终成立对有限合取封闭
    {P Q : Nat → Prop}
    (hP : EventuallyNat P)
    (hQ : EventuallyNat Q) :
    EventuallyNat (fun n => P n ∧ Q n) := by
  rcases hP with ⟨NP, hNP⟩
  rcases hQ with ⟨NQ, hNQ⟩
  refine ⟨max NP NQ, ?_⟩                                -- 选取max NP NQ，留下其余证明任务
  intro n hn
  constructor
  · apply hNP n
    omega                                               -- 核对自然数或整数算术
  · apply hNQ n
    omega                                               -- 核对自然数或整数算术


theorem EventuallyNat.mono                              -- 将较强断言传到较弱断言
    {P Q : Nat → Prop}
    (hP : EventuallyNat P)
    (hPQ : ∀ n, P n → Q n) :
    EventuallyNat Q := by
  rcases hP with ⟨N, hN⟩
  refine ⟨N, ?_⟩                                        -- 选取N，留下其余证明任务
  intro n hn
  exact hPQ n (hN n hn)

example (u : Nat → Nat)
    (h : EventuallyNat (fun n => 1000 < u n)) :
    EventuallyNat (fun n => 100 < u n) := by
  apply EventuallyNat.mono h
  intro n hn
  omega                                                 -- 核对自然数或整数算术

example (k : Nat) : EventuallyNat (fun n => k ≤ n) := by
  refine ⟨k, ?_⟩                                        -- 选取k，留下其余证明任务
  intro n hn
  exact hn

example : ¬ EventuallyNat (fun n => ∀ k : Nat, k ≤ n) := by
  intro h
  rcases h with ⟨N, hN⟩
  have hbad : N + 1 ≤ N := hN N (Nat.le_refl N) (N + 1)
  omega                                                 -- 核对自然数或整数算术

example (P : Nat → Prop) (h : ∀ n, P n) :
    EventuallyNat P := by
  refine ⟨0, ?_⟩                                        -- 选取0，留下其余证明任务
  intro n hn
  exact h n

end Ch02Eventually
