import Textbook.Ch02.Tail

namespace Ch02Eventually

def above100 : Set ℕ :=
  {n | 100 ≤ n}                                         -- 以成员谓词描述集合

def above100Explicit : Set ℕ :=
  Set.ofPred (fun n : ℕ => 100 ≤ n)                     -- 由成员谓词构造自然数集合

example : above100 = above100Explicit := by
  rfl                                                   -- 两边展开定义后相同

local notation "A₁₀₀" => above100                       -- 声明本节使用的数学记号

example : 105 ∈ A₁₀₀ := by
  change 100 ≤ 105
  omega                                                 -- 核对自然数或整数算术

local notation:50 n:50 " ∈ₙ " A:50 => Set.Mem A n       -- 声明本节使用的数学记号
local infixl:70 " ∩ₙ " => Set.inter                     -- 声明本节使用的数学记号

example (A B : Set ℕ) (n : ℕ) :
    n ∈ₙ (A ∩ₙ B) ↔ n ∈ A ∧ n ∈ B := by
  rfl                                                   -- 两边展开定义后相同

macro "setN{" x:ident " | " p:term "}" : term =>        -- 声明数学记号的语法
  `(Set.ofPred (fun $x:ident : ℕ => $p))                -- 把记号翻译为函数表达式

example : setN{n | 100 ≤ n} = above100 := by
  rfl                                                   -- 两边展开定义后相同

example : 105 ∈ above100 := by
  change 100 ≤ 105
  omega                                                 -- 核对自然数或整数算术

example : 99 ∉ above100 := by
  change ¬ (100 ≤ 99)
  omega                                                 -- 核对自然数或整数算术

example : 99 ∉ above100 := by
  intro h
  change 100 ≤ 99 at h
  omega                                                 -- 核对自然数或整数算术

example : (∅ : Set ℕ) = {_n : ℕ | False} := by
  rfl                                                   -- 两边展开定义后相同

example (n : ℕ) : n ∉ (∅ : Set ℕ) := by
  intro h
  change False at h
  exact h

example : tail 1000 ⊆ tail 100 := by
  intro n hn
  change 100 ≤ n
  change 1000 ≤ n at hn
  omega                                                 -- 核对自然数或整数算术

theorem set_inter_comm (A B : Set ℕ) :                  -- 证明集合交的交换律
    A ∩ B = B ∩ A := by
  ext n                                                 -- 转为逐元素比较成员关系
  constructor
  · intro hn
    rcases hn with ⟨hA, hB⟩
    exact ⟨hB, hA⟩
  · intro hn
    rcases hn with ⟨hB, hA⟩
    exact ⟨hA, hB⟩

def tailSets : Set (Set ℕ) :=
  {A | ∃ N : ℕ, tail N ⊆ A}                             -- 以成员谓词描述集合

theorem mem_tailSets_iff (A : Set ℕ) :                  -- 属于尾集集合族等价于包含某个尾集
    A ∈ tailSets ↔ EventualSet A := by
  rfl                                                   -- 两边展开定义后相同

end Ch02Eventually
