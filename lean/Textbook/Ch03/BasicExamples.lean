import Textbook.Ch03.Approach

namespace Ch03BasicExamples
open Ch02 Ch03 Ch03Approach

theorem reciprocal_sequence_from_definition :           -- 由定义证明1/(n+1)趋于零
    Approaches (fun n : ℕ => 1 / ((n : ℝ) + 1))
      tailFilter (neighborhoodFilter 0) := by
  apply (sequence_iff _ _).2                            -- 将极限目标转为绝对值判定
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩                                        -- 选取N，留下其余证明任务
  intro n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 1 / ε < (n : ℝ) + 1 := by linarith        -- 由索引大小关系比较两个分母
  have hsmall : 1 / ((n : ℝ) + 1) < ε := by
    have h := one_div_lt_one_div_of_lt (one_div_pos.mpr hε) hden
    simpa using h                                       -- 化简后使用已有证明
  rw [sub_zero, abs_of_pos (by positivity : 0 < 1 / ((n : ℝ) + 1))]  -- 用z-0=z及z>0时|z|=z化简
  exact hsmall

theorem reciprocal_atTop_from_definition :              -- 由定义证明正无穷处1/(x+1)趋于零
    Approaches (fun x : ℝ => 1 / (x + 1))
      (upperFilter ℝ) (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  refine ⟨1 / ε, ?_⟩                                    -- 选取1 / ε，留下其余证明任务
  intro x hx
  have hden : 1 / ε < x + 1 := by linarith
  have hxpos : 0 < x + 1 := lt_trans (one_div_pos.mpr hε) hden
  have hsmall : 1 / (x + 1) < ε := by
    have h := one_div_lt_one_div_of_lt (one_div_pos.mpr hε) hden
    simpa using h                                       -- 化简后使用已有证明
  change |1 / (x + 1) - 0| < ε
  rw [sub_zero, abs_of_pos (one_div_pos.mpr hxpos)]     -- 用z-0=z及z>0时|z|=z化简
  exact hsmall

theorem reciprocal_atBot_from_definition :              -- 由定义证明负无穷处1/(1+|x|)趋于零
    Approaches (fun x : ℝ => 1 / (1 + |x|))
      (lowerFilter ℝ) (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  refine ⟨-(1 / ε), ?_⟩                                 -- 选取-(1 / ε)，留下其余证明任务
  intro x hx
  have habs : 1 / ε ≤ |x| := by
    calc                                                -- 开始逐步等式或不等式链
      1 / ε ≤ -x := by linarith
      _ ≤ |x| := neg_le_abs x
  have hden : 1 / ε < 1 + |x| := by linarith
  have hsmall : 1 / (1 + |x|) < ε := by
    have h := one_div_lt_one_div_of_lt (one_div_pos.mpr hε) hden
    simpa using h                                       -- 化简后使用已有证明
  have hpos : 0 < 1 / (1 + |x|) := by positivity
  change |1 / (1 + |x|) - 0| < ε
  rw [sub_zero, abs_of_pos hpos]                        -- 用z-0=z及z>0时|z|=z化简
  exact hsmall

theorem identity_within_from_definition :               -- 恒等函数沿集合内邻域趋近零
    Approaches (fun x : ℝ => x)
      (nearWithin 0 (Set.Ici 0)) (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  refine ⟨ε, hε, ?_⟩                                    -- 选取ε，留下其余证明任务
  intro x hx _
  exact hx

theorem quotient_punctured_from_definition (a : ℝ) :    -- 去心处的平方差商趋于2a
    Approaches (fun x : ℝ => (x^2-a^2)/(x-a))
      (punctured a) (neighborhoodFilter (2*a)) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  refine ⟨ε, hε, ?_⟩                                    -- 选取ε，留下其余证明任务
  intro x hx hne
  change |x-a| < ε at hx
  change x ≠ a at hne
  change |(x^2-a^2)/(x-a)-2*a| < ε
  have hden : x-a ≠ 0 := sub_ne_zero.mpr hne
  have heq : (x^2-a^2)/(x-a) = x+a := by
    field_simp [hden]                                   -- 利用非零条件消去分母
    ring                                                -- 核对多项式恒等式
  rw [heq]                                              -- 使用heq中的等式或等价式改写
  simpa [show x+a-2*a = x-a by ring] using hx           -- 化简后使用已有证明

noncomputable def restrictedExample (x : ℝ) : ℝ := if 0 ≤ x then x else 1  -- 定义分段函数

theorem restricted_example_limit :                      -- 分段函数沿非负半轴趋于零
    Approaches restrictedExample
      (within (neighborhoodFilter 0) (Set.Ici 0)) (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2                              -- 将极限目标转为绝对值判定
  intro ε hε
  change ∃ δ > 0, ∀ x : ℝ, |x - 0| < δ →
    x ∈ Set.Ici (0 : ℝ) → |restrictedExample x - 0| < ε
  refine ⟨ε, hε, ?_⟩                                    -- 选取ε，留下其余证明任务
  intro x hx hS
  have hnonneg : 0 ≤ x := hS
  simpa [restrictedExample, hnonneg] using hx           -- 化简后使用已有证明

end Ch03BasicExamples
