import Textbook.Ch09.Tagged

namespace Ch09

open Set

private noncomputable def halfAndUniformPoints (n : ℕ) (i : Fin (n+3)) : ℝ :=
  if i.val = 0 then 0 else 1/2 + ((i.val:ℝ)-1)/(2*((n:ℝ)+1))

/-- The first interval has width 1/2, while the other n+1 intervals are uniform. -/
noncomputable def fixedHalfPartition (n : ℕ) : TaggedPartition 0 1 where
  n := n+1
  points := halfAndUniformPoints n
  first := by simp [halfAndUniformPoints]
  last := by
    simp only [halfAndUniformPoints, Fin.val_last, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  increasing := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hj : j.val ≠ 0 := by omega
    have hp : 0 < (2:ℝ)*((n:ℝ)+1) := by positivity
    by_cases hi : i.val = 0
    · simp only [halfAndUniformPoints,hi,hj,if_true,if_false]
      have hcast : (1:ℝ) ≤ j.val := by exact_mod_cast (show 1 ≤ j.val by omega)
      linarith [div_nonneg (sub_nonneg.mpr hcast) hp.le]
    · simp only [halfAndUniformPoints,hi,hj,if_false]
      apply add_lt_add_right
      apply div_lt_div_of_pos_right _ hp
      exact sub_lt_sub_right (by exact_mod_cast hij') 1
  tag := fun i => halfAndUniformPoints n i.castSucc
  tag_mem := by
    intro i
    refine ⟨le_rfl,?_⟩
    have hn : 0 < (2:ℝ)*((n:ℝ)+1) := by positivity
    by_cases hi : i.val = 0
    · simp [halfAndUniformPoints,hi]
    · simp only [halfAndUniformPoints,Fin.val_castSucc,Fin.val_succ,hi,Nat.succ_ne_zero,
        Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,Nat.cast_add,Nat.cast_one]
      apply add_le_add_right
      apply div_le_div_of_nonneg_right _ hn.le
      linarith

theorem fixed_half_mesh (n : ℕ) :
    (fixedHalfPartition n).n+1 = n+2 ∧ (fixedHalfPartition n).mesh = 1/2 := by
  let P := fixedHalfPartition n
  have hw (i : Fin (P.n+1)) : P.width i = if i.val = 0 then 1/2 else 1/(2*((n:ℝ)+1)) := by
    change halfAndUniformPoints n i.succ - halfAndUniformPoints n i.castSucc = _
    by_cases hi : i.val = 0
    · simp [halfAndUniformPoints,hi]
    · simp only [halfAndUniformPoints,Fin.val_castSucc,Fin.val_succ,hi,Nat.succ_ne_zero,
        Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,Nat.cast_add,Nat.cast_one]
      field_simp
      <;> ring
  refine ⟨rfl,le_antisymm ?_ ?_⟩
  · apply Finset.sup'_le
    intro i _
    rw [hw]
    split
    · rfl
    · apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)*((n:ℝ)+1))).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have h₀ : P.width 0 = 1/2 := by simpa using hw 0
    rw [← h₀]
    exact Finset.le_sup' P.width (Finset.mem_univ (0 : Fin (P.n+1)))

end Ch09
