import Textbook.Ch01.Language

namespace Ch01

abbrev Predicate (X : Type*) := X → Prop

def Universal (X : Type*) (P : X → Prop) : Prop := ∀ x, P x

def Existential (X : Type*) (P : X → Prop) : Prop := ∃ x, P x

theorem division_semantics :
    (1 : ℕ) / 2 = 0 ∧ 0 < (1 : ℝ) / 2 ∧
      (∀ x : ℝ, x / 0 = 0) ∧
      (∀ u v w : ℝ, (u + v) / w = u / w + v / w) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro x
    simp
  · intro u v w
    exact add_div u v w

theorem div_self_without_nonzero_false : ¬ (∀ x : ℝ, x / x = 1) := by
  intro h
  have hzero := h 0
  norm_num at hzero

end Ch01
