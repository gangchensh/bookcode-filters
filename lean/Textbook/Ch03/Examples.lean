import Textbook.Ch03.LimitRules

namespace Ch03Examples
open Ch02 Ch03 Ch03Approach Ch03Rules

-- A concrete failure of composition when the middle filters do not match.
noncomputable def outer (y : ℝ) : ℝ := if y = 0 then 1 else 0

theorem outer_punctured_zero :
    Approaches outer (punctured 0) (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2
  intro eps heps
  refine ⟨1, by norm_num, ?_⟩
  intro x hx hne
  change x ≠ 0 at hne
  simpa [outer, hne] using heps                 -- 去心源中外层函数恒为零

theorem punctured_proper (a : ℝ) : IsProper (punctured a) := by
  rintro ⟨d, hd, hU⟩
  have hx : |a + d / 2 - a| < d := by
    rw [show a + d / 2 - a = d / 2 by ring,
      abs_of_pos (half_pos hd)]
    linarith
  exact hU hx (by change a + d / 2 ≠ a; linarith)

theorem inner_zero :
    Approaches (fun _ : ℝ => 0) (punctured 0) (neighborhoodFilter 0) :=
  const_limit _ 0

theorem composition_is_one :
    Approaches (fun x : ℝ => outer (0 * x))
      (punctured 0) (neighborhoodFilter 1) := by
  simpa [outer] using (const_limit (punctured 0) 1)

theorem composition_not_zero :
    ¬ Approaches (fun x : ℝ => outer (0 * x))
      (punctured 0) (neighborhoodFilter 0) := by
  intro h
  have heq : (0 : ℝ) = 1 :=
    real_limit_unique (punctured_proper 0) h composition_is_one
  norm_num at heq                              -- 非平凡源不能同时趋于0和1

end Ch03Examples
