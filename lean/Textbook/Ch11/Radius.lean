import Textbook.Ch11.Audit

namespace Ch11

open Filter Set
open scoped Topology

theorem radiusSet_zero (c : ℕ → ℝ) : 0 ∈ radiusSet c := by
  refine ⟨le_rfl,(positive_series_summable (fun n => by positivity)).2 ?_⟩
  rw [← summable_nat_add_iff 1]
  simp [pow_succ]

theorem le_convergenceRadius {c : ℕ → ℝ} {r : ℝ} (hr : r ∈ radiusSet c) :
    (r : WithTop ℝ) ≤ convergenceRadius c := by
  unfold convergenceRadius
  split
  · exact WithTop.coe_le_coe.mpr (le_csSup ‹_› hr)
  · exact le_top

theorem radius_has_majorant {c : ℕ → ℝ} {r : ℝ} (hr : (r : WithTop ℝ) < convergenceRadius c) :
    ∃ ρ ∈ radiusSet c, r < ρ := by
  by_contra! h
  have hb : BddAbove (radiusSet c) := ⟨r, h⟩
  rw [convergenceRadius, ite_eq_left hb] at hr
  exact (not_lt_of_ge (csSup_le ⟨0,radiusSet_zero c⟩ h)) (WithTop.coe_lt_coe.mp hr)

theorem power_series_uniform {c : ℕ → ℝ} {a r : ℝ} (hr : 0 ≤ r)
    (h : (r : WithTop ℝ) < convergenceRadius c) :
    (∀ x, |x-a| ≤ r → AbsolutelyConvergent (powerSeriesTerm c a x)) ∧
    TendstoUniformlyOn (fun N x => partialSum (powerSeriesTerm c a x) N)
      (fun x => ∑' n, powerSeriesTerm c a x n) atTop {x | |x-a| ≤ r} := by
  obtain ⟨ρ,⟨hρ,hs⟩,hrρ⟩ := radius_has_majorant h
  exact weierstrass_test (M := fun n => |c n| * ρ^n) (fun n => by positivity) hs
    (fun n x hx => by
      change |x-a| ≤ r at hx
      rw [powerSeriesTerm, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hx.trans hrρ.le) n) (abs_nonneg _))

theorem power_series_inside {c : ℕ → ℝ} {a x : ℝ}
    (hx : ((|x-a| : ℝ) : WithTop ℝ) < convergenceRadius c) :
    AbsolutelyConvergent (powerSeriesTerm c a x) :=
  (power_series_uniform (a := a) (abs_nonneg _) hx).1 x le_rfl

theorem power_series_outside {c : ℕ → ℝ} {a x : ℝ}
    (hx : convergenceRadius c < ((|x-a| : ℝ) : WithTop ℝ)) :
    ¬ SeriesConverges (powerSeriesTerm c a x) := by
  classical
  rintro ⟨L,hL⟩
  have hb : BddAbove (radiusSet c) := by
    by_contra h
    simp [convergenceRadius,h] at hx
  have h0 : 0 ≤ sSup (radiusSet c) := le_csSup hb (radiusSet_zero c)
  have hx' : sSup (radiusSet c) < |x-a| := by
    simpa [convergenceRadius,hb] using hx
  obtain ⟨r,hr,hrx⟩ := exists_between hx'
  have hr0 : 0 ≤ r := h0.trans hr.le
  have hx0 : 0 < |x-a| := hr0.trans_lt hrx
  have ht := term_tendsto_zero hL
  obtain ⟨D,hD⟩ := Metric.isBounded_range_iff.mp (Metric.isBounded_range_of_tendsto _ ht)
  let C := D + |powerSeriesTerm c a x 0|
  have hCb (n : ℕ) : |c n| *|x-a|^n ≤ C := by
    have he := (dist_triangle (powerSeriesTerm c a x n) (powerSeriesTerm c a x 0) 0).trans
      (add_le_add_left (hD n 0) _)
    simpa [C, Real.dist_eq, powerSeriesTerm, abs_mul, abs_pow] using he
  have hs : Summable (fun n => |c n| * r^n) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) ?_
      ((summable_geometric_of_lt_one (div_nonneg hr0 hx0.le)
        ((div_lt_one hx0).2 hrx)).mul_left C)
    intro n
    calc
      |c n| * r^n = (|c n| * |x-a|^n) * (r/|x-a|)^n := by
        rw [div_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hCb n) (by positivity)
  have hm : r ∈ radiusSet c := ⟨hr0, (positive_series_summable (fun n => by positivity)).2 hs⟩
  exact (not_lt_of_ge (le_csSup hb hm)) hr

end Ch11
