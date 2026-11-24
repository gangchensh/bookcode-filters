import Textbook.Ch11.Radius
import Textbook.Ch11.SeriesExamples

namespace Ch11

open Filter Set
open scoped Topology

private theorem radius_eq_of_bounds {c : ℕ → ℝ} {R : ℝ}
    (hu : ∀ r ∈ radiusSet c, r ≤ R)
    (hl : ∀ r, 0 ≤ r → r < R → r ∈ radiusSet c) :
    convergenceRadius c = (R : WithTop ℝ) := by
  have hb : BddAbove (radiusSet c) := ⟨R, hu⟩
  have hz : 0 ≤ sSup (radiusSet c) := le_csSup hb (radiusSet_zero c)
  have he : sSup (radiusSet c) = R := by
    apply le_antisymm (csSup_le ⟨0,radiusSet_zero c⟩ hu)
    by_contra! h
    obtain ⟨r,hr,hr'⟩ := exists_between h
    exact (not_lt_of_ge (le_csSup hb (hl r (hz.trans hr.le) hr'))) hr
  simp [convergenceRadius,hb,he]

theorem geometric_radius : convergenceRadius (fun _ => 1) = (1:WithTop ℝ) := by
  apply radius_eq_of_bounds
  · intro r hr
    by_contra! h
    have h' : 1 ≤ |r| := le_trans h.le (le_abs_self r)
    exact geometric_nonconvergence h' (by simpa using hr.2)
  · intro r hr₀ hr
    exact ⟨hr₀, by simpa using (show SeriesConverges (fun n => r^n) from
      ⟨_,geometric_series r (by rwa [abs_of_nonneg hr₀])⟩)⟩

theorem exponential_radius :
    convergenceRadius (fun n => 1/(n.factorial:ℝ)) = ⊤ := by
  have hall (r : ℝ) (hr : 0 ≤ r) : r ∈ radiusSet (fun n => 1/(n.factorial:ℝ)) := by
    refine ⟨hr,(positive_series_summable (fun _ => by positivity)).2 ?_⟩
    apply (Real.summable_pow_div_factorial r).congr
    intro n
    rw [abs_of_nonneg (by positivity : 0 ≤ 1/(n.factorial:ℝ))]
    ring
  have hb : ¬ BddAbove (radiusSet (fun n => 1/(n.factorial:ℝ))) := by
    rintro ⟨B,hB⟩
    have h := hB (hall (max 0 B + 1) (by positivity))
    change max 0 B + 1 ≤ B at h
    linarith [le_max_right (0:ℝ) B]
  unfold convergenceRadius
  rw [ite_eq_right hb]

theorem factorial_radius : convergenceRadius (fun n => (n.factorial:ℝ)) = (0:WithTop ℝ) := by
  apply radius_eq_of_bounds
  · intro r hr
    by_contra! h
    have hs := (positive_series_summable (fun n => by positivity)).1 hr.2
    have hs' : Summable (fun n : ℕ => (n.factorial:ℝ)*r^n) := by
      simpa only [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hs
    apply not_summable_of_ratio_norm_eventually_ge (r := 2) (by norm_num) ?_ ?_ hs'
    · exact (Eventually.of_forall fun n => ne_of_gt
        (norm_pos_iff.mpr (by positivity : (n.factorial:ℝ)*r^n ≠ 0))).frequently
    · obtain ⟨N,hN⟩ := exists_nat_gt (2/r)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnr : (2:ℝ) ≤ ((n:ℝ)+1)*r := by
        have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
        have h' := (div_lt_iff₀ h).1 hN
        nlinarith
      rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),
        Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
      calc
        _ ≤ (((n:ℝ)+1)*r)*((n.factorial:ℝ)*r^n) :=
          mul_le_mul_of_nonneg_right hnr (by positivity)
        _ = _ := by ring
  · intro r hr h
    exact (not_lt_of_ge hr h).elim

theorem polynomial_denominator_radius {R : ℝ} (hR : 0 < R) (k : ℕ) :
    convergenceRadius (fun n => 1/((n:ℝ)^k*R^n)) = (R:WithTop ℝ) := by
  apply radius_eq_of_bounds
  · intro r hr
    by_contra! h
    have hr₀ : 0 < r := hR.trans h
    let a := fun n : ℕ => |1/((n:ℝ)^k*R^n)| * r^n
    have hsum : Summable a :=
      (positive_series_summable (fun _ => by positivity)).1 hr.2
    let C := ∑' n, a n
    have hC (n : ℕ) : a n ≤ C := hsum.le_tsum n (fun _ _ => by positivity)
    have hq : ‖R/r‖ < 1 := by
      rw [Real.norm_of_nonneg (div_nonneg hR.le hr₀.le)]
      exact (div_lt_one hr₀).2 h
    have hmajor := (summable_pow_mul_geometric_of_norm_lt_one k hq).mul_left C
    have hb (n : ℕ) : (1:ℝ) ≤ C*((n+1:ℝ)^k*(R/r)^(n+1)) := by
      have hn : 0 < (n+1:ℝ) := by positivity
      calc
        _ = a (n+1)*((n+1:ℝ)^k*(R/r)^(n+1)) := by
          unfold a
          rw [abs_of_nonneg (by positivity),div_pow]
          push_cast
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hC _) (by positivity)
    have hone : Summable (fun _ : ℕ => (1:ℝ)) := by
      apply Summable.of_nonneg_of_le (fun _ => zero_le_one) hb
      have hm : Summable (fun n : ℕ => C*((n:ℝ)^k*(R/r)^n)) := hmajor
      simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).2 hm
    have ht := hone.tendsto_atTop_zero
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)
  · intro r hr h
    refine ⟨hr,(positive_series_summable (fun _ => by positivity)).2 ?_⟩
    rw [← summable_nat_add_iff 1]
    apply Summable.of_nonneg_of_le (fun _ => by positivity) ?_
    · exact (summable_nat_add_iff 1).2
        (summable_geometric_of_lt_one (div_nonneg hr hR.le) ((div_lt_one hR).2 h))
    · intro n
      have hn : 1 ≤ ((n+1:ℕ):ℝ)^k := one_le_pow₀ (by exact_mod_cast Nat.succ_pos n)
      have he : |1/(((n+1:ℕ):ℝ)^k*R^(n+1))| * r^(n+1) =
          (r/R)^(n+1)/((n+1:ℕ):ℝ)^k := by
        rw [abs_of_nonneg (by positivity),div_pow]
        have hv : 0 < R^(n+1) := by positivity
        have hv' : 0 < ((n+1:ℕ):ℝ)^k := zero_lt_one.trans_le hn
        field_simp
      exact he.trans_le (div_le_self (by positivity) hn)

end Ch11
