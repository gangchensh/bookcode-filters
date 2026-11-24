import Textbook.Ch11.Audit
import Textbook.Ch09.Monotone
import Textbook.Ch10.Methods

namespace Ch11

open Filter MeasureTheory Set
open scoped Topology Interval

theorem integral_test_local_tagged {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 1))
    {T : ℝ} (hT : 1 < T) :
    Ch09.HasTaggedIntegral f 1 T (∫ x in (1:ℝ)..T, f x) :=
  Ch09.antitone_tagged_integral hT (hf.mono Icc_subset_Ici_self)

theorem integral_test {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 1))
    (hn : ∀ x ≥ 1, 0 ≤ f x) :
    (SeriesConverges (fun n => f (n+1 : ℕ)) ↔ ∃ L, Ch10.ImproperRight f 1 L) ∧
    (∀ L, Ch10.ImproperRight f 1 L → ∀ N : ℕ, 1 ≤ N →
      ∃ J, Ch10.ImproperRight f (N:ℝ) J ∧
        SeriesHasSum (fun n => f (n+N+1 : ℕ)) (∑' n : ℕ, f (n+N+1 : ℕ)) ∧
        (∑' n : ℕ, f (n+N+1 : ℕ)) ≤ J) := by
  have hloc (T : ℝ) (hT : 1 ≤ T) : IntervalIntegrable f volume 1 T := by
    apply (hf.mono ?_).intervalIntegrable
    rw [uIcc_of_le hT]
    exact Icc_subset_Ici_self
  have hn' : ∀ x ∈ Ioi ((1:ℕ):ℝ), 0 ≤ f x := fun x hx =>
    hn x (by exact_mod_cast (mem_Ioi.mp hx).le)
  have hmono : AntitoneOn f (Ici ((1:ℕ):ℝ)) := by simpa using hf
  have hbridge (L : ℝ) (hL : Ch10.ImproperRight f 1 L) : IntegrableOn f (Ioi 1) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop) (L+1) 1
      (b := fun T : ℝ => max 1 T)
      (fun T => (hloc _ (le_max_left 1 T)).1) ?_ ?_
    · apply tendsto_atTop.2
      intro B
      filter_upwards [eventually_ge_atTop B] with T hT
      exact hT.trans (le_max_right _ _)
    · filter_upwards [eventually_ge_atTop (1:ℝ), hL.2.eventually
        (Iio_mem_nhds (show L < L+1 by linarith))] with T hT hval
      rw [max_eq_right hT]
      have he : (∫ x in (1:ℝ)..T, ‖f x‖) = ∫ x in (1:ℝ)..T, f x := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hT]
        exact fun x hx => Real.norm_of_nonneg (hn x hx.1)
      exact he.trans_le hval.le
  have hpos : ∀ n : ℕ, 0 ≤ f (n+1 : ℕ) := fun n => hn _ (by exact_mod_cast Nat.succ_pos n)
  constructor
  · rw [positive_series_summable hpos]
    constructor
    · intro hs
      have hi := hmono.integrableOn_Ioi_of_summable_comp_add hs hn'
      exact ⟨_,hloc,intervalIntegral_tendsto_integral_Ioi 1 (by simpa using hi) tendsto_id⟩
    · rintro ⟨L,hL⟩
      have hs := hmono.summable_of_integrableOn_Ioi (by simpa using hbridge L hL) hn'
      exact (summable_nat_add_iff 1).2 hs
  · intro L hL N hN
    have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hmonoN := hf.mono (Ici_subset_Ici.mpr hN')
    have hnN : ∀ x ∈ Ioi (N:ℝ), 0 ≤ f x := fun x hx => hn x (hN'.trans hx.le)
    have hiN := (hbridge L hL).mono_set (Ioi_subset_Ioi hN')
    refine ⟨∫ x in Ioi (N:ℝ), f x,⟨fun T hT => ?_, intervalIntegral_tendsto_integral_Ioi _ hiN tendsto_id⟩, ?_,
      hmonoN.tsum_comp_add_le_integral N hiN hnN⟩
    · exact (hloc _ hN').symm.trans (hloc _ (hN'.trans hT))
    · have hs := hmonoN.summable_of_integrableOn_Ioi hiN hnN
      have hshift : Summable (fun n : ℕ => f (n+N+1 : ℕ)) := by
        simpa only [Nat.add_assoc] using (summable_nat_add_iff (N+1)).2 hs
      exact hshift.hasSum.tendsto_sum_nat

end Ch11
