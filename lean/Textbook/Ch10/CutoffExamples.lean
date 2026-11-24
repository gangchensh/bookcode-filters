import Textbook.Ch10.Audit

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem oscillating_integral_cutoff_counterexample :
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..(n:ℝ), 2*Real.pi*Real.cos (2*Real.pi*x)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..((n:ℝ)+1/4), 2*Real.pi*Real.cos (2*Real.pi*x))
      atTop (𝓝 1) ∧
    ¬ ∃ I, ImproperRight (fun x => 2*Real.pi*Real.cos (2*Real.pi*x)) 0 I := by
  have h₀ : Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..(n:ℝ), 2*Real.pi*Real.cos (2*Real.pi*x))
      atTop (𝓝 0) := tendsto_const_nhds.congr fun n => by
    rw [oscillating_truncation,(oscillating_cutoffs n).1]
  have h₁ : Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..((n:ℝ)+1/4), 2*Real.pi*Real.cos (2*Real.pi*x))
      atTop (𝓝 1) := tendsto_const_nhds.congr fun n => by
    rw [oscillating_truncation,(oscillating_cutoffs n).2]
  refine ⟨h₀,h₁,?_⟩
  rintro ⟨I,hI⟩
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hquarter := tendsto_atTop_add_const_right _ (1/4:ℝ) hn
  have e₀ := tendsto_nhds_unique h₀ (hI.2.comp hn)
  have e₁ := tendsto_nhds_unique h₁ (hI.2.comp hquarter)
  linarith

theorem integer_cutoff_of_full {f : ℝ → ℝ} {I : ℝ} (h : ImproperRight f 0 I) :
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..(n:ℝ), f x) atTop (𝓝 I) :=
  h.2.comp tendsto_natCast_atTop_atTop

end Ch10
