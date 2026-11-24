import Textbook.Ch11.Radius
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Uniqueness

namespace Ch11

open Filter Set
open scoped Topology NNReal ENNReal

private theorem scalar_series_on_ball {c : ℕ → ℝ} (a : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (hm : ρ ∈ radiusSet c) :
    HasFPowerSeriesOnBall (fun t => ∑' n, powerSeriesTerm c a t n)
      (FormalMultilinearSeries.ofScalars ℝ c) a (ENNReal.ofReal ρ) := by
  have hsum : Summable (fun n => ‖FormalMultilinearSeries.ofScalars ℝ c n‖ * ρ^n) := by
    simpa only [FormalMultilinearSeries.ofScalars_norm,Real.norm_eq_abs] using
      (positive_series_summable (fun _ => by positivity)).1 hm.2
  have hrad := (FormalMultilinearSeries.ofScalars ℝ c).le_radius_of_summable
    (r := ⟨ρ,hρ.le⟩) hsum
  refine ⟨by rw [ENNReal.ofReal_eq_coe_nnreal hρ.le]; exact hrad, ENNReal.ofReal_pos.mpr hρ,?_⟩
  intro y hy
  rw [Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero] at hy
  have hlt : ((|a+y-a| : ℝ) : WithTop ℝ) < convergenceRadius c :=
    (WithTop.coe_lt_coe.mpr (by simpa only [add_sub_cancel_left] using hy)).trans_le
      (le_convergenceRadius hm)
  have h := (positive_series_summable (fun n => abs_nonneg (powerSeriesTerm c a (a+y) n))).1
    (power_series_inside hlt)
  have he : powerSeriesTerm c a (a+y) = fun n => c n*y^n := by
    funext n
    simp [powerSeriesTerm,add_sub_cancel_left]
  rw [he] at h ⊢
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using h.of_abs.hasSum

theorem power_series_smooth {c : ℕ → ℝ} {a x : ℝ}
    (hx : ((|x-a| : ℝ) : WithTop ℝ) < convergenceRadius c) :
    ContDiffAt ℝ ⊤ (fun t => ∑' n, powerSeriesTerm c a t n) x := by
  obtain ⟨ρ,hm,hρ⟩ := radius_has_majorant hx
  have hb := scalar_series_on_ball a ((abs_nonneg _).trans_lt hρ) hm
  apply (hb.analyticAt_of_mem ?_).contDiffAt
  simpa only [Metric.eball_ofReal,Metric.mem_ball,Real.dist_eq] using hρ

theorem power_series_taylor_coefficients {c : ℕ → ℝ} {a : ℝ}
    (h : (0:WithTop ℝ) < convergenceRadius c) (m : ℕ) :
    c m = iteratedDeriv m (fun t => ∑' n, powerSeriesTerm c a t n) a / (m.factorial:ℝ) := by
  obtain ⟨ρ,hm,hρ⟩ := radius_has_majorant (r := 0) h
  have hb := (scalar_series_on_ball a hρ hm).hasFPowerSeriesAt
  have hc := hb.analyticAt.hasFPowerSeriesAt
  have he := FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    (hb.eq_formalMultilinearSeries hc)
  exact congrFun he m

theorem power_series_coefficients_unique {c d : ℕ → ℝ} {a : ℝ}
    (hc : (0:WithTop ℝ) < convergenceRadius c)
    (hd : (0:WithTop ℝ) < convergenceRadius d)
    (he : ∀ᶠ x in 𝓝 a, (∑' n, powerSeriesTerm c a x n) = ∑' n, powerSeriesTerm d a x n) :
    c = d := by
  obtain ⟨ρ,hr,hρ⟩ := radius_has_majorant (r := 0) hc
  obtain ⟨σ,hs,hσ⟩ := radius_has_majorant (r := 0) hd
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ
    ((scalar_series_on_ball a hρ hr).hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
      (scalar_series_on_ball a hσ hs).hasFPowerSeriesAt he)

end Ch11
