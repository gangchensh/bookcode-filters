import Textbook.Ch10.Audit

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

theorem improper_integration_by_parts {u v du dv : ℝ → ℝ} {a B J : ℝ}
    (hu : ContinuousOn u (Ici a)) (hv : ContinuousOn v (Ici a))
    (hdu : ∀ x > a, HasDerivAt u (du x) x)
    (hdv : ∀ x > a, HasDerivAt v (dv x) x)
    (hiu : ∀ T ≥ a, IntervalIntegrable du volume a T)
    (hiv : ∀ T ≥ a, IntervalIntegrable dv volume a T)
    (hB : Tendsto (fun T => u T * v T) atTop (𝓝 B))
    (hJ : ImproperRight (fun x => du x*v x) a J) :
    ImproperRight (fun x => u x*dv x) a (B-u a*v a-J) := by
  have hsub (T : ℝ) (hT : a ≤ T) : uIcc a T ⊆ Ici a := by
    rw [uIcc_of_le hT]
    exact fun _ hx => hx.1
  refine ⟨fun T hT => (hiv T hT).continuousOn_mul (hu.mono (hsub T hT)),?_⟩
  apply ((hB.sub_const (u a*v a)).sub hJ.2).congr'
  filter_upwards [eventually_ge_atTop a] with T hT
  exact (integration_by_parts (hu.mono (hsub T hT)) (hv.mono (hsub T hT))
    (fun x hx => hdu x ((min_eq_left hT) ▸ hx.1))
    (fun x hx => hdv x ((min_eq_left hT) ▸ hx.1))
    (hiu T hT) (hiv T hT)).symm

end Ch10
