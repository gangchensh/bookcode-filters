import Textbook.Ch11.Radius
import Mathlib.Analysis.Calculus.SmoothSeries

namespace Ch11

open Filter MeasureTheory Set
open scoped Topology Interval

theorem power_series_operations {c : ℕ → ℝ} {a x : ℝ}
    (hx : ((|x-a| : ℝ) : WithTop ℝ) < convergenceRadius c) :
    HasDerivAt (fun t => ∑' n, powerSeriesTerm c a t n)
      (∑' n : ℕ, (n+1 : ℝ) * c (n+1) * (x-a)^n) x ∧
    (∫ t in a..x, ∑' n, powerSeriesTerm c a t n) =
      ∑' n : ℕ, c n / (n+1 : ℝ) * (x-a)^(n+1) := by
  obtain ⟨ρ,⟨hρ₀,hρs⟩,hxρ⟩ := radius_has_majorant hx
  obtain ⟨r,hxr,hrρ⟩ := exists_between hxρ
  have hr : 0 < r := (abs_nonneg _).trans_lt hxr
  have hρ : 0 < ρ := hr.trans hrρ
  have hradius : (r : WithTop ℝ) < convergenceRadius c :=
    (WithTop.coe_lt_coe.mpr hrρ).trans_le (le_convergenceRadius ⟨hρ₀,hρs⟩)
  let C := ∑' n, |c n| *ρ^n
  let q := r/ρ
  let s := Ioo (a-r) (a+r)
  have hs : IsOpen s := isOpen_Ioo
  have hpre : IsPreconnected s := isPreconnected_Ioo
  have ha : a ∈ s := ⟨by linarith, by linarith⟩
  have hxs : x ∈ s := by
    have hh := abs_lt.mp hxr
    exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hb (t : ℝ) (ht : t ∈ s) : |t-a| ≤ r := by
    apply abs_le.mpr
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hsum : Summable (fun n => |c n| *ρ^n) :=
    (positive_series_summable (fun _ => by positivity)).1 hρs
  have hC (n : ℕ) : |c n| *ρ^n ≤ C := hsum.le_tsum n (fun _ _ => by positivity)
  have hq₀ : 0 ≤ q := div_nonneg hr.le hρ.le
  have hq : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq₀]; exact (div_lt_one hρ).2 hrρ
  have hgeom : Summable (fun n : ℕ => (n:ℝ)*q^n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have hdSum : Summable (fun n : ℕ => (C/ρ)*((n+1 : ℝ)*q^n)) :=
    ((hgeom.add (summable_geometric_of_norm_lt_one hq)).congr (fun n => by ring)).mul_left _
  have hdBound (n : ℕ) (t : ℝ) (ht : t ∈ s) :
      ‖(n+1 : ℝ)*c (n+1)*(t-a)^n‖ ≤ (C/ρ)*((n+1 : ℝ)*q^n) := by
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_of_nonneg (by positivity : 0 ≤ (n+1 : ℝ))]
    calc
      _ ≤ (n+1 : ℝ)*|c (n+1)| *r^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hb t ht) n) (by positivity)
      _ = (|c (n+1)| *ρ^(n+1))/ρ*((n+1 : ℝ)*q^n) := by
        dsimp [q]
        rw [div_pow,pow_succ]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hC _) hρ.le) (by positivity)
  have hzero : Summable (fun n : ℕ => powerSeriesTerm c a a (n+1)) := by
    simp [powerSeriesTerm,pow_succ]
  have hdiff := hasDerivAt_tsum_of_isPreconnected hdSum hs hpre
    (g := fun n t => powerSeriesTerm c a t (n+1))
    (g' := fun n t => (n+1 : ℝ)*c (n+1)*(t-a)^n)
    (fun n t _ => by
      have h := (((hasDerivAt_id t).sub_const a).fun_pow (n+1)).const_mul (c (n+1))
      simpa [id_eq,powerSeriesTerm,mul_comm,mul_left_comm,mul_assoc] using h)
    hdBound ha hzero hxs
  have hpoint (t : ℝ) (ht : t ∈ s) : Summable (powerSeriesTerm c a t) := by
    have hh := (power_series_uniform hr.le hradius).1 t (hb t ht)
    exact (Summable.of_abs ((positive_series_summable (fun _ => abs_nonneg _)).1 hh))
  have hshift := hdiff.const_add (c 0)
  have hderiv : HasDerivAt (fun t => ∑' n, powerSeriesTerm c a t n)
      (∑' n : ℕ, (n+1 : ℝ)*c (n+1)*(x-a)^n) x := by
    apply hshift.congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hxs] with t ht
    have h := (hpoint t ht).tsum_eq_zero_add
    simpa [powerSeriesTerm,pow_zero,mul_one] using h
  refine ⟨hderiv,?_⟩
  let G := fun t : ℝ => ∑' n : ℕ, c n/(n+1:ℝ)*(t-a)^(n+1)
  have hM (n : ℕ) (t : ℝ) (ht : t ∈ s) :
      ‖powerSeriesTerm c a t n‖ ≤ |c n| *ρ^n := by
    rw [Real.norm_eq_abs,powerSeriesTerm,abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) ((hb t ht).trans hrρ.le) n) (abs_nonneg _)
  have hG (t : ℝ) (ht : t ∈ s) :
      HasDerivAt G (∑' n, powerSeriesTerm c a t n) t := by
    apply hasDerivAt_tsum_of_isPreconnected hsum hs hpre ?_ hM ha ?_ ht
    · intro n y _
      have h := (((hasDerivAt_id y).sub_const a).fun_pow (n+1)).const_mul (c n/(n+1:ℝ))
      have he : c n / (n+1:ℝ) * ((n+1:ℝ) * (y-a)^n) = powerSeriesTerm c a y n := by
        unfold powerSeriesTerm
        field_simp
      simpa only [id_eq,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,mul_one,he] using h
    · simp [pow_succ]
  have hsub : uIcc a x ⊆ s := (show OrdConnected s by dsimp [s]; infer_instance).uIcc_subset ha hxs
  have hcont : ContinuousOn (fun t => ∑' n, powerSeriesTerm c a t n) (uIcc a x) :=
    ((power_series_uniform hr.le hradius).2.continuousOn
      (Eventually.of_forall (fun N => (continuous_finsetSum _ (fun n _ =>
        (by unfold powerSeriesTerm; fun_prop : Continuous (fun t => powerSeriesTerm c a t n)))).continuousOn)).frequently).mono
      (fun t ht => hb t (hsub ht))
  have hGa : G a = 0 := by simp [G,pow_succ]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hG t (hsub ht)) hcont.intervalIntegrable,hGa,sub_zero]

end Ch11
