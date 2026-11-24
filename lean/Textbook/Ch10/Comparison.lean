import Textbook.Ch10.Audit

namespace Ch10

open MeasureTheory Filter Set
open scoped Topology Interval

def LocallyIntervalIntegrable (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ T, a ≤ T → IntervalIntegrable f volume a T

theorem positive_improper_iff_bounded {f : ℝ → ℝ} {a : ℝ}
    (hi : LocallyIntervalIntegrable f a) (hf : ∀ x ≥ a, 0 ≤ f x) :
    (∃ L, ImproperRight f a L) ↔
      ∃ C : ℝ, ∀ T ≥ a, (∫ x in a..T, f x) ≤ C := by
  let A (T : ℝ) := ∫ x in a..T, f x
  have hm : MonotoneOn A (Ici a) := by
    intro T hT U hU hTU
    have hseg := (hi T hT).symm.trans (hi U hU)
    have he := intervalIntegral.integral_add_adjacent_intervals (hi T hT) hseg
    have hn := intervalIntegral.integral_nonneg (μ := volume) hTU (fun x hx => hf x (hT.trans hx.1))
    dsimp [A]
    linarith
  constructor
  · rintro ⟨L,hL⟩
    refine ⟨L,fun T hT => ge_of_tendsto hL.2 ?_⟩
    exact (eventually_ge_atTop T).mono fun U hU => hm hT (show U ∈ Ici a from hT.trans hU) hU
  · rintro ⟨C,hC⟩
    have hm' : Monotone (fun T => A (max a T)) :=
      fun T U h => hm (a := max a T) (b := max a U)
        (le_max_left a T) (le_max_left a U) (max_le_max_left a h)
    have hb : BddAbove (range fun T => A (max a T)) := ⟨C,by
      rintro _ ⟨T,rfl⟩
      exact hC _ (le_max_left _ _)⟩
    refine ⟨_,hi,(tendsto_atTop_ciSup hm' hb).congr' ?_⟩
    filter_upwards [eventually_ge_atTop a] with T hT
    rw [max_eq_right hT]

theorem improper_start_iff {f : ℝ → ℝ} {a B : ℝ} (hB : a ≤ B)
    (hi : LocallyIntervalIntegrable f a) :
    (∃ L, ImproperRight f a L) ↔ ∃ L, ImproperRight f B L := by
  have hb : LocallyIntervalIntegrable f B :=
    fun T hT => (hi B hB).symm.trans (hi T (hB.trans hT))
  have he (T : ℝ) (hT : B ≤ T) :
      (∫ x in a..B, f x) + (∫ x in B..T, f x) = ∫ x in a..T, f x :=
    intervalIntegral.integral_add_adjacent_intervals (hi B hB) (hb T hT)
  constructor
  · rintro ⟨L,hL⟩
    refine ⟨_,hb,(hL.2.sub_const (∫ x in a..B, f x)).congr' ?_⟩
    filter_upwards [eventually_ge_atTop B] with T hT
    linarith [he T hT]
  · rintro ⟨L,hL⟩
    refine ⟨_,hi,(hL.2.const_add (∫ x in a..B, f x)).congr' ?_⟩
    filter_upwards [eventually_ge_atTop B] with T hT
    exact he T hT

theorem improper_comparison {f g : ℝ → ℝ} {a B : ℝ} (hB : a ≤ B)
    (hfi : LocallyIntervalIntegrable f a) (hgi : LocallyIntervalIntegrable g a)
    (h : ∀ x ≥ B, 0 ≤ f x ∧ f x ≤ g x) :
    ((∃ L, ImproperRight g a L) → ∃ L, ImproperRight f a L) ∧
      (Tendsto (fun T => ∫ x in B..T, f x) atTop atTop →
        Tendsto (fun T => ∫ x in a..T, g x) atTop atTop) := by
  have hfB : LocallyIntervalIntegrable f B :=
    fun T hT => (hfi B hB).symm.trans (hfi T (hB.trans hT))
  have hgB : LocallyIntervalIntegrable g B :=
    fun T hT => (hgi B hB).symm.trans (hgi T (hB.trans hT))
  have hp (T : ℝ) (hT : B ≤ T) : (∫ x in B..T, f x) ≤ ∫ x in B..T, g x :=
    intervalIntegral.integral_mono_on hT (hfB T hT) (hgB T hT) (fun x hx => (h x hx.1).2)
  constructor
  · intro hg
    obtain ⟨C,hC⟩ := (positive_improper_iff_bounded hgB
      (fun x hx => (h x hx).1.trans (h x hx).2)).1 ((improper_start_iff hB hgi).1 hg)
    exact (improper_start_iff hB hfi).2 ((positive_improper_iff_bounded hfB
      (fun x hx => (h x hx).1)).2 ⟨C,fun T hT => (hp T hT).trans (hC T hT)⟩)
  · intro ht
    have hg := tendsto_atTop_mono' _ (by
      filter_upwards [eventually_ge_atTop B] with T hT
      exact hp T hT) ht
    apply (tendsto_atTop_add_const_left atTop (∫ x in a..B, g x) hg).congr'
    filter_upwards [eventually_ge_atTop B] with T hT
    exact intervalIntegral.integral_add_adjacent_intervals (hgi B hB) (hgB T hT)

private theorem improper_const_mul {f : ℝ → ℝ} {a L : ℝ} (h : ImproperRight f a L) (k : ℝ) :
    ImproperRight (fun x => k*f x) a (k*L) := by
  refine ⟨fun T hT => (h.1 T hT).const_mul k,?_⟩
  simpa only [intervalIntegral.integral_const_mul] using h.2.const_mul k

theorem improper_limit_comparison {f g : ℝ → ℝ} {a c : ℝ} (hc : 0 < c)
    (hfi : LocallyIntervalIntegrable f a) (hgi : LocallyIntervalIntegrable g a)
    (hg : ∀ᶠ x in atTop, 0 < g x)
    (h : Tendsto (fun x => f x / g x) atTop (𝓝 c)) :
    (∃ L, ImproperRight f a L) ↔ ∃ L, ImproperRight g a L := by
  have hlow := (tendsto_order.1 h).1 (c/2) (by linarith)
  have hhigh := (tendsto_order.1 h).2 (3*c/2) (by linarith)
  have hb : ∀ᶠ x in atTop, 0 ≤ f x ∧ f x ≤ (3*c/2)*g x ∧
      0 ≤ g x ∧ g x ≤ (2/c)*f x := by
    filter_upwards [hg,hlow,hhigh] with x hgp hl hh
    have hl' := (lt_div_iff₀ hgp).1 hl
    have hh' := (div_lt_iff₀ hgp).1 hh
    have hcl : 0 ≤ (c/2)*g x := mul_nonneg (by positivity) hgp.le
    refine ⟨hcl.trans hl'.le,hh'.le,hgp.le,?_⟩
    rw [div_mul_eq_mul_div,le_div_iff₀ hc]
    nlinarith
  obtain ⟨B,hB⟩ := eventually_atTop.1 hb
  have hBa : a ≤ max a B := le_max_left _ _
  have hB' (x : ℝ) (hx : max a B ≤ x) := hB x ((le_max_right _ _).trans hx)
  constructor
  · rintro ⟨L,hL⟩
    exact (improper_comparison hBa hgi (fun T hT => (hfi T hT).const_mul (2/c))
      (fun x hx => ⟨(hB' x hx).2.2.1,(hB' x hx).2.2.2⟩)).1
      ⟨_,improper_const_mul hL (2/c)⟩
  · rintro ⟨L,hL⟩
    exact (improper_comparison hBa hfi (fun T hT => (hgi T hT).const_mul (3*c/2))
      (fun x hx => ⟨(hB' x hx).1,(hB' x hx).2.1⟩)).1
      ⟨_,improper_const_mul hL (3*c/2)⟩

end Ch10
