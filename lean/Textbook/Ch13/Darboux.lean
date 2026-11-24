import Textbook.Ch13.Bridges

namespace Ch13
open MeasureTheory Set Filter

theorem ae_measurable_of_envelopes {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : X → ℝ) (l u : ℕ → X → ℝ)
    (hml : ∀ n, Measurable (l n)) (hmu : ∀ n, Measurable (u n))
    (hil : ∀ n, Integrable (l n) μ) (hiu : ∀ n, Integrable (u n) μ)
    (hbounds : ∀ᵐ x ∂μ, ∀ n, l n x ≤ f x ∧ f x ≤ u n x)
    (hgap : ∀ ε > 0, ∃ n, (∫ x, u n x ∂μ) - (∫ x, l n x ∂μ) < ε) :
    AEStronglyMeasurable f μ := by
  let lo := fun x => ⨆ n, l n x
  let hi := fun x => ⨅ n, u n x
  have hlo : Measurable lo := Measurable.iSup hml
  have hhi : Measurable hi := Measurable.iInf hmu
  have hb : ∀ᵐ x ∂μ, ∀ n, l n x ≤ lo x ∧ lo x ≤ f x ∧ f x ≤ hi x ∧ hi x ≤ u n x := by
    filter_upwards [hbounds] with x hx n
    have hl : BddAbove (range fun k => l k x) := ⟨f x, by rintro _ ⟨k,rfl⟩; exact (hx k).1⟩
    have hu : BddBelow (range fun k => u k x) := ⟨f x, by rintro _ ⟨k,rfl⟩; exact (hx k).2⟩
    exact ⟨le_ciSup hl n, ciSup_le (fun k => (hx k).1),
      le_ciInf (fun k => (hx k).2), ciInf_le hu n⟩
  let gap := fun x => hi x - lo x
  have hnon : 0 ≤ᵐ[μ] gap := hb.mono fun x hx =>
    sub_nonneg.mpr ((hx 0).2.1.trans (hx 0).2.2.1)
  have hdom (n : ℕ) : gap ≤ᵐ[μ] fun x => u n x - l n x := by
    filter_upwards [hb] with x hx
    exact sub_le_sub (hx n).2.2.2 (hx n).1
  have hgi : Integrable gap μ := by
    apply ((hiu 0).sub (hil 0)).mono' (hhi.sub hlo).aestronglyMeasurable
    filter_upwards [hnon, hdom 0] with x h0 hx
    change 0 ≤ gap x at h0
    change ‖gap x‖ ≤ u 0 x - l 0 x
    rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hzero : (∫ x, gap x ∂μ) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hnon)
    by_contra! hp
    obtain ⟨n,hn⟩ := hgap _ hp
    have hb' := integral_mono_ae hgi ((hiu n).sub (hil n)) (hdom n)
    change (∫ x, gap x ∂μ) ≤ ∫ x, u n x - l n x ∂μ at hb'
    rw [integral_sub (hiu n) (hil n)] at hb'
    exact (not_lt_of_ge hb') hn
  have hzg := (integral_eq_zero_iff_of_nonneg_ae hnon hgi).1 hzero
  have hfeq : lo =ᵐ[μ] f := by
    filter_upwards [hb, hzg] with x hx hz
    change hi x - lo x = 0 at hz
    exact le_antisymm (hx 0).2.1 ((hx 0).2.2.1.trans (sub_eq_zero.mp hz).le)
  exact hlo.aestronglyMeasurable.congr hfeq

theorem riemann_agreement_of_nested_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : X → ℝ) (I : ℝ) (l u : ℕ → X → ℝ)
    (hml : ∀ n, Measurable (l n)) (hmu : ∀ n, Measurable (u n))
    (hil : ∀ n, Integrable (l n) μ) (hiu : ∀ n, Integrable (u n) μ)
    (hbounds : ∀ᵐ x ∂μ, Monotone (fun n => l n x) ∧ Antitone (fun n => u n x) ∧
      ∀ n, l n x ≤ f x ∧ f x ≤ u n x)
    (hI : ∀ n, (∫ x, l n x ∂μ) ≤ I ∧ I ≤ ∫ x, u n x ∂μ)
    (hgap : ∀ ε > 0, ∃ n, (∫ x, u n x ∂μ) - (∫ x, l n x ∂μ) < ε) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = I := by
  apply integral_agreement_of_sandwich f I (ae_measurable_of_envelopes f l u hml hmu hil hiu
    (hbounds.mono fun _ hx => hx.2.2) hgap)
  intro ε hε
  obtain ⟨n,hn⟩ := hgap ε hε
  exact ⟨l n, u n, hil n, hiu n, hbounds.mono (fun _ hx => (hx.2.2 n).1),
    hbounds.mono (fun _ hx => (hx.2.2 n).2), (hI n).1, (hI n).2, hn⟩

end Ch13
