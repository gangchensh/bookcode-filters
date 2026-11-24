import Textbook.Ch09.FiniteChange

namespace Ch09

open Set MeasureTheory Filter Topology
open scoped Interval

noncomputable def rationalIndicator : ℝ → ℝ :=
  (range ((↑) : ℚ → ℝ)).indicator (fun _ => 1)

theorem rational_indicator_not_tagged_integrable {a b : ℝ} (hab : a < b) :
    (∀ x, |rationalIndicator x| ≤ 1) ∧ ¬ ∃ I, HasTaggedIntegral rationalIndicator a b I := by
  classical
  constructor
  · intro x
    by_cases hx : x ∈ range ((↑) : ℚ → ℝ) <;> simp [rationalIndicator,hx]
  · rintro ⟨I,hI⟩
    obtain ⟨δ,hδ,hfine⟩ := (tagged_integral_iff _ _ _ _).1 hI ((b-a)/3) (by linarith)
    obtain ⟨P,hP⟩ := arbitrarily_fine hab δ hδ
    have hwidth (i : Fin (P.n+1)) := P.increasing (Fin.castSucc_lt_succ (i := i))
    choose q hq₁ hq₂ using fun i => exists_rat_btwn (hwidth i)
    choose x hx₀ hx₁ hx₂ using fun i => exists_irrational_btwn (hwidth i)
    let Q : TaggedPartition a b :=
      { P with tag := fun i => q i, tag_mem := fun i => ⟨(hq₁ i).le,(hq₂ i).le⟩ }
    let R : TaggedPartition a b :=
      { P with tag := x, tag_mem := fun i => ⟨(hx₁ i).le,(hx₂ i).le⟩ }
    have hQ : Q.riemannSum rationalIndicator = b-a := by
      have h (i : Fin (Q.n+1)) : rationalIndicator (Q.tag i) = 1 :=
        indicator_of_mem (show Q.tag i ∈ range ((↑) : ℚ → ℝ) from ⟨q i,rfl⟩) _
      simp only [TaggedPartition.riemannSum,h,one_mul,TaggedPartition.width]
      rw [sum_endpoint_differences,Q.first,Q.last]
    have hR : R.riemannSum rationalIndicator = 0 := by
      have h (i : Fin (R.n+1)) : rationalIndicator (R.tag i) = 0 :=
        indicator_of_notMem (hx₀ i) _
      simp only [TaggedPartition.riemannSum,h,zero_mul,Finset.sum_const_zero]
    have h₁ := abs_lt.mp (hfine Q hP)
    have h₂ := abs_lt.mp (hfine R hP)
    rw [hQ] at h₁
    rw [hR] at h₂
    linarith [h₁.2,h₂.1]

theorem rational_indicator_interval_integral (a b : ℝ) :
    IntervalIntegrable rationalIndicator volume a b ∧
      (∫ x in a..b, rationalIndicator x) = 0 := by
  let S := range ((↑) : ℚ → ℝ)
  have hzero : volume S = 0 := (countable_range _).measure_zero _
  have he : rationalIndicator =ᵐ[volume] (fun _ => 0) := by
    filter_upwards [ae_iff.mpr (show volume {x | ¬ x ∉ S} = 0 by simpa using hzero)] with x hx
    exact indicator_of_notMem hx _
  have hi : Integrable rationalIndicator volume := (integrable_zero ℝ ℝ volume).congr he.symm
  refine ⟨hi.intervalIntegrable,?_⟩
  rw [intervalIntegral.integral_congr_ae (he.mono fun _ hx _ => hx)]
  simp

theorem modified_identity_at_zero {a b : ℝ} (hab : a < b) :
    let g := Function.update (fun x : ℝ => x) 0 1
    HasTaggedIntegral g a b (∫ x in a..b, x) ∧
      Tendsto g (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) ∧
      ¬ ContinuousAt g 0 ∧ ¬ DifferentiableAt ℝ g 0 := by
  dsimp only
  let g := Function.update (fun x : ℝ => x) 0 1
  have hI : HasTaggedIntegral g a b (∫ x in a..b, x) :=
    tagged_integral_update (continuous_tagged_integral hab continuous_id.continuousOn) 0 1
  have he : g =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)] fun x : ℝ => x := by
    filter_upwards [(self_mem_nhdsWithin : ({0}ᶜ : Set ℝ) ∈ nhdsWithin 0 {0}ᶜ)] with x hx
    exact Function.update_of_ne (show x ≠ 0 from hx) ..
  have ht : Tendsto g (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0) :=
    (tendsto_congr' he).mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hn : ¬ ContinuousAt g 0 := by
    intro hc
    have hu := tendsto_nhds_unique ht (hc.tendsto.mono_left nhdsWithin_le_nhds)
    simpa [g] using hu
  exact ⟨hI,ht,hn,fun h => hn h.continuousAt⟩

end Ch09
