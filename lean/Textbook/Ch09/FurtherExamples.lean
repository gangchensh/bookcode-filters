import Textbook.Ch09.Accumulation
import Textbook.Ch09.MeanValue

namespace Ch09

open MeasureTheory Set
open scoped Interval

theorem tagged_displacement {v : ℝ → ℝ} {a b D : ℝ} (hab : a < b)
    (h : HasTaggedIntegral v a b D) :
    (∫ t in a..b, v t) = D ∧
    ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b, P.mesh < δ →
      |(∑ i, v (P.tag i)*(P.points i.succ-P.points i.castSucc)) - D| < ε :=
  ⟨(tagged_measure_agreement hab h).2, (tagged_integral_iff _ _ _ _).1 h⟩

theorem tagged_density_mass {ρ : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (h : HasTaggedIntegral ρ a b M) (hρ : ∀ x ∈ Icc a b, 0 ≤ ρ x) :
    0 ≤ M ∧ (∫ x in a..b, ρ x) = M := by
  have hzero : HasTaggedIntegral (fun _ => 0) a b 0 := by
    simpa using (tagged_constant_integral (a := a) (b := b) 0)
  exact ⟨tagged_integral_mono hab hzero h (fun x hx => hρ x hx),
    (tagged_measure_agreement hab h).2⟩

theorem primitive_on_open_interval {f : ℝ → ℝ} {l r a : ℝ}
    (hf : ContinuousOn f (Ioo l r)) (ha : a ∈ Ioo l r) :
    ∀ x ∈ Ioo l r, HasDerivAt (fun y => ∫ t in a..y, f t) (f x) x := by
  intro x hx
  obtain ⟨p,hlp,hp⟩ := exists_between (lt_min ha.1 hx.1)
  obtain ⟨q,hq,hqr⟩ := exists_between (max_lt ha.2 hx.2)
  have hpa := hp.trans_le (min_le_left a x)
  have hpx := hp.trans_le (min_le_right a x)
  have haq := (le_max_left a x).trans_lt hq
  have hxq := (le_max_right a x).trans_lt hq
  have hpq := hpa.trans haq
  have hs : Icc p q ⊆ Ioo l r := fun _ hy => ⟨hlp.trans_le hy.1,hy.2.trans_lt hqr⟩
  exact tagged_accumulation_derivative ⟨hpx,hxq⟩ ⟨hpa.le,haq.le⟩
    (continuous_tagged_integral hpq (hf.mono hs))
    (hf.continuousAt (Ioo_mem_nhds hx.1 hx.2))

theorem primitives_differ_by_constant {F G f : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hF' : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hG' : ∀ x ∈ Ioo a b, HasDerivAt G (f x) x) :
    ∃ C, ∀ x ∈ Icc a b, F x = G x+C := by
  refine ⟨F a-G a,?_⟩
  intro x hx
  have hc : ContinuousOn (fun y => F y-G y) (Icc a x) :=
    (hF.sub hG).mono (Icc_subset_Icc_right hx.2)
  have hd (y : ℝ) (hy : y ∈ Ioo a x) : HasDerivAt (fun t => F t-G t) 0 y := by
    have hy' : y ∈ Ioo a b := ⟨hy.1,hy.2.trans_le hx.2⟩
    convert (hF' y hy').sub (hG' y hy') using 1
    simp
  have he := interval_newton_leibniz hx.1 hc hd
    (intervalIntegrable_const (c := (0:ℝ)))
  simp at he
  linarith

theorem tagged_strict_order {f g : ℝ → ℝ} {a b I J : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) (hp : ∃ c ∈ Icc a b, f c < g c)
    (hi : HasTaggedIntegral f a b I) (hj : HasTaggedIntegral g a b J) : I < J := by
  have h : HasTaggedIntegral (fun x => g x-f x) a b (J-I) := by
    simpa [sub_eq_add_neg] using tagged_integral_linear hj hi 1 (-1)
  apply sub_pos.mp
  exact tagged_integral_positive hab (hg.sub hf) (fun x hx => sub_nonneg.mpr (hfg x hx))
    (by obtain ⟨c,hc,hc'⟩ := hp; exact ⟨c,hc,sub_pos.mpr hc'⟩) h

end Ch09
