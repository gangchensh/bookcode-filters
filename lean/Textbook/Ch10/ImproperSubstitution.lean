import Textbook.Ch10.RootExamples

namespace Ch10

open Filter MeasureTheory Set
open scoped Topology Interval

private theorem map_increasing_ray {g : ℝ → ℝ} {a : ℝ} {s : Set ℝ}
    (hm : StrictMonoOn g (Ici a)) (hs : MapsTo g (Ici a) s)
    (ho : SurjOn g (Ici a) s)
    {F : Filter ℝ} (hb : ∀ U : Set ℝ, U ∈ F ↔
      ∃ y ∈ s, ∀ z ∈ s, y ≤ z → z ∈ U) :
    map g atTop = F := by
  ext U
  change (∀ᶠ x in atTop, g x ∈ U) ↔ U ∈ F
  rw [eventually_atTop, hb]
  constructor
  · rintro ⟨B, hB⟩
    let T := max a B
    have hT : T ∈ Ici a := mem_Ici.mpr (le_max_left _ _)
    refine ⟨g T, hs hT, ?_⟩
    intro z hz hgz
    obtain ⟨x, hx, rfl⟩ := ho hz
    have hTx : T ≤ x := le_of_not_gt fun h => (not_lt_of_ge hgz) (hm hx hT h)
    exact hB x ((le_max_right a B).trans hTx)
  · rintro ⟨y, hy, hU⟩
    obtain ⟨T, hT, rfl⟩ := ho hy
    refine ⟨T, fun x hx => ?_⟩
    have hxa : x ∈ Ici a := hT.trans hx
    exact hU (g x) (hs hxa) (hm.monotoneOn hT hxa hx)

private theorem substitution_on_ray {g dg f : ℝ → ℝ} {a α T : ℝ} {s : Set ℝ}
    (hT : a ≤ T) (hg : g a = α) (hs : MapsTo g (Ici a) s)
    (hd : ∀ x ≥ a, HasDerivAt g (dg x) x)
    (hc : ContinuousOn dg (Ici a)) (hf : ContinuousOn f s) :
    (∫ x in a..T, f (g x) * dg x) = ∫ y in α..g T, f y := by
  have hsub : uIcc a T ⊆ Ici a := by
    rw [uIcc_of_le hT]
    exact fun _ hx => hx.1
  rw [← hg]
  exact change_variable_local (fun x hx => hd x (hsub hx)) (hc.mono hsub)
    (hf.mono (by rintro _ ⟨x,hx,rfl⟩; exact hs (hsub hx)))

private theorem left_integrable {g dg f : ℝ → ℝ} {a T : ℝ} {s : Set ℝ}
    (hT : a ≤ T) (hs : MapsTo g (Ici a) s)
    (hd : ∀ x ≥ a, HasDerivAt g (dg x) x)
    (hc : ContinuousOn dg (Ici a)) (hf : ContinuousOn f s) :
    IntervalIntegrable (fun x => f (g x) * dg x) volume a T :=
  ((hf.comp (fun x hx => (hd x hx).continuousAt.continuousWithinAt) hs).mul hc)
    |>.mono (fun _ hx => hx.1) |>.intervalIntegrable_of_Icc hT

theorem improper_substitution_infinite {g dg f : ℝ → ℝ} {a α L : ℝ}
    (hg : g a = α) (hm : StrictMonoOn g (Ici a)) (hs : MapsTo g (Ici a) (Ici α))
    (ho : SurjOn g (Ici a) (Ici α)) (hd : ∀ x ≥ a, HasDerivAt g (dg x) x)
    (hc : ContinuousOn dg (Ici a)) (hf : ContinuousOn f (Ici α)) :
    ImproperRight (fun x => f (g x) * dg x) a L ↔ ImproperRight f α L := by
  have hm' := map_increasing_ray hm hs ho (F := atTop) (fun U => by
    change (∀ᶠ x in atTop, x ∈ U) ↔ _
    rw [eventually_atTop]
    constructor
    · rintro ⟨B,hB⟩
      exact ⟨max α B,mem_Ici.mpr (le_max_left _ _),fun x _ hx => hB x ((le_max_right α B).trans hx)⟩
    · rintro ⟨B,hB,h⟩
      exact ⟨B,fun x hx => h x (hB.trans hx) hx⟩)
  have he : (fun T => ∫ x in a..T, f (g x) * dg x) =ᶠ[atTop]
      fun T => (fun c => ∫ x in α..c, f x) (g T) :=
    (eventually_ge_atTop a).mono fun T hT => substitution_on_ray hT hg hs hd hc hf
  have hlim : Tendsto (fun T => ∫ x in a..T, f (g x) * dg x) atTop (𝓝 L) ↔
      Tendsto (fun c => ∫ x in α..c, f x) atTop (𝓝 L) := by
    rw [tendsto_congr' he]
    change Tendsto ((fun c => ∫ x in α..c, f x) ∘ g) atTop (𝓝 L) ↔ _
    rw [← tendsto_map'_iff, hm']
  exact ⟨fun h => ⟨fun T hT => (hf.mono (fun _ hx => hx.1)).intervalIntegrable_of_Icc hT,
      hlim.mp h.2⟩,
    fun h => ⟨fun T hT => left_integrable hT hs hd hc hf,hlim.mpr h.2⟩⟩

theorem improper_substitution_finite {g dg f : ℝ → ℝ} {a α β L : ℝ}
    (hαβ : α < β) (hg : g a = α) (hm : StrictMonoOn g (Ici a))
    (hs : MapsTo g (Ici a) (Ico α β)) (ho : SurjOn g (Ici a) (Ico α β))
    (hd : ∀ x ≥ a, HasDerivAt g (dg x) x)
    (hc : ContinuousOn dg (Ici a)) (hf : ContinuousOn f (Ico α β)) :
    ImproperRight (fun x => f (g x) * dg x) a L ↔ ImproperEndpointRight f α β L := by
  have hm' := map_increasing_ray hm hs ho (F := 𝓝[<] β) (fun U => by
    rw [mem_nhdsLT_iff_exists_Ioo_subset' hαβ]
    constructor
    · rintro ⟨B,hB,hU⟩
      obtain ⟨y, hy, hy'⟩ := exists_between (max_lt hB hαβ)
      refine ⟨y,⟨(le_max_right B α).trans hy.le,hy'⟩,fun z hz hzy => ?_⟩
      exact hU ⟨((le_max_left B α).trans_lt hy).trans_le hzy,hz.2⟩
    · rintro ⟨B,hB,hU⟩
      exact ⟨B,hB.2,fun z hz => hU z ⟨hB.1.trans hz.1.le,hz.2⟩ hz.1.le⟩)
  have he : (fun T => ∫ x in a..T, f (g x) * dg x) =ᶠ[atTop]
      fun T => (fun c => ∫ x in α..c, f x) (g T) :=
    (eventually_ge_atTop a).mono fun T hT => substitution_on_ray hT hg hs hd hc hf
  have hlim : Tendsto (fun T => ∫ x in a..T, f (g x) * dg x) atTop (𝓝 L) ↔
      Tendsto (fun c => ∫ x in α..c, f x) (𝓝[<] β) (𝓝 L) := by
    rw [tendsto_congr' he]
    change Tendsto ((fun c => ∫ x in α..c, f x) ∘ g) atTop (𝓝 L) ↔ _
    rw [← tendsto_map'_iff, hm']
  exact ⟨fun h => ⟨fun T hT hTβ =>
    (hf.mono (fun _ hx => ⟨hx.1,hx.2.trans_lt hTβ⟩)).intervalIntegrable_of_Icc hT,
      hlim.mp h.2⟩,
    fun h => ⟨fun T hT => left_integrable hT hs hd hc hf,hlim.mpr h.2⟩⟩

end Ch10
