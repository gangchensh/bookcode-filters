import Textbook.Ch12.Multivariable

namespace Ch12

open Filter Set Asymptotics
open scoped Topology

def HasMultivariableLimit {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : E → G) (a : E) (b : G) : Prop :=
  Tendsto f (𝓝[≠] a) (𝓝 b)

def HasMultivariableLimitWithin {E G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : E → G) (S : Set E) (a : E) (b : G) : Prop :=
  Tendsto f (𝓝[S \ {a}] a) (𝓝 b)

theorem limit_within_epsilon {E G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : E → G) (S : Set E) (a : E) (b : G) :
    HasMultivariableLimitWithin f S a b ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, 0 < ‖x-a‖ → ‖x-a‖ < δ → ‖f x-b‖ < ε := by
  rw [HasMultivariableLimitWithin, Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_sdiff, mem_singleton_iff, dist_eq_norm, norm_pos_iff, sub_ne_zero, and_imp]

section Differential

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def directionalQuotient (f : E → ℝ) (a v : E) (t : ℝ) : ℝ :=
  (f (a+t • v)-f a)/t

def HasBookDirectionalDerivative (f : E → ℝ) (a v : E) (d : ℝ) : Prop :=
  Tendsto (directionalQuotient f a v) (𝓝[≠] 0) (𝓝 d)

def HasBookPartialDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (a : ι → ℝ) (i : ι) (d : ℝ) : Prop :=
  HasBookDirectionalDerivative f a (Pi.single i 1) d

theorem directional_epsilon (f : E → ℝ) (a v : E) (d : ℝ) :
    HasBookDirectionalDerivative f a v d ↔
      ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t| → |t| < δ →
        |directionalQuotient f a v t-d| < ε := by
  simpa only [HasBookDirectionalDerivative, sub_zero, Real.norm_eq_abs, and_imp] using
    punctured_limit_norm_iff (directionalQuotient f a v) 0 d

theorem partial_epsilon {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (a : ι → ℝ) (i : ι) (d : ℝ) :
    HasBookPartialDerivative f a i d ↔
      ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t| → |t| < δ →
        |(f (a+t • Pi.single i 1)-f a)/t-d| < ε :=
  directional_epsilon f a (Pi.single i 1) d

theorem directional_native (f : E → ℝ) (a v : E) (d : ℝ) :
    HasBookDirectionalDerivative f a v d ↔
      HasDerivAt (fun t : ℝ => f (a+t • v)) d 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  unfold HasBookDirectionalDerivative directionalQuotient
  simp only [zero_add, zero_smul,
    add_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem total_decides_direction {f : E → ℝ} {a : E} {L : E →L[ℝ] ℝ}
    (h : HasFDerivAt f L a) (v : E) :
    HasBookDirectionalDerivative f a v (L v) := by
  apply (directional_native f a v (L v)).2
  have hl : HasDerivAt (fun t : ℝ => a+t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add a
  have h0 : HasFDerivAt f L (a+(0:ℝ) • v) := by simpa using h
  exact h0.comp_hasDerivAt 0 hl

def HasBookTotalDerivativeWithin (f : E → G) (S : Set E) (a : E) (L : E →L[ℝ] G) : Prop :=
  Tendsto (fun x => ‖f x-f a-L (x-a)‖ / ‖x-a‖) (𝓝[S \ {a}] a) (𝓝 0)

def HasBookTotalDerivative (f : E → G) (a : E) (L : E →L[ℝ] G) : Prop :=
  HasBookTotalDerivativeWithin f univ a L

theorem native_within_remainder (f : E → G) (S : Set E) (a : E) (L : E →L[ℝ] G) :
    HasFDerivWithinAt f L S a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ h, a+h ∈ S → ‖h‖ < δ →
        ‖f (a+h)-f a-L h‖ ≤ ε*‖h‖ := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  constructor
  · intro H ε hε
    obtain ⟨δ,hδ,he⟩ := Metric.mem_nhdsWithin_iff.mp (H hε)
    refine ⟨δ,hδ,fun h hs hh => ?_⟩
    have hm : a+h ∈ Metric.ball a δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hh
    simpa using he ⟨hm,hs⟩
  · intro H ε hε
    obtain ⟨δ,hδ,he⟩ := H ε hε
    refine Metric.mem_nhdsWithin_iff.mpr ⟨δ,hδ,?_⟩
    intro x hx
    have hn : ‖x-a‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hx.1
    simpa using he (x-a) (by simpa using hx.2) hn

theorem total_within_remainder (f : E → G) (S : Set E) (a : E) (L : E →L[ℝ] G) :
    HasBookTotalDerivativeWithin f S a L ↔
      ∀ ε > 0, ∃ δ > 0, ∀ h, a+h ∈ S → ‖h‖ < δ →
        ‖f (a+h)-f a-L h‖ ≤ ε*‖h‖ := by
  change HasMultivariableLimitWithin _ S a (0:ℝ) ↔ _
  rw [limit_within_epsilon]
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
  constructor
  · intro H ε hε
    obtain ⟨δ,hδ,he⟩ := H ε hε
    refine ⟨δ,hδ,fun h hs hh => ?_⟩
    by_cases hz : h = 0
    · subst h
      simp
    · have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hz
      have hb := he (a+h) hs (by simpa using hpos) (by simpa using hh)
      have hb' : ‖f (a+h)-f a-L h‖ / ‖h‖ < ε := by simpa using hb
      exact (div_lt_iff₀ hpos).mp hb' |>.le
  · intro H ε hε
    obtain ⟨δ,hδ,he⟩ := H (ε/2) (half_pos hε)
    refine ⟨δ,hδ,fun x hx hp hd => ?_⟩
    have hb : ‖f x-f a-L (x-a)‖ ≤ (ε/2)*‖x-a‖ := by
      simpa using he (x-a) (by simpa using hx) hd
    exact (div_le_iff₀ hp).2 hb |>.trans_lt (half_lt_self hε)

theorem total_within_native (f : E → G) (S : Set E) (a : E) (L : E →L[ℝ] G) :
    HasBookTotalDerivativeWithin f S a L ↔ HasFDerivWithinAt f L S a :=
  (total_within_remainder f S a L).trans (native_within_remainder f S a L).symm

theorem total_remainder (f : E → G) (a : E) (L : E →L[ℝ] G) :
    HasBookTotalDerivative f a L ↔
      ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → ‖f (a+h)-f a-L h‖ ≤ ε*‖h‖ := by
  simpa [HasBookTotalDerivative] using total_within_remainder f univ a L

theorem total_native (f : E → G) (a : E) (L : E →L[ℝ] G) :
    HasBookTotalDerivative f a L ↔ HasFDerivAt f L a := by
  simpa [HasBookTotalDerivative] using total_within_native f univ a L

theorem total_punctured_increment (f : E → G) (a : E) (L : E →L[ℝ] G) :
    HasBookTotalDerivative f a L ↔
      Tendsto (fun h => ‖f (a+h)-f a-L h‖ / ‖h‖) (𝓝[≠] 0) (𝓝 0) := by
  have hmap : 𝓝[≠] a = Filter.map (fun h => a+h) (𝓝[≠] 0) := by simp
  rw [HasBookTotalDerivative, HasBookTotalDerivativeWithin, ← Set.compl_eq_univ_sdiff, hmap, tendsto_map'_iff]
  simp only [Function.comp_def, add_sub_cancel_left]

end Differential

theorem path_necessary {α E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
    {F : Filter α} {γ : α → E} {f : E → G} {a : E} {b : G}
    (hγ : Tendsto γ F (𝓝 a)) (hne : ∀ᶠ t in F, γ t ≠ a)
    (hf : HasMultivariableLimit f a b) :
    Tendsto (f ∘ γ) F (𝓝 b) := by
  apply hf.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hγ,hne⟩

theorem components_limit {α ι : Type*} {F : Filter α}
    (f : α → ι → ℝ) (b : ι → ℝ) :
    Tendsto f F (𝓝 b) ↔ ∀ i, Tendsto (fun x => f x i) F (𝓝 (b i)) :=
  tendsto_pi_nhds

theorem continuity_within_epsilon {E G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup G] (f : E → G) (S : Set E) (a : E) :
    ContinuousWithinAt f S a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ‖x-a‖ < δ → ‖f x-f a‖ < ε := by
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm]

section Rules

variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem total_unique {f : E → G} {a : E} {L M : E →L[ℝ] G}
    (hL : HasBookTotalDerivative f a L) (hM : HasBookTotalDerivative f a M) : L = M :=
  ((total_native f a L).1 hL).unique ((total_native f a M).1 hM)

theorem total_continuous {f : E → G} {a : E} {L : E →L[ℝ] G}
    (hL : HasBookTotalDerivative f a L) : ContinuousAt f a :=
  ((total_native f a L).1 hL).continuousAt

theorem affine_derivative (L : E →L[ℝ] G) (b : G) (a : E) :
    HasBookTotalDerivative (fun x => L x+b) a L :=
  (total_native _ _ _).2 (L.hasFDerivAt.add_const b)

theorem composed_derivative {f : E → G} {g : G → H} {a : E}
    {L : E →L[ℝ] G} {M : G →L[ℝ] H}
    (hf : HasBookTotalDerivative f a L) (hg : HasBookTotalDerivative g (f a) M) :
    HasBookTotalDerivative (g ∘ f) a (M.comp L) :=
  (total_native _ _ _).2 (((total_native _ _ _).1 hg).comp a ((total_native _ _ _).1 hf))

theorem total_direction_filter {f : E → ℝ} {a : E} {L : E →L[ℝ] ℝ}
    (h : HasBookTotalDerivative f a L) (v : E) :
    HasBookDirectionalDerivative f a v (L v) :=
  total_decides_direction ((total_native _ _ _).1 h) v

theorem coordinate_direction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {a : ι → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ}
    (h : HasBookTotalDerivative f a L) (i : ι) :
    HasBookPartialDerivative f a i (L (Pi.single i 1)) :=
  total_direction_filter h (Pi.single i 1)

end Rules

theorem product_direction (a v : ℝ × ℝ) :
    HasBookDirectionalDerivative (fun x : ℝ × ℝ => x.1*x.2) a v
      (a.2*v.1+a.1*v.2) := by
  rw [← linearModel_apply]
  exact total_decides_direction (product_derivative a) v

theorem product_limit_origin :
    HasMultivariableLimit (fun x : ℝ × ℝ => x.1*x.2) (0,0) 0 := by
  have h : ContinuousAt (fun x : ℝ × ℝ => x.1*x.2) (0,0) := by fun_prop
  have ht : Tendsto (fun x : ℝ × ℝ => x.1*x.2) (𝓝 (0,0)) (𝓝 0) := by simpa using h.tendsto
  exact ht.mono_left nhdsWithin_le_nhds

theorem sqrt_boundary_continuity (b : ℝ) :
    ContinuousWithinAt (fun x : ℝ × ℝ => Real.sqrt x.1+x.2) {x | 0 ≤ x.1} (0,b) := by
  have h : Continuous (fun x : ℝ × ℝ => Real.sqrt x.1+x.2) :=
    (Real.continuous_sqrt.comp continuous_fst).add continuous_snd
  exact h.continuousAt.continuousWithinAt

theorem component_differentiability {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] (f : E → ι → ℝ) (a : E) :
    DifferentiableAt ℝ f a ↔ ∀ i, DifferentiableAt ℝ (fun x => f x i) a :=
  differentiableAt_pi

theorem component_derivative {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype ι] {f : E → ι → ℝ} {a h : E}
    (hf : DifferentiableAt ℝ f a) (i : ι) :
    fderiv ℝ f a h i = fderiv ℝ (fun x => f x i) a h := by
  have hi := (hasFDerivAt_pi'.mp hf.hasFDerivAt) i
  rw [hi.fderiv]
  rfl

theorem line_derivatives (f : ℝ × ℝ → ℝ) (hf : ∀ x : ℝ, f (x,0) = 0) (c : ℝ) :
    HasBookTotalDerivativeWithin f {x | x.2 = 0} (0,0) (linearModel 0 c) := by
  apply (total_within_remainder _ _ _ _).2
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro h hh _
  have hy : h.2 = 0 := by simpa using hh
  have hval : f h = 0 := by
    have heq : h = (h.1,0) := Prod.ext rfl hy
    rw [heq, hf]
  have hzero : (0,0) = (0 : ℝ × ℝ) := rfl
  have hbase : f (0 : ℝ × ℝ) = 0 := hzero ▸ hf 0
  simpa [hzero, hval, hbase, linearModel_apply, hy] using
    (mul_nonneg hε.le (norm_nonneg h) : 0 ≤ ε * ‖h‖)

theorem line_derivatives_distinct {c d : ℝ} (hne : c ≠ d) :
    linearModel 0 c ≠ linearModel 0 d := by
  intro h
  apply hne
  simpa [linearModel_apply] using congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) h

end Ch12
