import Textbook.Ch09.Darboux
import Textbook.Ch09.FiniteChange
import Textbook.Ch09.Monotone
import Textbook.Ch09.Consequences

namespace Ch09

open MeasureTheory Set
open scoped Interval

private theorem tagged_finset_sum {ι : Type*} {a b : ℝ} (s : Finset ι)
    (g : ι → ℝ → ℝ) (v : ι → ℝ) (h : ∀ i ∈ s, HasTaggedIntegral (g i) a b (v i)) :
    HasTaggedIntegral (fun x => ∑ i ∈ s, g i x) a b (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (tagged_constant_integral (a := a) (b := b) 0)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      simpa using tagged_integral_linear (h i (Finset.mem_insert_self i s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) 1 1

private theorem tagged_cell_indicator {a b l r : ℝ} (hab : a < b)
    (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b) (c : ℝ) :
    HasTaggedIntegral ((Ioc l r).indicator fun _ => c) a b (c*(r-l)) := by
  let step (p x : ℝ) : ℝ := if x ≤ p then 1 else 0
  have hm (p : ℝ) : AntitoneOn (step p) (Icc a b) := by
    intro x _ y _ hxy
    by_cases hy : y ≤ p
    · simp [step,hy,hxy.trans hy]
    · simp [step,hy]
      split <;> norm_num
  have he (x : ℝ) : c*step r x + (-c)*step l x = (Ioc l r).indicator (fun _ => c) x := by
    by_cases hx : x ≤ l
    · simp [step,hx,hx.trans hlr,not_lt_of_ge hx]
    · by_cases hy : x ≤ r
      · simp [step,hx,hy,lt_of_not_ge hx]
      · simp [step,hx,hy]
  have h := tagged_integral_linear (antitone_tagged_integral hab (hm r))
    (antitone_tagged_integral hab (hm l)) c (-c)
  simp_rw [he] at h
  have hv : (∫ x in a..b, (Ioc l r).indicator (fun _ => c) x) = c*(r-l) := by
    rw [intervalIntegral.integral_of_le hab.le, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (Ioc_subset_Ioc hal hrb), setIntegral_const, Measure.real_def,
      Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hlr), smul_eq_mul, mul_comm]
  rwa [← (tagged_measure_agreement hab h).2, hv] at h

private noncomputable def cellEnvelope {a b : ℝ} (P : TaggedPartition a b)
    (f : ℝ → ℝ) (v : Fin (P.n+1) → ℝ) (x : ℝ) : ℝ :=
  Function.update (fun y => ∑ i, (Ioc (P.points i.castSucc) (P.points i.succ)).indicator
    (fun _ => v i) y) a (f a) x

private theorem envelope_integral {a b : ℝ} (hab : a < b) (P : TaggedPartition a b)
    (f : ℝ → ℝ) (v : Fin (P.n+1) → ℝ) :
    HasTaggedIntegral (cellEnvelope P f v) a b (∑ i, v i * P.width i) := by
  apply tagged_integral_update
  apply tagged_finset_sum
  intro i _
  have hlr := (P.increasing (Fin.castSucc_lt_succ (i := i))).le
  exact tagged_cell_indicator hab (P.subinterval_subset i (left_mem_Icc.mpr hlr)).1
    hlr (P.subinterval_subset i (right_mem_Icc.mpr hlr)).2 (v i)

private theorem envelope_on_cell {a b : ℝ} (P : TaggedPartition a b)
    (f : ℝ → ℝ) (v : Fin (P.n+1) → ℝ) {x : ℝ} (hx : x ∈ Ioc a b)
    {i : Fin (P.n+1)} (hi : x ∈ Ioc (P.points i.castSucc) (P.points i.succ)) :
    cellEnvelope P f v x = v i := by
  classical
  rw [cellEnvelope, Function.update_of_ne (ne_of_gt hx.1), Finset.sum_eq_single i]
  · simp [indicator_of_mem hi]
  · intro j _ hji
    exact indicator_of_notMem (fun hj => hji (Ch13.tagged_half_open_unique P hj hi)) _
  · simp

private theorem darboux_envelopes {a b : ℝ} (P : TaggedPartition a b)
    (f : ℝ → ℝ) (M : ℝ) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    ∀ x ∈ Icc a b, cellEnvelope P f (fun i => sInf (f '' P.closedCell i)) x ≤ f x ∧
      f x ≤ cellEnvelope P f (fun i => sSup (f '' P.closedCell i)) x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with he | he
  · subst x
    simp [cellEnvelope]
  · have hx' : x ∈ Ioc a b := ⟨he,hx.2⟩
    obtain ⟨i,hi⟩ := Ch13.tagged_half_open_cover P hx'
    rw [envelope_on_cell P f _ hx' hi, envelope_on_cell P f _ hx' hi]
    have hmem : f x ∈ f '' P.closedCell i := mem_image_of_mem f (Ioc_subset_Icc_self hi)
    exact ⟨csInf_le ⟨-M, by rintro _ ⟨y,hy,rfl⟩; exact (abs_le.mp (hf y (P.subinterval_subset i hy))).1⟩ hmem,
      le_csSup ⟨M, by rintro _ ⟨y,hy,rfl⟩; exact (abs_le.mp (hf y (P.subinterval_subset i hy))).2⟩ hmem⟩

private theorem tagged_of_integrable_brackets {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (h : ∀ ε > 0, ∃ l u : ℝ → ℝ, ∃ L U : ℝ,
      HasTaggedIntegral l a b L ∧ HasTaggedIntegral u a b U ∧
      (∀ x ∈ Icc a b, l x ≤ f x ∧ f x ≤ u x) ∧ U-L < ε) :
    ∃ I, HasTaggedIntegral f a b I := by
  apply (tagged_cauchy_criterion hab f).2
  intro ε hε
  obtain ⟨l,u,L,U,hl,hu,hb,hgap⟩ := h (ε/3) (by positivity)
  obtain ⟨d,hd,hlo⟩ := (tagged_integral_iff _ _ _ _).1 hl (ε/3) (by positivity)
  obtain ⟨e,he,hup⟩ := (tagged_integral_iff _ _ _ _).1 hu (ε/3) (by positivity)
  refine ⟨min d e,lt_min hd he,?_⟩
  have bounds (Q : TaggedPartition a b) (hq : Q.mesh < min d e) :
      L - ε/3 < Q.riemannSum f ∧ Q.riemannSum f < U + ε/3 := by
    have hcell (i : Fin (Q.n+1)) := hb _ (Q.subinterval_subset i (Q.tag_mem i))
    have hw (i : Fin (Q.n+1)) : 0 ≤ Q.width i :=
      sub_nonneg.mpr (Q.increasing (Fin.castSucc_lt_succ (i := i))).le
    have hlq : Q.riemannSum l ≤ Q.riemannSum f :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcell i).1 (hw i)
    have huq : Q.riemannSum f ≤ Q.riemannSum u :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcell i).2 (hw i)
    have h₁ := (abs_lt.mp (hlo Q (hq.trans_le (min_le_left _ _)))).1
    have h₂ := (abs_lt.mp (hup Q (hq.trans_le (min_le_right _ _)))).2
    exact ⟨by linarith,by linarith⟩
  intro Q R hq hr
  rw [abs_lt]
  exact ⟨by linarith [(bounds Q hq).1,(bounds R hr).2],
    by linarith [(bounds Q hq).2,(bounds R hr).1]⟩

/-- Small gaps on some partitions suffice, by bracketing fine sums between
the tagged integrals of the corresponding step functions. -/
theorem tagged_integrable_of_darboux_gap {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (M : ℝ) (hf : ∀ x ∈ Icc a b, |f x| ≤ M)
    (h : ∀ ε > 0, ∃ P : TaggedPartition a b, P.upperSum f - P.lowerSum f < ε) :
    ∃ I, HasTaggedIntegral f a b I := by
  apply tagged_of_integrable_brackets hab f
  intro ε hε
  obtain ⟨P,hP⟩ := h ε hε
  exact ⟨_,_,P.lowerSum f,P.upperSum f,envelope_integral hab P f _,
    envelope_integral hab P f _,darboux_envelopes P f M hf,hP⟩

theorem tagged_darboux_criterion {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (M : ℝ) (hf : ∀ x ∈ Icc a b, |f x| ≤ M) :
    ((∃ I, HasTaggedIntegral f a b I) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b,
        P.mesh < δ → P.upperSum f - P.lowerSum f < ε) ∧
    ((∃ I, HasTaggedIntegral f a b I) ↔
      ∀ ε > 0, ∃ P : TaggedPartition a b, P.upperSum f - P.lowerSum f < ε) := by
  have h₁ : (∃ I, HasTaggedIntegral f a b I) →
      ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b,
        P.mesh < δ → P.upperSum f - P.lowerSum f < ε := by
    rintro ⟨I,hi⟩
    exact tagged_integral_implies_small_darboux_gap hab f hi
  have h₂ := small_darboux_gap_exists hab f
  have h₃ := tagged_integrable_of_darboux_gap hab f M hf
  exact ⟨⟨h₁,h₃ ∘ h₂⟩,⟨h₂ ∘ h₁,h₃⟩⟩

theorem tagged_darboux_values {a b I : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (h : HasTaggedIntegral f a b I) :
    sSup (range fun P : TaggedPartition a b => P.lowerSum f) = I ∧
      sInf (range fun P : TaggedPartition a b => P.upperSum f) = I := by
  obtain ⟨M,_,hf⟩ := tagged_integrable_bounded hab h
  have hb (P : TaggedPartition a b) : P.lowerSum f ≤ I ∧ I ≤ P.upperSum f := by
    exact ⟨tagged_integral_mono hab (envelope_integral hab P f _) h
      (fun x hx => (darboux_envelopes P f M hf x hx).1),
      tagged_integral_mono hab h (envelope_integral hab P f _)
      (fun x hx => (darboux_envelopes P f M hf x hx).2)⟩
  let L := range fun P : TaggedPartition a b => P.lowerSum f
  let U := range fun P : TaggedPartition a b => P.upperSum f
  let P₀ := uniformPartition hab 0
  have hL : L.Nonempty := ⟨P₀.lowerSum f, ⟨P₀,rfl⟩⟩
  have hU : U.Nonempty := ⟨P₀.upperSum f, ⟨P₀,rfl⟩⟩
  have hl : ∀ x ∈ L, x ≤ I := by rintro _ ⟨P,rfl⟩; exact (hb P).1
  have hu : ∀ x ∈ U, I ≤ x := by rintro _ ⟨P,rfl⟩; exact (hb P).2
  have hLS := csSup_le hL hl
  have hUI := le_csInf hU hu
  change sSup L = I ∧ sInf U = I
  have hgap := small_darboux_gap_exists hab f (tagged_integral_implies_small_darboux_gap hab f h)
  constructor
  · apply le_antisymm hLS
    by_contra! hlt
    obtain ⟨P,hP⟩ := hgap _ (sub_pos.mpr hlt)
    have hv : P.lowerSum f ≤ sSup L := le_csSup ⟨I,hl⟩ ⟨P,rfl⟩
    linarith [(hb P).2]
  · apply le_antisymm _ hUI
    by_contra! hlt
    obtain ⟨P,hP⟩ := hgap _ (sub_pos.mpr hlt)
    have hv : sInf U ≤ P.upperSum f := csInf_le ⟨I,hu⟩ ⟨P,rfl⟩
    linarith [(hb P).1]

private theorem envelope_on_interval {a b s t : ℝ} (hst : s < t)
    (P : TaggedPartition a b) (f : ℝ → ℝ) (v : Fin (P.n+1) → ℝ) :
    HasTaggedIntegral (cellEnvelope P f v) s t (∫ x in s..t, cellEnvelope P f v x) := by
  suffices ∃ I, HasTaggedIntegral (cellEnvelope P f v) s t I by
    obtain ⟨I,hI⟩ := this
    rw [(tagged_measure_agreement hst hI).2]
    exact hI
  classical
  let step (p x : ℝ) : ℝ := if x ≤ p then 1 else 0
  have hm (p : ℝ) : AntitoneOn (step p) (Icc s t) := by
    intro x _ y _ hxy
    by_cases hy : y ≤ p
    · simp [step,hy,hxy.trans hy]
    · simp [step,hy]
      split <;> norm_num
  let coeff (i : Fin (P.n+1)) :=
    v i * (∫ x in s..t, step (P.points i.succ) x) +
      (-v i) * (∫ x in s..t, step (P.points i.castSucc) x)
  refine ⟨∑ i, coeff i, tagged_integral_update (tagged_finset_sum Finset.univ _ coeff ?_) a (f a)⟩
  intro i _
  let l := P.points i.castSucc
  let r := P.points i.succ
  have hlr : l ≤ r := (P.increasing (Fin.castSucc_lt_succ (i := i))).le
  have he (x : ℝ) : v i*step r x + (-v i)*step l x =
      (Ioc l r).indicator (fun _ => v i) x := by
    by_cases hx : x ≤ l
    · simp [step,hx,hx.trans hlr,not_lt_of_ge hx]
    · by_cases hy : x ≤ r
      · simp [step,hx,hy,lt_of_not_ge hx]
      · simp [step,hx,hy]
  have h := tagged_integral_linear (antitone_tagged_integral hst (hm r))
    (antitone_tagged_integral hst (hm l)) (v i) (-v i)
  simpa only [he] using h

/-- Restrict the step bounds to each side of the split; their gap cannot increase. -/
theorem tagged_adjacent_restrict {a c b I : ℝ} {f : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (h : HasTaggedIntegral f a b I) :
    (∃ J, HasTaggedIntegral f a c J) ∧ (∃ K, HasTaggedIntegral f c b K) := by
  have hab := hac.trans hcb
  obtain ⟨M,_,hf⟩ := tagged_integrable_bounded hab h
  have hgap := small_darboux_gap_exists hab f (tagged_integral_implies_small_darboux_gap hab f h)
  have restrict {s t : ℝ} (hst : s < t) (hsub : Icc s t ⊆ Icc a b)
      (gap_le : ∀ l u : ℝ → ℝ, (∀ x ∈ Icc a b, l x ≤ u x) →
        IntervalIntegrable l volume a c → IntervalIntegrable l volume c b →
        IntervalIntegrable u volume a c → IntervalIntegrable u volume c b →
        (∫ x in s..t, u x) - (∫ x in s..t, l x) ≤
          (∫ x in a..b, u x) - (∫ x in a..b, l x)) :
      ∃ J, HasTaggedIntegral f s t J := by
    apply tagged_of_integrable_brackets hst f
    intro ε hε
    obtain ⟨P,hP⟩ := hgap ε hε
    let lv := fun i => sInf (f '' P.closedCell i)
    let uv := fun i => sSup (f '' P.closedCell i)
    let l := cellEnvelope P f lv
    let u := cellEnvelope P f uv
    have hb := darboux_envelopes P f M hf
    refine ⟨l,u,_,_,envelope_on_interval hst P f lv,envelope_on_interval hst P f uv,
      fun x hx => hb x (hsub hx),?_⟩
    have he := gap_le l u (fun x hx => (hb x hx).1.trans (hb x hx).2)
      (tagged_measure_agreement hac (envelope_on_interval hac P f lv)).1
      (tagged_measure_agreement hcb (envelope_on_interval hcb P f lv)).1
      (tagged_measure_agreement hac (envelope_on_interval hac P f uv)).1
      (tagged_measure_agreement hcb (envelope_on_interval hcb P f uv)).1
    rw [(tagged_measure_agreement hab (envelope_integral hab P f lv)).2,
      (tagged_measure_agreement hab (envelope_integral hab P f uv)).2] at he
    exact he.trans_lt hP
  constructor
  · apply restrict hac (Icc_subset_Icc_right hcb.le)
    intro l u hp hl₁ hl₂ hu₁ hu₂
    rw [← intervalIntegral.integral_add_adjacent_intervals hl₁ hl₂,
      ← intervalIntegral.integral_add_adjacent_intervals hu₁ hu₂]
    have hm := intervalIntegral.integral_mono_on hcb.le hl₂ hu₂
      (fun x hx => hp x (Icc_subset_Icc_left hac.le hx))
    linarith
  · apply restrict hcb (Icc_subset_Icc_left hac.le)
    intro l u hp hl₁ hl₂ hu₁ hu₂
    rw [← intervalIntegral.integral_add_adjacent_intervals hl₁ hl₂,
      ← intervalIntegral.integral_add_adjacent_intervals hu₁ hu₂]
    have hm := intervalIntegral.integral_mono_on hac.le hl₁ hu₁
      (fun x hx => hp x (Icc_subset_Icc_right hcb.le hx))
    linarith

private theorem envelope_outside {a b : ℝ} (P : TaggedPartition a b)
    (f : ℝ → ℝ) (v : Fin (P.n+1) → ℝ) {x : ℝ} (hx : x ∉ Icc a b) :
    cellEnvelope P f v x = 0 := by
  have hne : x ≠ a := by
    intro he
    have hleft : P.points 0 ∈ Icc a b :=
      P.subinterval_subset 0 (left_mem_Icc.mpr (P.increasing.monotone (Fin.zero_le _)))
    exact hx (by simpa only [P.first, he] using hleft)
  rw [cellEnvelope, Function.update_of_ne hne]
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx (P.subinterval_subset i (Ioc_subset_Icc_self hi))

private theorem joined_envelope_integral {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (P : TaggedPartition a c) (Q : TaggedPartition c b) (f : ℝ → ℝ)
    (v : Fin (P.n+1) → ℝ) (w : Fin (Q.n+1) → ℝ) :
    HasTaggedIntegral (Function.update (fun x => cellEnvelope P f v x +
      cellEnvelope Q f w x) c (f c)) a b ((∑ i, v i * P.width i) + ∑ i, w i * Q.width i) := by
  let l := cellEnvelope P f v
  let r := cellEnvelope Q f w
  have hab := hac.trans hcb
  have hl := envelope_on_interval hab P f v
  have hr := envelope_on_interval hab Q f w
  have hlc : (∫ x in c..b, l x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hcb.le
      (f := l) (g := fun _ => 0) (fun x hx => envelope_outside P f v
        (fun hm => (not_lt_of_ge hm.2) hx.1))]
    simp
  have hra : (∫ x in a..c, r x) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hac.le
      (f := r) (g := fun _ => 0) (fun x hx => envelope_outside Q f w
        (fun hm => (not_lt_of_ge hm.1) hx.2))]
    simp
  have hl' := intervalIntegral.integral_add_adjacent_intervals
    (tagged_measure_agreement hac (envelope_on_interval hac P f v)).1
    (tagged_measure_agreement hcb (envelope_on_interval hcb P f v)).1
  have hr' := intervalIntegral.integral_add_adjacent_intervals
    (tagged_measure_agreement hac (envelope_on_interval hac Q f w)).1
    (tagged_measure_agreement hcb (envelope_on_interval hcb Q f w)).1
  change (∫ x in a..c, l x) + (∫ x in c..b, l x) = (∫ x in a..b, l x) at hl'
  change (∫ x in a..c, r x) + (∫ x in c..b, r x) = (∫ x in a..b, r x) at hr'
  rw [hlc, add_zero, (tagged_measure_agreement hac (envelope_integral hac P f v)).2] at hl'
  rw [hra, zero_add, (tagged_measure_agreement hcb (envelope_integral hcb Q f w)).2] at hr'
  rw [hl', hr']
  exact tagged_integral_update (by simpa using tagged_integral_linear hl hr 1 1) c (f c)

theorem tagged_adjacent_glue {a c b J K : ℝ} {f : ℝ → ℝ}
    (hac : a < c) (hcb : c < b)
    (hl : HasTaggedIntegral f a c J) (hr : HasTaggedIntegral f c b K) :
    ∃ I, HasTaggedIntegral f a b I := by
  apply tagged_of_integrable_brackets (hac.trans hcb) f
  intro ε hε
  obtain ⟨Ml,_,hfl⟩ := tagged_integrable_bounded hac hl
  obtain ⟨Mr,_,hfr⟩ := tagged_integrable_bounded hcb hr
  obtain ⟨P,hP⟩ := small_darboux_gap_exists hac f
    (tagged_integral_implies_small_darboux_gap hac f hl) (ε/2) (by positivity)
  obtain ⟨Q,hQ⟩ := small_darboux_gap_exists hcb f
    (tagged_integral_implies_small_darboux_gap hcb f hr) (ε/2) (by positivity)
  refine ⟨_,_,_,_,
    joined_envelope_integral hac hcb P Q f (fun i => sInf (f '' P.closedCell i))
      (fun i => sInf (f '' Q.closedCell i)),
    joined_envelope_integral hac hcb P Q f (fun i => sSup (f '' P.closedCell i))
      (fun i => sSup (f '' Q.closedCell i)),?_,?_⟩
  · intro x hx
    rcases lt_trichotomy x c with hlt | heq | hgt
    · simp only [Function.update_of_ne hlt.ne, envelope_outside Q f _ (fun hm => (not_lt_of_ge hm.1) hlt), add_zero]
      exact darboux_envelopes P f Ml hfl x ⟨hx.1,hlt.le⟩
    · simp [heq]
    · simp only [Function.update_of_ne hgt.ne', envelope_outside P f _ (fun hm => (not_lt_of_ge hm.2) hgt), zero_add]
      exact darboux_envelopes Q f Mr hfr x ⟨hgt.le,hx.2⟩
  · change (P.upperSum f + Q.upperSum f) - (P.lowerSum f + Q.lowerSum f) < ε
    linarith

/-- Adjacent intervals have a tagged integral exactly when both pieces do,
and the integral of the union is the sum of the two values. -/
theorem tagged_adjacent_iff {a c b I : ℝ} {f : ℝ → ℝ} (hac : a < c) (hcb : c < b) :
    HasTaggedIntegral f a b I ↔ ∃ J K,
      HasTaggedIntegral f a c J ∧ HasTaggedIntegral f c b K ∧ I = J+K := by
  constructor
  · intro h
    obtain ⟨⟨J,hl⟩,⟨K,hr⟩⟩ := tagged_adjacent_restrict hac hcb h
    exact ⟨J,K,hl,hr,tagged_adjacent_values hac hcb h hl hr⟩
  · rintro ⟨J,K,hl,hr,rfl⟩
    obtain ⟨I,h⟩ := tagged_adjacent_glue hac hcb hl hr
    rwa [tagged_adjacent_values hac hcb h hl hr] at h

theorem tagged_step_example {a c b : ℝ} (hac : a < c) (hcb : c < b) :
    HasTaggedIntegral ((Icc a c).indicator fun _ => (1 : ℝ)) a b (c-a) ∧
    ∀ t ∈ Icc a b, (∫ x in a..t, (Icc a c).indicator (fun _ => (1 : ℝ)) x) =
      min t c - a := by
  constructor
  · have h := tagged_integral_update
      (tagged_cell_indicator (hac.trans hcb) le_rfl hac.le hcb.le 1) a 1
    have he : Function.update ((Ioc a c).indicator (fun _ => (1:ℝ))) a 1 =
        (Icc a c).indicator (fun _ => (1:ℝ)) := by
      funext x
      by_cases hx : x = a
      · subst x
        simp [hac.le]
      · rw [Function.update_of_ne hx]
        have hm : x ∈ Ioc a c ↔ x ∈ Icc a c := by
          simp only [mem_Ioc, mem_Icc, lt_iff_le_and_ne]
          tauto
        by_cases hs : x ∈ Icc a c <;> simp [hs,hm]
    rwa [he, one_mul] at h
  · intro t ht
    have hmin : a ≤ min t c := le_min ht.1 hac.le
    have he : Ioc a t ∩ Icc a c = Ioc a (min t c) := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Icc, le_min_iff]
      exact ⟨fun h => ⟨h.1.1,h.1.2,h.2.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.1.le,h.2.2⟩⟩
    rw [intervalIntegral.integral_of_le ht.1, setIntegral_indicator measurableSet_Icc,
      he,setIntegral_const,Measure.real_def,Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hmin),smul_eq_mul,mul_one]

end Ch09
