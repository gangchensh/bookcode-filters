import Textbook.Ch09.Integration

namespace Ch09

open Set MeasureTheory
open scoped Interval

/-- The equal-width partition with left endpoints as tags. -/
noncomputable def uniformPartition {a b : ℝ} (hab : a < b) (n : ℕ) : TaggedPartition a b where
  n := n
  points := fun i => a + (i.val : ℝ) / ((n : ℝ) + 1) * (b-a)
  first := by simp
  last := by
    simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [div_self (by positivity), one_mul]
    ring
  increasing := by
    intro i j hij
    have h : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    exact add_lt_add_right
      (mul_lt_mul_of_pos_right (div_lt_div_of_pos_right h (by positivity : 0 < (n : ℝ)+1)) (sub_pos.mpr hab)) _
  tag := fun i => a + (i.val : ℝ) / ((n : ℝ) + 1) * (b-a)
  tag_mem := by
    intro i
    refine ⟨le_rfl, ?_⟩
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hab.le)
    apply div_le_div_of_nonneg_right _ (by positivity)
    simp [Fin.val_succ]

theorem uniform_width {a b : ℝ} (hab : a < b) (n : ℕ) (i : Fin (n+1)) :
    (uniformPartition hab n).width i = (b-a)/((n:ℝ)+1) := by
  simp only [TaggedPartition.width, uniformPartition, Fin.val_succ, Fin.val_castSucc,
    Nat.cast_add, Nat.cast_one]
  ring

theorem uniform_mesh {a b : ℝ} (hab : a < b) (n : ℕ) :
    (uniformPartition hab n).mesh = (b-a)/((n:ℝ)+1) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _ => (uniform_width hab n i).le)
  · exact (uniform_width hab n 0).ge.trans
      (Finset.le_sup' (f := (uniformPartition hab n).width) (Finset.mem_univ 0))

theorem arbitrarily_fine {a b : ℝ} (hab : a < b) :
    ∀ δ > 0, ∃ P : TaggedPartition a b, P.mesh < δ := by
  intro δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt ((b-a)/δ)
  refine ⟨uniformPartition hab n, ?_⟩
  rw [uniform_mesh, div_lt_iff₀ (by positivity)]
  have h := (div_lt_iff₀ hδ).mp hn
  nlinarith

theorem tagged_filter_proper {a b : ℝ} (hab : a < b) :
    Ch02.IsProper (fineFilter (TaggedPartition.mesh (a := a) (b := b))) := by
  exact fineFilter_proper _ (arbitrarily_fine hab)

theorem sum_endpoint_differences {n : ℕ} (g : Fin (n+2) → ℝ) :
    (∑ i : Fin (n+1), (g i.succ - g i.castSucc)) = g (Fin.last (n+1)) - g 0 := by
  have h := (Fin.sum_univ_succ g).symm.trans (Fin.sum_univ_castSucc g)
  rw [Finset.sum_sub_distrib]
  linarith

theorem tagged_constant_sum {a b : ℝ} (P : TaggedPartition a b) (c : ℝ) :
    P.riemannSum (fun _ => c) = (b-a)*c := by
  unfold TaggedPartition.riemannSum TaggedPartition.width
  rw [← Finset.mul_sum, sum_endpoint_differences, P.first, P.last, mul_comm]

theorem tagged_constant_integral {a b : ℝ} (c : ℝ) :
    HasTaggedIntegral (fun _ => c) a b ((b-a)*c) := by
  apply (tagged_integral_iff _ _ _ _).2
  intro ε hε
  exact ⟨1, by norm_num, fun P _ => by simpa [tagged_constant_sum] using hε⟩

theorem tagged_newton_leibniz {F f : ℝ → ℝ} {a b I : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hi : HasTaggedIntegral f a b I) : I = F b - F a := by
  classical
  have sums : ∀ ε > 0, |F b-F a-I| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδI⟩ := (tagged_integral_iff _ _ _ _).1 hi ε hε
    obtain ⟨P, hP⟩ := arbitrarily_fine hab δ hδ
    have bounds (i : Fin (P.n+1)) :
        Icc (P.points i.castSucc) (P.points i.succ) ⊆ Icc a b := by
      apply Icc_subset_Icc
      · exact P.first.ge.trans (P.increasing.monotone (Fin.zero_le _))
      · exact (P.increasing.monotone (Fin.le_last _)).trans P.last.le
    have mvt (i : Fin (P.n+1)) : ∃ t ∈ Ioo (P.points i.castSucc) (P.points i.succ),
        f t * P.width i = F (P.points i.succ) - F (P.points i.castSucc) := by
      have hlt : P.points i.castSucc < P.points i.succ := P.increasing (Fin.castSucc_lt_succ (i := i))
      have localDeriv (t : ℝ) (ht : t ∈ Ioo (P.points i.castSucc) (P.points i.succ)) :
          HasDerivAt F (f t) t := by
        have hleft := (bounds i (left_mem_Icc.mpr hlt.le)).1
        have hright := (bounds i (right_mem_Icc.mpr hlt.le)).2
        exact hd t ⟨hleft.trans_lt ht.1, ht.2.trans_le hright⟩
      obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope F hlt (hF.mono (bounds i))
        (fun t ht => (localDeriv t ht).differentiableAt.differentiableWithinAt)
      rw [(localDeriv t ht).deriv] at he
      exact ⟨t, ht, (eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp he⟩
    choose t ht he using mvt
    let Q : TaggedPartition a b := { P with tag := t, tag_mem := fun i => Ioo_subset_Icc_self (ht i) }
    have hQ : Q.mesh < δ := hP
    have hv : Q.riemannSum f = F b - F a := by
      calc
        _ = ∑ i : Fin (P.n+1), (F (P.points i.succ) - F (P.points i.castSucc)) :=
          Finset.sum_congr rfl (fun i _ => he i)
        _ = _ := by simpa [P.last, P.first] using sum_endpoint_differences (F ∘ P.points)
    simpa only [hv] using hδI Q hQ
  have hzero : |F b-F a-I| = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun ε hε => by simpa using (sums ε hε).le)
      (abs_nonneg _)
  linarith [abs_eq_zero.mp hzero]

theorem tagged_integral_unique {a b I J : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hI : HasTaggedIntegral f a b I) (hJ : HasTaggedIntegral f a b J) : I = J :=
  Ch03Rules.real_limit_unique (tagged_filter_proper hab) hI hJ

theorem accumulation_at_continuous_point {f : ℝ → ℝ} {a b : ℝ}
    (hi : IntervalIntegrable f volume a b)
    (hm : StronglyMeasurableAtFilter f (nhds b)) (hc : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  intervalIntegral.integral_hasDerivAt_right hi hm hc

theorem interval_newton_leibniz {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hi : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) = F b-F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd hi

theorem tagged_sum_linear {a b : ℝ} (P : TaggedPartition a b) (f g : ℝ → ℝ) (c d : ℝ) :
    P.riemannSum (fun x => c*f x+d*g x) = c*P.riemannSum f+d*P.riemannSum g := by
  simp only [TaggedPartition.riemannSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem tagged_integral_linear {a b I J : ℝ} {f g : ℝ → ℝ}
    (hf : HasTaggedIntegral f a b I) (hg : HasTaggedIntegral g a b J) (c d : ℝ) :
    HasTaggedIntegral (fun x => c*f x+d*g x) a b (c*I+d*J) := by
  apply (tagged_integral_iff _ _ _ _).2
  intro ε hε
  let η := ε/(|c|+|d|+1)
  have hD : 0 < |c|+|d|+1 := by positivity
  have hη : 0 < η := div_pos hε hD
  obtain ⟨δ₁, hp₁, h₁⟩ := (tagged_integral_iff _ _ _ _).1 hf η hη
  obtain ⟨δ₂, hp₂, h₂⟩ := (tagged_integral_iff _ _ _ _).1 hg η hη
  refine ⟨min δ₁ δ₂, lt_min hp₁ hp₂, ?_⟩
  intro P hP
  rw [tagged_sum_linear, show c*P.riemannSum f+d*P.riemannSum g-(c*I+d*J) =
    c*(P.riemannSum f-I)+d*(P.riemannSum g-J) by ring]
  calc
    _ ≤ |c*(P.riemannSum f-I)|+|d*(P.riemannSum g-J)| := abs_add_le _ _
    _ ≤ |c| * η + |d| * η := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (h₁ P (hP.trans_le (min_le_left _ _))).le (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (h₂ P (hP.trans_le (min_le_right _ _))).le (abs_nonneg _))
    _ < ε := by
      have he : η*(|c|+|d|+1)=ε := div_mul_cancel₀ _ hD.ne'
      nlinarith

theorem TaggedPartition.subinterval_subset {a b : ℝ} (P : TaggedPartition a b)
    (i : Fin (P.n+1)) : Icc (P.points i.castSucc) (P.points i.succ) ⊆ Icc a b := by
  apply Icc_subset_Icc
  · exact P.first.ge.trans (P.increasing.monotone (Fin.zero_le _))
  · exact (P.increasing.monotone (Fin.le_last _)).trans P.last.le

theorem continuous_tagged_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    HasTaggedIntegral f a b (∫ x in a..b, f x) := by
  apply (tagged_integral_iff _ _ _ _).2
  intro ε hε
  let η := ε / (2*(b-a))
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ, hδ, ?_⟩
  intro P hP
  let A := fun t : ℝ => ∫ x in a..t, f x
  have hseg (i : Fin (P.n+1)) :
      |f (P.tag i)*P.width i-(A (P.points i.succ)-A (P.points i.castSucc))| ≤ η*P.width i := by
    let l := P.points i.castSucc
    let r := P.points i.succ
    have hlr : l ≤ r := (P.increasing (Fin.castSucc_lt_succ (i := i))).le
    have hsub : Icc l r ⊆ Icc a b := P.subinterval_subset i
    have hfsub : IntervalIntegrable f volume l r :=
      (hf.mono hsub).intervalIntegrable_of_Icc hlr
    have hal : a ≤ l := (hsub (left_mem_Icc.mpr hlr)).1
    have hla : IntervalIntegrable f volume a l :=
      (hf.mono (Icc_subset_Icc_right (hsub (left_mem_Icc.mpr hlr)).2)).intervalIntegrable_of_Icc hal
    have hA : A r-A l = ∫ x in l..r, f x := by
      have h := intervalIntegral.integral_add_adjacent_intervals hla hfsub
      dsimp [A]
      linarith
    have hwidth : r-l ≤ P.mesh :=
      Finset.le_sup' (f := P.width) (Finset.mem_univ i)
    have hbound : ∀ x ∈ Ι l r, ‖f (P.tag i)-f x‖ ≤ η := by
      rw [uIoc_of_le hlr]
      intro x hx
      have ht := P.tag_mem i
      have hx' : x ∈ Icc l r := Ioc_subset_Icc_self hx
      have hdist : dist (P.tag i) x ≤ r-l := by
        rw [Real.dist_eq, abs_le]
        exact ⟨by linarith [ht.1, hx'.2], by linarith [ht.2, hx'.1]⟩
      rw [Real.norm_eq_abs, ← Real.dist_eq]
      exact (huc _ (hsub ht) _ (hsub hx') (hdist.trans_lt (hwidth.trans_lt hP))).le
    change |f (P.tag i)*(r-l)-(A r-A l)| ≤ η*(r-l)
    rw [hA, mul_comm (f (P.tag i)), ← integral_constant,
      ← intervalIntegral.integral_sub (intervalIntegrable_const) hfsub]
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlr), mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have htot : (∑ i : Fin (P.n+1), (A (P.points i.succ)-A (P.points i.castSucc))) =
      ∫ x in a..b, f x := by
    simpa [A, P.first, P.last] using sum_endpoint_differences (A ∘ P.points)
  have hw : (∑ i : Fin (P.n+1), P.width i) = b-a := by
    unfold TaggedPartition.width
    rw [sum_endpoint_differences, P.first, P.last]
  calc
    _ = |∑ i : Fin (P.n+1), (f (P.tag i)*P.width i -
          (A (P.points i.succ)-A (P.points i.castSucc)))| := by
      rw [Finset.sum_sub_distrib, htot]
      rfl
    _ ≤ ∑ i : Fin (P.n+1), |f (P.tag i)*P.width i -
          (A (P.points i.succ)-A (P.points i.castSucc))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (P.n+1), η*P.width i := Finset.sum_le_sum (fun i _ => hseg i)
    _ = η*(b-a) := by rw [← Finset.mul_sum, hw]
    _ < ε := by
      have he : η*(2*(b-a)) = ε := div_mul_cancel₀ _ (by linarith)
      linarith

theorem continuous_integral_agreement {f : ℝ → ℝ} {a b I : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    HasTaggedIntegral f a b I ↔ I = ∫ x in a..b, f x := by
  constructor
  · intro hi
    exact tagged_integral_unique hab hi (continuous_tagged_integral hab hf)
  · rintro rfl
    exact continuous_tagged_integral hab hf

theorem tagged_integral_square :
    HasTaggedIntegral (fun x : ℝ => x^2) 0 1 (1/3) := by
  rw [← integral_square]
  exact continuous_tagged_integral zero_lt_one ((continuous_id.pow 2).continuousOn)

theorem tagged_integral_id :
    HasTaggedIntegral (fun x : ℝ => x) 0 1 (1/2) := by
  rw [← integral_linear]
  exact continuous_tagged_integral zero_lt_one continuous_id.continuousOn

theorem tagged_cauchy_criterion {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    (∃ I, HasTaggedIntegral f a b I) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ P Q : TaggedPartition a b,
      P.mesh < δ → Q.mesh < δ → |P.riemannSum f-Q.riemannSum f| < ε := by
  constructor
  · rintro ⟨I, hI⟩ ε hε
    obtain ⟨δ, hδ, hb⟩ := (tagged_integral_iff _ _ _ _).1 hI (ε/2) (half_pos hε)
    refine ⟨δ, hδ, fun P Q hp hq => ?_⟩
    have ht := abs_sub_le (P.riemannSum f) I (Q.riemannSum f)
    rw [abs_sub_comm I] at ht
    linarith [hb P hp, hb Q hq]
  · intro h
    let L := Ch02.toMathlib (fineFilter (TaggedPartition.mesh (a := a) (b := b)))
    let S := TaggedPartition.riemannSum (a := a) (b := b) f
    haveI : Filter.NeBot L :=
      ⟨fun hbot => tagged_filter_proper hab (Filter.empty_mem_iff_bot.mpr hbot)⟩
    have hc : Cauchy (Filter.map S L) := by
      apply Metric.cauchy_iff.mpr
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hb⟩ := h ε hε
      let B : Set (TaggedPartition a b) := {P | P.mesh < δ}
      refine ⟨S '' B, ?_, ?_⟩
      · change ∃ d > 0, {P : TaggedPartition a b | P.mesh < d} ⊆ S ⁻¹' (S '' B)
        exact ⟨δ, hδ, fun P hP => ⟨P, hP, rfl⟩⟩
      · rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩
        simpa [Real.dist_eq] using hb P Q hP hQ
    obtain ⟨I, hI⟩ := cauchy_map_iff_exists_tendsto.mp hc
    refine ⟨I, (tagged_integral_iff _ _ _ _).2 fun ε hε => ?_⟩
    have he := hI.eventually (Metric.ball_mem_nhds I hε)
    change ∃ δ > 0, {P : TaggedPartition a b | P.mesh < δ} ⊆
      S ⁻¹' Metric.ball I ε at he
    obtain ⟨δ, hδ, hball⟩ := he
    exact ⟨δ, hδ, fun P hP => by simpa [Metric.mem_ball, Real.dist_eq, S] using hball hP⟩

theorem tagged_integral_mono {a b I J : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : HasTaggedIntegral f a b I) (hg : HasTaggedIntegral g a b J)
    (hle : ∀ x ∈ Icc a b, f x ≤ g x) : I ≤ J := by
  by_contra! hn
  let ε := (I-J)/3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨δ, hδ, hb⟩ := (tagged_integral_iff _ _ _ _).1 hf ε hε
  obtain ⟨η, hη, hc⟩ := (tagged_integral_iff _ _ _ _).1 hg ε hε
  obtain ⟨P, hp⟩ := arbitrarily_fine hab (min δ η) (lt_min hδ hη)
  have hs : P.riemannSum f ≤ P.riemannSum g := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hle _ (P.subinterval_subset i (P.tag_mem i)))
      (sub_nonneg.mpr (P.increasing (Fin.castSucc_lt_succ (i := i))).le)
  have h₁ := (abs_lt.mp (hb P (hp.trans_le (min_le_left _ _)))).1
  have h₂ := (abs_lt.mp (hc P (hp.trans_le (min_le_right _ _)))).2
  dsimp [ε] at h₁ h₂
  linarith

theorem tagged_integral_bounds {a b I m M : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : HasTaggedIntegral f a b I) (h : ∀ x ∈ Icc a b, m ≤ f x ∧ f x ≤ M) :
    (b-a)*m ≤ I ∧ I ≤ (b-a)*M :=
  ⟨tagged_integral_mono hab (tagged_constant_integral m) hf (fun x hx => (h x hx).1),
    tagged_integral_mono hab hf (tagged_constant_integral M) (fun x hx => (h x hx).2)⟩

theorem tagged_integral_error {a b I J C : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : HasTaggedIntegral f a b I) (hg : HasTaggedIntegral g a b J)
    (h : ∀ x ∈ Icc a b, |f x-g x| ≤ C) : |I-J| ≤ C*(b-a) := by
  have hd : HasTaggedIntegral (fun x => f x-g x) a b (I-J) := by
    simpa [sub_eq_add_neg] using tagged_integral_linear hf hg 1 (-1)
  have hb := tagged_integral_bounds hab hd (fun x hx => abs_le.mp (h x hx))
  apply abs_le.mpr
  constructor <;> linarith [hb.1, hb.2]

/-- The estimate for FTC I after identifying increments of the accumulation function
with the integral on the short interval. -/
theorem tagged_accumulation_increment {f : ℝ → ℝ} {a b I C : ℝ}
    (hab : a < b) (hi : HasTaggedIntegral f a b I)
    (c : ℝ) (hc : ∀ x ∈ Icc a b, |f x-c| ≤ C) :
    |I-(b-a)*c| ≤ C*(b-a) :=
  tagged_integral_error hab hi (tagged_constant_integral c) hc

theorem tagged_integral_abs_bound {a b I M : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : HasTaggedIntegral f a b I) (h : ∀ x ∈ Icc a b, |f x| ≤ M) :
    |I| ≤ M*(b-a) := by
  have hb := tagged_integral_error hab hf (tagged_constant_integral 0)
    (fun x hx => by simpa using h x hx)
  simpa using hb

theorem reversed_constant_example :
    (∫ _ : ℝ in (1:ℝ)..3, (2:ℝ)) = 4 ∧ (∫ _ : ℝ in (3:ℝ)..1, (2:ℝ)) = -4 := by
  norm_num [integral_constant]

theorem tagged_accumulation_derivative_of_increments {f A : ℝ → ℝ} {l x r : ℝ}
    (hl : l < x) (hr : x < r) (hf : ContinuousAt f x)
    (hA : ∀ u v, l < u → u < v → v < r → HasTaggedIntegral f u v (A v-A u)) :
    HasDerivAt A (f x) x := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ t in nhds x, dist (f t) (f x) < ε/2 :=
    hf.tendsto.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hlocal : Ioo l r ∩ {t | dist (f t) (f x) < ε/2} ∈ nhds x :=
    Filter.inter_mem (Ioo_mem_nhds hl hr) he
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hlocal
  have he' : ∀ᶠ y in nhdsWithin x ({x}ᶜ : Set ℝ), dist y x < δ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)
  filter_upwards [he', (self_mem_nhdsWithin : ({x}ᶜ : Set ℝ) ∈ nhdsWithin x {x}ᶜ)] with y hy hne
  have hy' := (hb hy).1
  have calc_bound (u v : ℝ) (huv : u < v) (hu : l < u) (hv : v < r)
      (hs : ∀ t ∈ Icc u v, dist t x ≤ dist y x) :
      |A v-A u-(v-u)*f x| ≤ (ε/2)*(v-u) := by
    apply tagged_accumulation_increment huv (hA u v hu huv hv)
    intro t ht
    have h := (hb ((hs t ht).trans_lt hy)).2
    exact (show |f t-f x| < ε/2 by simpa [Real.dist_eq] using h).le
  rcases lt_or_gt_of_ne (show y ≠ x from hne) with hyx | hxy
  · have hh := calc_bound y x hyx hy'.1 hr (fun t ht => by
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2),
        abs_of_neg (sub_neg.mpr hyx)]
      linarith [ht.1])
    have hz : slope A x y-f x = (A x-A y-(x-y)*f x)/(x-y) := by
      rw [slope_def_field]
      field_simp [sub_ne_zero.mpr hyx.ne, sub_ne_zero.mpr hyx.ne']
      ring
    rw [Real.dist_eq, hz, abs_div, abs_of_pos (sub_pos.mpr hyx),
      div_lt_iff₀ (sub_pos.mpr hyx)]
    exact hh.trans_lt (mul_lt_mul_of_pos_right (half_lt_self hε) (sub_pos.mpr hyx))
  · have hh := calc_bound x y hxy hl hy'.2 (fun t ht => by
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1),
        abs_of_pos (sub_pos.mpr hxy)]
      linarith [ht.2])
    have hz : slope A x y-f x = (A y-A x-(y-x)*f x)/(y-x) := by
      rw [slope_def_field]
      field_simp [sub_ne_zero.mpr hxy.ne']
    rw [Real.dist_eq, hz, abs_div, abs_of_pos (sub_pos.mpr hxy),
      div_lt_iff₀ (sub_pos.mpr hxy)]
    exact hh.trans_lt (mul_lt_mul_of_pos_right (half_lt_self hε) (sub_pos.mpr hxy))

end Ch09
