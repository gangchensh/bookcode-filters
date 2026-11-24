import Textbook.Ch10.Methods
import Textbook.Ch09.Tagged

namespace Ch10
open MeasureTheory Filter Set
open scoped Topology Interval

def ImproperLeft (f : ℝ → ℝ) (b L : ℝ) : Prop :=
  (∀ T, T ≤ b → IntervalIntegrable f volume T b) ∧
    Tendsto (fun T => ∫ x in T..b, f x) atBot (𝓝 L)

theorem improper_left_epsilon_iff (f : ℝ → ℝ) (b L : ℝ) :
    ImproperLeft f b L ↔
      (∀ T, T ≤ b → IntervalIntegrable f volume T b) ∧
      ∀ ε > 0, ∃ B ≤ b, ∀ T ≤ B, |(∫ x in T..b, f x)-L| < ε := by
  unfold ImproperLeft
  change ((∀ T : ℝ, T ≤ b → IntervalIntegrable f volume T b) ∧
    Tendsto (fun T : ℝᵒᵈ => ∫ x in T..b, f x) atTop (𝓝 L)) ↔ _
  rw [Metric.tendsto_atTop]
  simp only [Real.dist_eq]
  constructor
  · rintro ⟨hi,h⟩
    refine ⟨hi, fun ε hε => ?_⟩
    obtain ⟨B,hB⟩ := h ε hε
    exact ⟨min B b, min_le_right _ _, fun T hT => hB T (hT.trans (min_le_left _ _))⟩
  · rintro ⟨hi,h⟩
    exact ⟨hi, fun ε hε => by obtain ⟨B,_,hB⟩ := h ε hε; exact ⟨B,hB⟩⟩

def ImproperEndpointLeft (f : ℝ → ℝ) (a b L : ℝ) : Prop :=
  (∀ c, a < c → c ≤ b → IntervalIntegrable f volume c b) ∧
    Tendsto (fun c => ∫ x in c..b, f x) (𝓝[>] a) (𝓝 L)

def ImproperEndpointRight (f : ℝ → ℝ) (a b L : ℝ) : Prop :=
  (∀ c, a ≤ c → c < b → IntervalIntegrable f volume a c) ∧
    Tendsto (fun c => ∫ x in a..c, f x) (𝓝[<] b) (𝓝 L)

def AbsolutelyImproperRight (f : ℝ → ℝ) (a : ℝ) : Prop :=
  (∀ T, a ≤ T → IntervalIntegrable f volume a T) ∧
    ∃ L, ImproperRight (fun x => |f x|) a L

def TwoEndedImproper (f : ℝ → ℝ) (c L : ℝ) : Prop :=
  ∃ I J, ImproperLeft f c I ∧ ImproperRight f c J ∧ L=I+J

noncomputable def mass (ρ : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, ρ x
noncomputable def firstMoment (ρ : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, x*ρ x
noncomputable def centroid (ρ : ℝ → ℝ) (a b : ℝ) : ℝ := firstMoment ρ a b / mass ρ a b
noncomputable def work (F : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, F x

theorem improper_linear {f g : ℝ → ℝ} {a I J : ℝ}
    (hf : ImproperRight f a I) (hg : ImproperRight g a J) (c d : ℝ) :
    ImproperRight (fun x => c*f x+d*g x) a (c*I+d*J) := by
  refine ⟨fun T hT => ((hf.1 T hT).const_mul c).add ((hg.1 T hT).const_mul d), ?_⟩
  have H := (hf.2.const_mul c).add (hg.2.const_mul d)
  apply H.congr'
  filter_upwards [eventually_ge_atTop a] with T hT
  rw [intervalIntegral.integral_add ((hf.1 T hT).const_mul c) ((hg.1 T hT).const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem change_start {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hi : ∀ T, a ≤ T → IntervalIntegrable f volume a T) :
    ImproperRight f a L ↔ ImproperRight f b (L-∫ x in a..b, f x) := by
  have hj (T : ℝ) (hT : b ≤ T) : IntervalIntegrable f volume b T :=
    (hi T (hab.le.trans hT)).mono_set (by
      rw [uIcc_of_le hT, uIcc_of_le (hab.le.trans hT)]
      exact Icc_subset_Icc hab.le le_rfl)
  have he (T : ℝ) (hT : b ≤ T) :
      (∫ x in a..T, f x) = (∫ x in a..b, f x)+(∫ x in b..T, f x) :=
    (intervalIntegral.integral_add_adjacent_intervals (hi b hab.le) (hj T hT)).symm
  constructor
  · intro h
    refine ⟨hj, ?_⟩
    apply (h.2.sub_const _).congr'
    filter_upwards [eventually_ge_atTop b] with T hT
    rw [he T hT]
    ring
  · intro h
    refine ⟨hi, ?_⟩
    have H := (tendsto_const_nhds (x := ∫ x in a..b, f x)).add h.2
    have H' : Tendsto (fun T => (∫ x in a..b, f x)+(∫ x in b..T, f x)) atTop (𝓝 L) := by
      convert H using 1 <;> ring
    apply H'.congr'
    filter_upwards [eventually_ge_atTop b] with T hT
    exact (he T hT).symm

theorem exponential_left :
    ImproperLeft Real.exp 0 1 := by
  refine ⟨fun T _ => Real.continuous_exp.intervalIntegrable _ _, ?_⟩
  have he (T : ℝ) : (∫ x in T..0, Real.exp x)=1-Real.exp T := by
    rw [Ch09.primitive_integral (fun x _ => Real.hasDerivAt_exp x)
      (Real.continuous_exp.intervalIntegrable _ _)]
    simp
  simp_rw [he]
  simpa using tendsto_const_nhds.sub Real.tendsto_exp_atBot

theorem decreasing_substitution :
    (∫ x : ℝ in (0:ℝ)..1, Real.exp (-x)) = 1-Real.exp (-1) ∧
    (∫ y : ℝ in (-1:ℝ)..0, Real.exp y) = 1-Real.exp (-1) := by
  refine ⟨decay_truncation 1, ?_⟩
  rw [Ch09.primitive_integral (fun x _ => Real.hasDerivAt_exp x)
    (Real.continuous_exp.intervalIntegrable _ _), Real.exp_zero]

theorem folded_substitution :
    (∫ x : ℝ in (0:ℝ)..Real.pi, Real.cos x) = 0 := by
  rw [integral_cos, Real.sin_pi, Real.sin_zero, sub_zero]

theorem spring_work (k a b : ℝ) :
    work (fun x => k*x) a b = k/2*(b^2-a^2) := by
  have hd (x : ℝ) : HasDerivAt (fun t => k/2*t^2) (k*x) x := by
    convert ((hasDerivAt_id x).fun_pow 2).const_mul (k/2) using 1 <;>
      first | rfl | (simp only [Pi.sub_apply, id_eq, Pi.pow_apply]; ring)
  rw [work, Ch09.primitive_integral (fun x _ => hd x) (by
    apply Continuous.intervalIntegrable; fun_prop)]
  ring

theorem preload_work (k c a b : ℝ) :
    work (fun x => k*x+c) a b = k/2*(b^2-a^2)+c*(b-a) := by
  rw [work, intervalIntegral.integral_add (by
    apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
    ← work, spring_work, Ch09.integral_constant]
  ring

theorem power_truncation {p T : ℝ} (hp : p ≠ 1) (hT : 1 ≤ T) :
    (∫ x : ℝ in (1:ℝ)..T, x^(-p)) = (T^(1-p)-1)/(1-p) := by
  have hn : (-p:ℝ) ≠ -1 := by intro h; apply hp; linarith
  have hi := integral_rpow (a := (1:ℝ)) (b := T)
    (r := -p) (Or.inr ⟨hn, notMem_uIcc_of_lt zero_lt_one (lt_of_lt_of_le zero_lt_one hT)⟩)
  convert hi using 1 <;> simp [Real.one_rpow] <;> congr 2 <;> ring

theorem power_improper_converges {p : ℝ} (hp : 1 < p) :
    ImproperRight (fun x : ℝ => x^(-p)) 1 (1/(p-1)) := by
  have hl : Tendsto (fun T : ℝ => T^(1-p)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop (sub_pos.mpr hp) using 1 <;> congr 2 <;> ring
  refine ⟨?_, ?_⟩
  · intro T hT
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    intro x hx
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)))).continuousWithinAt
  have H := (hl.sub_const 1).div_const (1-p)
  have H' : Tendsto (fun T : ℝ => (T^(1-p)-1)/(1-p)) atTop (𝓝 (1/(p-1))) := by
    convert H using 1
    congr 1
    field_simp [show 1-p ≠ 0 by linarith]
    ring
  apply H'.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  exact (power_truncation hp.ne' hT).symm

theorem origin_power_truncation {p c : ℝ} (hp : p ≠ 1) (hc : 0 < c) :
    (∫ x : ℝ in c..1, x^(-p)) = (1-c^(1-p))/(1-p) := by
  have hn : (-p:ℝ) ≠ -1 := by intro h; apply hp; linarith
  have hi := integral_rpow (a := c) (b := (1:ℝ)) (r := -p)
    (Or.inr ⟨hn, notMem_uIcc_of_lt hc zero_lt_one⟩)
  convert hi using 1 <;> simp [Real.one_rpow] <;> congr 2 <;> ring

theorem power_tail_identity {p T : ℝ} (hp : 1 < p) (hT : 1 ≤ T) :
    1/(p-1)-(∫ x : ℝ in (1:ℝ)..T, x^(-p)) = T^(1-p)/(p-1) := by
  rw [power_truncation hp.ne' hT]
  field_simp [show 1-p ≠ 0 by linarith, show p-1 ≠ 0 by linarith]
  ring

theorem origin_power_tail_identity {p c : ℝ} (hp : p < 1) (hc : 0 < c) :
    1/(1-p)-(∫ x : ℝ in c..1, x^(-p)) = c^(1-p)/(1-p) := by
  rw [origin_power_truncation hp.ne hc]
  ring

theorem log_interval_examples :
    (∫ x : ℝ in (1:ℝ)..2, 1/x) = Real.log 2 ∧
    (∫ x : ℝ in (-2:ℝ)..(-1), 1/x) = -Real.log 2 := by
  constructor
  · simpa using integral_one_div_of_pos (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2)
  · rw [integral_one_div_of_neg (by norm_num : (-2:ℝ)<0) (by norm_num : (-1:ℝ)<0)]
    norm_num
    rw [show (1/2:ℝ) = 2⁻¹ by norm_num, Real.log_inv]

def TaggedImproperRight (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∃ A : ℝ → ℝ, (∀ T, a < T → Ch09.HasTaggedIntegral f a T (A T)) ∧
    Tendsto A atTop (𝓝 L)

theorem tagged_improper_right_iff {f : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ T, a ≤ T → ContinuousOn f (Icc a T)) :
    TaggedImproperRight f a L ↔ ImproperRight f a L := by
  constructor
  · rintro ⟨A,hA,hL⟩
    refine ⟨fun T hT => (hf T hT).intervalIntegrable_of_Icc hT, ?_⟩
    apply hL.congr'
    filter_upwards [eventually_gt_atTop a] with T hT
    exact (Ch09.continuous_integral_agreement hT (hf T hT.le)).1 (hA T hT)
  · intro h
    exact ⟨fun T => ∫ x in a..T, f x,
      fun T hT => Ch09.continuous_tagged_integral hT (hf T hT.le), h.2⟩

theorem change_variable_local {g dg f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ uIcc a b, HasDerivAt g (dg x) x)
    (hg : ContinuousOn dg (uIcc a b)) (hf : ContinuousOn f (g '' uIcc a b)) :
    (∫ x in a..b, f (g x)*dg x) = ∫ y in g a..g b, f y := by
  simpa only [smul_eq_mul, Function.comp_apply, mul_comm] using
    intervalIntegral.integral_deriv_smul_comp' hd hg hf

theorem endpoint_left_epsilon {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b) :
    ImproperEndpointLeft f a b L ↔
      (∀ c, a < c → c ≤ b → IntervalIntegrable f volume c b) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ c, a < c → c < a+δ → c ≤ b →
        |(∫ x in c..b, f x)-L| < ε := by
  rw [ImproperEndpointLeft, Metric.tendsto_nhdsWithin_nhds]
  constructor
  · rintro ⟨hi,h⟩
    refine ⟨hi, fun ε hε => ?_⟩
    obtain ⟨δ,hδ,hb⟩ := h ε hε
    refine ⟨δ,hδ,fun c hc hcδ _ => ?_⟩
    have hd : dist c a < δ := by rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hc)]; linarith
    simpa [Real.dist_eq] using hb hc hd
  · rintro ⟨hi,h⟩
    refine ⟨hi,fun ε hε => ?_⟩
    obtain ⟨δ,hδ,hb⟩ := h ε hε
    refine ⟨min δ (b-a), lt_min hδ (sub_pos.mpr hab), ?_⟩
    intro c hc hd
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hc)] at hd
    have hd₁ := hd.trans_le (min_le_left _ _)
    have hd₂ := hd.trans_le (min_le_right _ _)
    simpa [Real.dist_eq] using hb c hc (by linarith) (by linarith)

theorem scaled_decay_truncation {k : ℝ} (hk : k ≠ 0) (P T : ℝ) :
    (∫ t : ℝ in (0:ℝ)..T, P*Real.exp (-k*t)) = P/k*(1-Real.exp (-k*T)) := by
  have hd (x : ℝ) : HasDerivAt (fun t => -(P/k)*Real.exp (-k*t)) (P*Real.exp (-k*x)) x := by
    have h := ((Real.hasDerivAt_exp (-k*x)).comp x ((hasDerivAt_id x).const_mul (-k))).const_mul (-(P/k))
    convert h using 1 <;> first | rfl | (field_simp [hk] <;> ring)
  rw [Ch09.primitive_integral (fun x _ => hd x) (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.exp_zero, mul_one]
  ring

theorem scaled_decay_improper {k : ℝ} (hk : 0 < k) (P : ℝ) :
    ImproperRight (fun t : ℝ => P*Real.exp (-k*t)) 0 (P/k) := by
  refine ⟨fun T _ => (by apply Continuous.intervalIntegrable; fun_prop), ?_⟩
  simp_rw [scaled_decay_truncation hk.ne']
  have ht : Tendsto (fun T : ℝ => k*T) atTop atTop := tendsto_id.const_mul_atTop hk
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have H := ((tendsto_const_nhds (x := (1:ℝ))).sub he).const_mul (P/k)
  simpa only [sub_zero, mul_one, Function.comp_apply, neg_mul] using H

theorem scaled_decay_error {k : ℝ} (hk : 0 < k) {P : ℝ} (hP : 0 ≤ P) (T : ℝ) :
    |P/k-(∫ t : ℝ in (0:ℝ)..T, P*Real.exp (-k*t))| =
      P/k*Real.exp (-k*T) := by
  rw [scaled_decay_truncation hk.ne']
  have he : P/k-P/k*(1-Real.exp (-k*T)) = P/k*Real.exp (-k*T) := by ring
  rw [he, abs_of_nonneg (by positivity)]

theorem normalized_exponential {k : ℝ} (hk : 0 < k) :
    ImproperRight (fun t : ℝ => k*Real.exp (-k*t)) 0 1 := by
  simpa only [div_self hk.ne'] using scaled_decay_improper hk k

theorem linear_density_centroid :
    mass (fun x : ℝ => 1+x) 0 1 = 3/2 ∧
    firstMoment (fun x : ℝ => 1+x) 0 1 = 5/6 ∧
    centroid (fun x : ℝ => 1+x) 0 1 = 5/9 := by
  have hm : mass (fun x : ℝ => 1+x) 0 1 = 3/2 := by
    rw [mass, intervalIntegral.integral_add (f := fun _ : ℝ => (1:ℝ)) (g := fun x : ℝ => x) intervalIntegrable_const
      (continuous_id.intervalIntegrable _ _), Ch09.integral_constant, Ch09.integral_linear]
    norm_num
  have hj : firstMoment (fun x : ℝ => 1+x) 0 1 = 5/6 := by
    have he : (fun x : ℝ => x*(1+x)) = fun x => x+x^2 := by funext x; ring
    rw [firstMoment, he, intervalIntegral.integral_add (f := fun x : ℝ => x) (g := fun x : ℝ => x^2)
      (continuous_id.intervalIntegrable _ _) ((continuous_id.pow 2).intervalIntegrable _ _),
      Ch09.integral_linear, Ch09.integral_square]
    norm_num
  exact ⟨hm,hj,by rw [centroid,hm,hj]; norm_num⟩

theorem parameter_energy {P α : ℝ} (hP : 0 < P) (hα : 0 < α) :
    ImproperRight (fun t : ℝ => P*Real.exp (-2*α*t)) 0 (P/(2*α)) ∧
    ∀ T, |P/(2*α)-(∫ t : ℝ in (0:ℝ)..T, P*Real.exp (-2*α*t))| =
      P/(2*α)*Real.exp (-2*α*T) := by
  have hk : 0 < 2*α := by positivity
  have he : (fun t : ℝ => P*Real.exp (-2*α*t)) = fun t => P*Real.exp (-(2*α)*t) := by
    funext t
    congr 1
    congr 1
    ring
  rw [he]
  refine ⟨scaled_decay_improper hk P, fun T => ?_⟩
  convert scaled_decay_error hk hP.le T using 1 <;> congr 2 <;> ring

theorem oscillating_truncation (T : ℝ) :
    (∫ x : ℝ in (0:ℝ)..T, 2*Real.pi*Real.cos (2*Real.pi*x)) = Real.sin (2*Real.pi*T) := by
  have hd (x : ℝ) : HasDerivAt (fun t => Real.sin (2*Real.pi*t))
      (2*Real.pi*Real.cos (2*Real.pi*x)) x := by
    convert (Real.hasDerivAt_sin (2*Real.pi*x)).comp x
      ((hasDerivAt_id x).const_mul (2*Real.pi)) using 1 <;> first | rfl | ring
  rw [Ch09.primitive_integral (fun x _ => hd x) (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp

theorem oscillating_cutoffs (n : ℕ) :
    Real.sin (2*Real.pi*(n:ℝ)) = 0 ∧
    Real.sin (2*Real.pi*((n:ℝ)+1/4)) = 1 := by
  constructor
  · rw [show 2*Real.pi*(n:ℝ) = ((2*n:ℕ):ℝ)*Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  · rw [show 2*Real.pi*((n:ℝ)+1/4) = ((2*n:ℕ):ℝ)*Real.pi+Real.pi/2 by push_cast; ring,
      Real.sin_add]
    simp only [Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two, mul_one, zero_add]
    convert Real.cos_nat_mul_two_pi n using 2 <;> push_cast <;> ring

def InteriorImproper (f : ℝ → ℝ) (a c b L : ℝ) : Prop :=
  ∃ I J, ImproperEndpointRight f a c I ∧ ImproperEndpointLeft f c b J ∧ L=I+J

theorem origin_power_converges {p : ℝ} (hp : p < 1) :
    ImproperEndpointLeft (fun x : ℝ => x^(-p)) 0 1 (1/(1-p)) := by
  refine ⟨?_, ?_⟩
  · intro c hc hc₁
    apply ContinuousOn.intervalIntegrable_of_Icc hc₁
    intro x hx
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (hc.trans_le hx.1)))).continuousWithinAt
  have hl : Tendsto (fun c : ℝ => c^(1-p)) (𝓝[>] 0) (𝓝 0) := by
    have H := (Real.continuousAt_rpow_const (0:ℝ) (1-p) (Or.inr (by linarith))).tendsto
    simpa [Real.zero_rpow (by linarith : 1-p ≠ 0)] using H.mono_left nhdsWithin_le_nhds
  have H := ((tendsto_const_nhds (x := (1:ℝ))).sub hl).div_const (1-p)
  apply (show Tendsto (fun c : ℝ => (1-c^(1-p))/(1-p)) (𝓝[>] 0) (𝓝 (1/(1-p))) from by simpa using H).congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (origin_power_truncation hp.ne hc).symm

theorem improper_cauchy {f : ℝ → ℝ} {a : ℝ}
    (hi : ∀ T, a ≤ T → IntervalIntegrable f volume a T) :
    (∃ L, ImproperRight f a L) ↔
      ∀ ε > 0, ∃ B ≥ a, ∀ T ≥ B, ∀ U ≥ B, |∫ x in T..U, f x| < ε := by
  let A := fun T : ℝ => ∫ x in a..T, f x
  have he (T U : ℝ) (ht : a ≤ T) (hu : a ≤ U) :
      (∫ x in T..U, f x) = A U - A T := by
    have htu := (hi T ht).symm.trans (hi U hu)
    have h := intervalIntegral.integral_add_adjacent_intervals (hi T ht) htu
    dsimp [A]
    linarith
  constructor
  · rintro ⟨L,hL⟩ ε hε
    obtain ⟨B,hB,h⟩ := ((improper_right_epsilon_iff _ _ _).1 hL).2 (ε/2) (half_pos hε)
    refine ⟨B,hB,fun T hT U hU => ?_⟩
    rw [he T U (hB.trans hT) (hB.trans hU)]
    have hb := abs_sub_le (A U) L (A T)
    rw [abs_sub_comm L] at hb
    exact hb.trans_lt (by linarith [h U hU, h T hT])
  · intro h
    have hc : Cauchy (Filter.map A atTop) := by
      apply Metric.cauchy_iff.mpr
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨B,hB,hδ⟩ := h ε hε
      refine ⟨A '' Ici B, ?_, ?_⟩
      · change A ⁻¹' (A '' Ici B) ∈ (atTop : Filter ℝ)
        filter_upwards [eventually_ge_atTop B] with T hT
        exact ⟨T,hT,rfl⟩
      · rintro _ ⟨T,hT,rfl⟩ _ ⟨U,hU,rfl⟩
        rw [Real.dist_eq, ← he U T (hB.trans hU) (hB.trans hT)]
        exact hδ U hU T hT
    obtain ⟨L,hL⟩ := cauchy_map_iff_exists_tendsto.mp hc
    exact ⟨L,hi,hL⟩

theorem exponential_cutoff {T ε : ℝ} (hε : 0 < ε)
    (hT : Real.log (1/ε) ≤ T) :
    |1-(∫ x : ℝ in (0:ℝ)..T, Real.exp (-x))| ≤ ε := by
  rw [decay_tail_error]
  have hlog : Real.log (1/ε) = -Real.log ε := by
    rw [one_div, Real.log_inv]
  rw [hlog] at hT
  exact (Real.exp_le_exp.mpr (by linarith : -T ≤ Real.log ε)).trans_eq (Real.exp_log hε)

theorem signed_exponential_tail (T : ℝ) :
    1-(∫ x : ℝ in (0:ℝ)..T, Real.exp (-x)) = Real.exp (-T) ∧
    0 < Real.exp (-T) := by
  rw [decay_truncation]
  exact ⟨by ring, Real.exp_pos _⟩

theorem spring_work_example (k L : ℝ) :
    work (fun x => k*x) 0 L = k/2*L^2 ∧
    work (fun x => -k*x) 0 L = -(k/2*L^2) := by
  rw [spring_work, spring_work]
  constructor <;> ring

theorem endpoint_right_epsilon {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b) :
    ImproperEndpointRight f a b L ↔
      (∀ c, a ≤ c → c < b → IntervalIntegrable f volume a c) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ c, b-δ < c → c < b → a ≤ c →
        |(∫ x in a..c, f x)-L| < ε := by
  rw [ImproperEndpointRight, Metric.tendsto_nhdsWithin_nhds]
  constructor
  · rintro ⟨hi,h⟩
    refine ⟨hi, fun ε hε => ?_⟩
    obtain ⟨δ,hδ,hb⟩ := h ε hε
    refine ⟨δ,hδ,fun c hcδ hc _ => ?_⟩
    have hd : dist c b < δ := by rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hc)]; linarith
    simpa [Real.dist_eq] using hb hc hd
  · rintro ⟨hi,h⟩
    refine ⟨hi,fun ε hε => ?_⟩
    obtain ⟨δ,hδ,hb⟩ := h ε hε
    refine ⟨min δ (b-a), lt_min hδ (sub_pos.mpr hab), ?_⟩
    intro c hc hd
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hc)] at hd
    have hd₁ := hd.trans_le (min_le_left _ _)
    have hd₂ := hd.trans_le (min_le_right _ _)
    simpa [Real.dist_eq] using hb c (by linarith) hc (by linarith)

end Ch10
