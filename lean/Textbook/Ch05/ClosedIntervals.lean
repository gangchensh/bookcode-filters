import Textbook.Ch05.Sequences

namespace Ch05ClosedIntervals

-- BEGIN ivt
theorem zero_on_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ c ∈ Set.Icc a b, f c = 0 := by
  exact intermediate_value_Icc hab hf ⟨ha, hb⟩
-- END ivt

theorem intermediate_on_interval {f : ℝ → ℝ} {a b y : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hy : y ∈ Set.Icc (min (f a) (f b)) (max (f a) (f b))) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  rcases le_total (f a) (f b) with h | h
  · exact intermediate_value_Icc hab hf (by simpa [min_eq_left h, max_eq_right h] using hy)
  · exact intermediate_value_Icc' hab hf (by simpa [min_eq_right h, max_eq_left h] using hy)

theorem maximum_on_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f c :=
  isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab⟩ hf

theorem minimum_on_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x :=
  isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hf

theorem bounded_on_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ M ≥ 0, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
  obtain ⟨c,hc,hmax⟩ := maximum_on_interval hab hf.abs
  exact ⟨|f c|, abs_nonneg _, hmax⟩

def UniformlyContinuous (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, |x-y| < δ → |f x-f y| < ε

theorem uniform_continuity_iff (f : ℝ → ℝ) (S : Set ℝ) :
    UniformlyContinuous f S ↔ UniformContinuousOn f S := by
  rw [Metric.uniformContinuousOn_iff]
  simp only [UniformlyContinuous, Real.dist_eq]

theorem heine_cantor {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) : UniformlyContinuous f (Set.Icc a b) :=
  (uniform_continuity_iff _ _).2 (isCompact_Icc.uniformContinuousOn_of_continuous hf)

theorem stable_root {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) (ha : f a < 0) (hb : 0 < f b)
    (hga : |g a-f a| < min (-f a) (f b)/2)
    (hgb : |g b-f b| < min (-f a) (f b)/2) : ∃ c ∈ Set.Icc a b, g c = 0 := by
  apply zero_on_interval hab hg
  · linarith [(abs_lt.mp hga).2, min_le_left (-f a) (f b)]
  · linarith [(abs_lt.mp hgb).1, min_le_right (-f a) (f b)]

def rootPolynomial (x : ℝ) : ℝ := x^3+x-1

theorem rootPolynomial_strictMono : StrictMono rootPolynomial := by
  intro x y hxy
  have hp : 0 < y^2+y*x+x^2+1 := by nlinarith [sq_nonneg (y+x/2), sq_nonneg x]
  have hprod := mul_pos (sub_pos.mpr hxy) hp
  unfold rootPolynomial
  nlinarith

theorem polynomial_unique_root : ∃! c, c ∈ Set.Ioo (0 : ℝ) 1 ∧ rootPolynomial c = 0 := by
  have hcont : Continuous rootPolynomial := by unfold rootPolynomial; fun_prop
  obtain ⟨c,hc,hzero⟩ := zero_on_interval (show (0:ℝ) ≤ 1 by norm_num)
    hcont.continuousOn (by norm_num [rootPolynomial]) (by norm_num [rootPolynomial])
  refine ⟨c, ⟨⟨lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩,hzero⟩, ?_⟩
  · intro h
    norm_num [← h, rootPolynomial] at hzero
  · intro h
    norm_num [h, rootPolynomial] at hzero
  · intro d hd
    exact rootPolynomial_strictMono.injective (hd.2.trans hzero.symm)

theorem polynomial_root_bracket {c : ℝ} (hc : rootPolynomial c = 0) :
    (68/100 : ℝ) < c ∧ c < 69/100 ∧ |c-685/1000| < 5/1000 := by
  have ha : rootPolynomial (68/100) < rootPolynomial c := by rw [hc]; norm_num [rootPolynomial]
  have hb : rootPolynomial c < rootPolynomial (69/100) := by rw [hc]; norm_num [rootPolynomial]
  have hl := rootPolynomial_strictMono.lt_iff_lt.mp ha
  have hu := rootPolynomial_strictMono.lt_iff_lt.mp hb
  exact ⟨hl,hu,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

theorem root_perturbation (f g : ℝ → ℝ) (I : Set ℝ) (c d m η : ℝ)
    (hc : c ∈ I) (hd : d ∈ I) (hf : f c = 0) (hg : g d = 0) (hm : 0 < m)
    (hlower : ∀ x ∈ I, ∀ y ∈ I, m*|x-y| ≤ |f x-f y|)
    (hpert : ∀ x ∈ I, |f x-g x| ≤ η) : |c-d| ≤ η/m := by
  apply (le_div_iff₀ hm).2
  calc
    |c-d| * m = m * |c-d| := mul_comm _ _
    _ ≤ |f c-f d| := hlower c hc d hd
    _ = |f d-g d| := by simp [hf,hg]
    _ ≤ η := hpert d hd

end Ch05ClosedIntervals
