import Textbook.Ch11.Audit

namespace Ch11

open MeasureTheory Set
open scoped Interval

private theorem integral_cos_frequency {k : ℝ} (hk : k ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Real.cos (k*x)) = Real.sin (k*b)/k-Real.sin (k*a)/k := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => Real.sin (k*x)/k) ?_
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos (k*x))).intervalIntegrable a b)
  intro x _
  simpa [id_eq,mul_div_cancel_right₀ _ hk] using
    ((((hasDerivAt_id x).const_mul k).sin).div_const k)

private theorem integral_sin_frequency {k : ℝ} (hk : k ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Real.sin (k*x)) = -Real.cos (k*b)/k-(-Real.cos (k*a)/k) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => -Real.cos (k*x)/k) ?_
    ((by fun_prop : Continuous (fun x : ℝ => Real.sin (k*x))).intervalIntegrable a b)
  intro x _
  simpa [id_eq,mul_div_cancel_right₀ _ hk] using
    ((((hasDerivAt_id x).const_mul k).cos).fun_neg.div_const k)

noncomputable def squareWaveOnPeriod (x : ℝ) : ℝ := if x ≤ 0 then -1 else 1

private theorem square_wave_integral {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in -Real.pi..Real.pi, squareWaveOnPeriod x*f x) =
      -(∫ x in -Real.pi..(0:ℝ), f x) + ∫ x in (0:ℝ)..Real.pi, f x := by
  have h₁ : EqOn (fun x => -f x) (fun x => squareWaveOnPeriod x*f x) (uIoc (-Real.pi) 0) := by
    rw [uIoc_of_le (by linarith [Real.pi_pos])]
    intro x hx
    simp [squareWaveOnPeriod,hx.2]
  have h₂ : EqOn f (fun x => squareWaveOnPeriod x*f x) (uIoc 0 Real.pi) := by
    rw [uIoc_of_le Real.pi_pos.le]
    intro x hx
    simp [squareWaveOnPeriod,not_le_of_gt hx.1]
  have hi₁ : IntervalIntegrable (fun x => squareWaveOnPeriod x*f x) volume (-Real.pi) 0 :=
    (hf.neg.intervalIntegrable (-Real.pi) 0).congr h₁
  have hi₂ : IntervalIntegrable (fun x => squareWaveOnPeriod x*f x) volume 0 Real.pi :=
    (hf.intervalIntegrable 0 Real.pi).congr h₂
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,
    ← intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall h₁),
    ← intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall h₂),
    intervalIntegral.integral_neg]

theorem square_wave_coefficients :
    (∀ n, fourierCos squareWaveOnPeriod n = 0) ∧
    (∀ n : ℕ, 0 < n → fourierSin squareWaveOnPeriod n = 2*(1-(-1:ℝ)^n)/(Real.pi*n)) := by
  constructor
  · intro n
    unfold fourierCos
    rw [square_wave_integral (by fun_prop)]
    by_cases hn : n = 0
    · subst n
      simp [intervalIntegral.integral_const]
    · have h : (n:ℝ) ≠ 0 := by exact_mod_cast hn
      rw [integral_cos_frequency h,integral_cos_frequency h]
      simp [mul_neg,Real.sin_nat_mul_pi]
  · intro n hn
    unfold fourierSin
    have h : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [square_wave_integral (by fun_prop),integral_sin_frequency h,integral_sin_frequency h]
    simp only [mul_neg,Real.cos_neg,Real.cos_nat_mul_pi,mul_zero,Real.cos_zero]
    field_simp [Real.pi_ne_zero]
    <;> ring

theorem integral_cos_integer (k : ℤ) :
    (∫ x in -Real.pi..Real.pi, Real.cos ((k:ℝ)*x)) =
      if k = 0 then 2*Real.pi else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [intervalIntegral.integral_const,two_mul]
  · have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    rw [integral_cos_frequency hk']
    simp [hk,mul_neg,Real.sin_int_mul_pi]

theorem sine_frequency_orthogonality {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∫ x in -Real.pi..Real.pi, Real.sin ((m:ℝ)*x)*Real.sin ((n:ℝ)*x)) =
      if m = n then Real.pi else 0 := by
  let d : ℤ := (m:ℤ)-n
  let s : ℤ := (m:ℤ)+n
  have h (x : ℝ) : Real.sin ((m:ℝ)*x)*Real.sin ((n:ℝ)*x) =
      (1/2:ℝ)*(Real.cos ((d:ℝ)*x)-Real.cos ((s:ℝ)*x)) := by
    simp only [d,s,Int.cast_sub,Int.cast_add,Int.cast_natCast,sub_mul,add_mul,
      Real.cos_sub,Real.cos_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos ((d:ℝ)*x))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos ((s:ℝ)*x))).intervalIntegrable _ _),
    integral_cos_integer,integral_cos_integer]
  have hs : s ≠ 0 := by dsimp [s]; omega
  by_cases he : m = n
  · simp [d,hs,he]
  · have hd : d ≠ 0 := by dsimp [d]; omega
    simp [hd,hs,he]

theorem sine_cosine_orthogonality (m n : ℕ) :
    (∫ x in -Real.pi..Real.pi, Real.sin ((m:ℝ)*x)*Real.cos ((n:ℝ)*x)) = 0 := by
  let f := fun x : ℝ => Real.sin ((m:ℝ)*x)*Real.cos ((n:ℝ)*x)
  have hf (x : ℝ) : f (-x) = -f x := by simp [f,mul_neg,Real.sin_neg,Real.cos_neg,neg_mul]
  have h := intervalIntegral.integral_comp_neg f (a := -Real.pi) (b := Real.pi)
  simp_rw [hf, neg_neg,intervalIntegral.integral_neg] at h
  change (∫ x in -Real.pi..Real.pi, f x) = 0
  linarith

theorem cosine_frequency_orthogonality (m n : ℕ) :
    (∫ x in -Real.pi..Real.pi, Real.cos ((m:ℝ)*x)*Real.cos ((n:ℝ)*x)) =
      if m = n then (if m = 0 then 2*Real.pi else Real.pi) else 0 := by
  let d : ℤ := (m:ℤ)-n
  let s : ℤ := (m:ℤ)+n
  have h (x : ℝ) : Real.cos ((m:ℝ)*x)*Real.cos ((n:ℝ)*x) =
      (1/2:ℝ)*(Real.cos ((d:ℝ)*x)+Real.cos ((s:ℝ)*x)) := by
    simp only [d,s,Int.cast_sub,Int.cast_add,Int.cast_natCast,sub_mul,add_mul,
      Real.cos_sub,Real.cos_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos ((d:ℝ)*x))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos ((s:ℝ)*x))).intervalIntegrable _ _),
    integral_cos_integer,integral_cos_integer]
  by_cases he : m = n
  · subst n
    by_cases hm : m = 0
    · simp [hm,d,s]
      <;> ring
    · have hs : s ≠ 0 := by dsimp [s]; omega
      simp [hm,d,hs]
  · have hd : d ≠ 0 := by dsimp [d]; omega
    have hs : s ≠ 0 := by dsimp [s]; omega
    simp [hd,hs,he]

noncomputable def finiteHarmonicSignal (x : ℝ) : ℝ := Real.sin x+(1/2:ℝ)*Real.sin (3*x)

private theorem signal_split (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ x in -Real.pi..Real.pi, finiteHarmonicSignal x*φ x) =
      (∫ x in -Real.pi..Real.pi, Real.sin ((1:ℝ)*x)*φ x) +
        (1/2:ℝ)*∫ x in -Real.pi..Real.pi, Real.sin ((3:ℝ)*x)*φ x := by
  simp_rw [finiteHarmonicSignal,add_mul,mul_assoc,one_mul]
  have h1 : IntervalIntegrable (fun x => Real.sin x*φ x) volume (-Real.pi) Real.pi :=
    (Real.continuous_sin.mul hφ).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x => (1/2:ℝ)*(Real.sin (3*x)*φ x)) volume (-Real.pi) Real.pi :=
    ((by fun_prop : Continuous (fun x : ℝ => Real.sin (3*x)*φ x)).const_mul (1/2:ℝ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h3,intervalIntegral.integral_const_mul]


theorem finite_harmonic_coefficients :
    (∀ n, fourierCos finiteHarmonicSignal n = 0) ∧
    (∀ n, fourierSin finiteHarmonicSignal n =
      (if n = 1 then 1 else 0)+(if n = 3 then (1/2:ℝ) else 0)) := by
  constructor
  · intro n
    unfold fourierCos
    rw [signal_split _ (by fun_prop)]
    have h1 := sine_cosine_orthogonality 1 n
    have h3 := sine_cosine_orthogonality 3 n
    norm_num at h1 h3 ⊢
    rw [h1,h3]
    ring
  · intro n
    unfold fourierSin
    rw [signal_split _ (by fun_prop)]
    by_cases hn : n = 0
    · subst n
      simp
    have h1' := sine_frequency_orthogonality (m := 1) (by decide) (Nat.pos_of_ne_zero hn)
    have h3' := sine_frequency_orthogonality (m := 3) (by decide) (Nat.pos_of_ne_zero hn)
    norm_num at h1' h3' ⊢
    rw [h1',h3']
    by_cases h1 : n = 1
    · subst n; simp [Real.pi_ne_zero]
    · by_cases h3 : n = 3
      · subst n; simp; field_simp [Real.pi_ne_zero]
      · simp [h1,h3,Ne.symm h1,Ne.symm h3]

theorem finite_harmonic_reconstruction (N : ℕ) (x : ℝ) :
    fourierPartialSum finiteHarmonicSignal N x =
      (if 1 ≤ N then Real.sin x else 0) + (if 3 ≤ N then (1/2:ℝ)*Real.sin (3*x) else 0) := by
  unfold fourierPartialSum
  simp only [finite_harmonic_coefficients.1,finite_harmonic_coefficients.2,
    zero_div,zero_mul,zero_add,add_mul,Finset.sum_add_distrib,ite_mul,one_mul]
  classical
  simp [Finset.sum_ite_eq',Finset.mem_Icc]

theorem finite_harmonic_first_mode_error :
    (∀ x, |finiteHarmonicSignal x-fourierPartialSum finiteHarmonicSignal 1 x| ≤ 1/2) ∧
    (∫ x in -Real.pi..Real.pi, (finiteHarmonicSignal x-fourierPartialSum finiteHarmonicSignal 1 x)^2) =
      Real.pi/4 := by
  have he (x : ℝ) :
      finiteHarmonicSignal x-fourierPartialSum finiteHarmonicSignal 1 x =
        (1/2:ℝ)*Real.sin (3*x) := by
    rw [finite_harmonic_reconstruction,finiteHarmonicSignal]
    norm_num
  constructor
  · intro x
    rw [he,abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ))]
    exact mul_le_of_le_one_right (by norm_num) (Real.abs_sin_le_one _)
  · simp_rw [he,mul_pow,pow_two (Real.sin _)]
    rw [intervalIntegral.integral_const_mul]
    have h := sine_frequency_orthogonality (m := 3) (n := 3) (by decide) (by decide)
    simp only [ite_true] at h
    norm_num at h ⊢
    rw [h]
    ring

end Ch11
