import Textbook.Ch11.FourierExamples

namespace Ch11

open MeasureTheory Set
open scoped Interval

private theorem finite_bessel {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → ℝ → ℝ) (w : ι → ℝ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hf₂ : IntervalIntegrable (fun x => (f x)^2) volume (-Real.pi) Real.pi)
    (hg : ∀ i ∈ s, Continuous (g i)) (hw : ∀ i ∈ s, 0 < w i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, (∫ x in -Real.pi..Real.pi, g i x*g j x) =
      if i = j then w i else 0) :
    (∑ i ∈ s, ((∫ x in -Real.pi..Real.pi, f x*g i x)/w i)^2*w i) ≤
      ∫ x in -Real.pi..Real.pi, (f x)^2 := by
  let I := fun f : ℝ → ℝ => ∫ x in -Real.pi..Real.pi, f x
  let c := fun i => I (fun x => f x*g i x)/w i
  let G := fun x => ∑ i ∈ s, c i*g i x
  let E := ∑ i ∈ s, (c i)^2*w i
  have hGc : Continuous G :=
    continuous_finsetSum _ (fun i hi => (hg i hi).const_mul (c i))
  have hmul {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-Real.pi) Real.pi) :
      I (fun x => u x*G x) = ∑ i ∈ s, c i*I (fun x => u x*g i x) := by
    have he (x : ℝ) : u x*G x = ∑ i ∈ s, c i*(u x*g i x) := by
      unfold G
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    unfold I
    simp_rw [he]
    rw [intervalIntegral.integral_finsetSum (fun i hi =>
      (hu.mul_continuousOn (hg i hi).continuousOn).const_mul (c i))]
    simp_rw [intervalIntegral.integral_const_mul]
  have hproj (i : ι) (hi : i ∈ s) :
      I (fun x => G x*g i x) = c i*w i := by
    simp_rw [mul_comm (G _) (g i _)]
    rw [hmul ((hg i hi).intervalIntegrable _ _)]
    unfold I
    calc
      _ = ∑ j ∈ s, c j * (if i = j then w i else 0) :=
        Finset.sum_congr rfl (fun j hj => by rw [horth i hi j hj])
      _ = _ := by simp [mul_ite,Finset.sum_ite_eq,hi]
  have hfg : I (fun x => f x*G x) = E := by
    rw [hmul hf]
    apply Finset.sum_congr rfl
    intro i hi
    unfold c
    field_simp [(hw i hi).ne']
  have hgg : I (fun x => (G x)^2) = E := by
    simp_rw [pow_two]
    rw [hmul (hGc.intervalIntegrable _ _)]
    exact Finset.sum_congr rfl (fun i hi => by rw [hproj i hi]; ring)
  have hfgI : IntervalIntegrable (fun x => f x*G x) volume (-Real.pi) Real.pi :=
    hf.mul_continuousOn hGc.continuousOn
  have hggI : IntervalIntegrable (fun x => (G x)^2) volume (-Real.pi) Real.pi :=
    (hGc.pow 2).intervalIntegrable _ _
  have hnonneg : 0 ≤ I (fun x => (f x-G x)^2) :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun x _ => sq_nonneg _)
  have hexpand : I (fun x => (f x-G x)^2) =
      I (fun x => (f x)^2)-2*I (fun x => f x*G x)+I (fun x => (G x)^2) := by
    unfold I
    simp_rw [sub_sq]
    have he (x : ℝ) : 2*f x*G x = 2*(f x*G x) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_add (hf₂.sub (hfgI.const_mul 2)) hggI,
      intervalIntegral.integral_sub hf₂ (hfgI.const_mul 2), intervalIntegral.integral_const_mul]
  change E ≤ I (fun x => (f x)^2)
  rw [hexpand,hfg,hgg] at hnonneg
  linarith

private noncomputable def trigMode (i : Unit ⊕ (ℕ × Bool)) (x : ℝ) : ℝ :=
  match i with
  | .inl _ => 1
  | .inr (n,false) => Real.cos ((n:ℝ)*x)
  | .inr (n,true) => Real.sin ((n:ℝ)*x)

private noncomputable def trigWeight (i : Unit ⊕ (ℕ × Bool)) : ℝ :=
  match i with
  | .inl _ => 2*Real.pi
  | .inr _ => Real.pi

set_option autoImplicit false in
theorem fourier_bessel (f : ℝ → ℝ) (N : ℕ)
    (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hf₂ : IntervalIntegrable (fun x => (f x)^2) volume (-Real.pi) Real.pi) :
    (fourierCos f 0)^2/2 + (∑ n ∈ Finset.Icc 1 N, ((fourierCos f n)^2+(fourierSin f n)^2)) ≤
      (1/Real.pi)*(∫ x in -Real.pi..Real.pi, (f x)^2) := by
  classical
  let s : Finset (Unit ⊕ (ℕ × Bool)) := Finset.univ.disjSum ((Finset.Icc 1 N).product Finset.univ)
  have hmemb (n : ℕ) (b : Bool) (h : Sum.inr (n,b) ∈ s) : 0 < n := by
    have hn : 1 ≤ n ∧ n ≤ N := by simpa [s] using h
    omega
  have hcont (i : Unit ⊕ (ℕ × Bool)) : Continuous (trigMode i) := by
    rcases i with _ | ⟨n,b⟩
    · exact continuous_const
    · cases b <;> unfold trigMode <;> fun_prop
  have h := finite_bessel s trigMode trigWeight f hf hf₂
    (fun i _ => hcont i)
    (fun i _ => by rcases i with _ | _ <;> unfold trigWeight <;> positivity) ?_
  · rw [one_div,mul_comm Real.pi⁻¹,← div_eq_mul_inv]
    apply (le_div_iff₀ Real.pi_pos).2
    convert h using 1
    rw [Finset.sum_disjSum,Finset.product_eq_sprod,Finset.sum_product]
    simp only [Finset.univ_unique,Finset.sum_singleton,Fintype.univ_bool,
      Finset.sum_insert (by simp : true ∉ ({false}:Finset Bool)),trigMode,trigWeight,
      mul_one]
    rw [add_mul]
    congr 1
    · unfold fourierCos
      simp
      field_simp [Real.pi_ne_zero]
      <;> ring
    · erw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      unfold fourierCos fourierSin
      field_simp [Real.pi_ne_zero]
      <;> ring
  · intro i hi j hj
    rcases i with ⟨⟩ | ⟨m, bm⟩ <;> rcases j with ⟨⟩ | ⟨n,bn⟩
    · simp [trigMode,trigWeight,intervalIntegral.integral_const,two_mul]
    · have hn := hmemb n bn hj
      cases bn
      · have h := cosine_frequency_orthogonality 0 n
        simpa [trigMode,trigWeight,hn.ne',Ne.symm hn.ne'] using h
      · have h := sine_cosine_orthogonality n 0
        simpa [trigMode,trigWeight] using h
    · have hm := hmemb m bm hi
      cases bm
      · have h := cosine_frequency_orthogonality m 0
        simpa [trigMode,trigWeight,hm.ne'] using h
      · have h := sine_cosine_orthogonality m 0
        simpa [trigMode,trigWeight] using h
    · have hm := hmemb m bm hi
      have hn := hmemb n bn hj
      cases bm <;> cases bn
      · simpa [trigMode,trigWeight,hm.ne'] using cosine_frequency_orthogonality m n
      · simpa [trigMode,trigWeight,mul_comm] using sine_cosine_orthogonality n m
      · simpa [trigMode,trigWeight] using sine_cosine_orthogonality m n
      · simpa [trigMode,trigWeight] using sine_frequency_orthogonality hm hn

end Ch11
