import Textbook.Ch11.ApproximationExamples

namespace Ch11

open Filter
open scoped Topology

def twoPositiveOneNegative (n : ℕ) : ℕ :=
  if n%3 = 0 then 4*(n/3) else if n%3 = 1 then 4*(n/3)+2 else 2*(n/3)+1

theorem two_positive_one_negative_bijective : Function.Bijective twoPositiveOneNegative := by
  constructor
  · intro n m h
    unfold twoPositiveOneNegative at h
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> omega
  · intro k
    rcases (show k%4 = 0 ∨ k%4 = 1 ∨ k%4 = 2 ∨ k%4 = 3 by omega) with h|h|h|h
    · refine ⟨3*(k/4),?_⟩
      unfold twoPositiveOneNegative
      split <;> omega
    · refine ⟨3*(k/2)+2,?_⟩
      unfold twoPositiveOneNegative
      split <;> (try split) <;> omega
    · refine ⟨3*(k/4)+1,?_⟩
      unfold twoPositiveOneNegative
      split <;> (try split) <;> omega
    · refine ⟨3*(k/2)+2,?_⟩
      unfold twoPositiveOneNegative
      split <;> (try split) <;> omega

private noncomputable def hterm (n : ℕ) : ℝ := (-1:ℝ)^n/(n+1:ℝ)

private theorem hterm_even (m : ℕ) : hterm (2*m) = 1/(2*(m:ℝ)+1) := by
  simp [hterm,pow_mul,Nat.cast_mul]

private theorem hterm_odd (m : ℕ) : hterm (2*m+1) = -1/(2*(m:ℝ)+2) := by
  norm_num [hterm,pow_succ,pow_mul,Nat.cast_add,Nat.cast_mul,add_assoc]

private theorem block_sum (m : ℕ) :
    partialSum (hterm ∘ twoPositiveOneNegative) (3*m) =
      partialSum hterm (4*m) + (1/2:ℝ)*partialSum hterm (2*m) := by
  induction m with
  | zero => simp [partialSum]
  | succ m ih =>
    rw [show 3*(m+1) = 3*m+1+1+1 by omega,
      partialSum_succ,partialSum_succ,partialSum_succ,ih,
      show 4*(m+1) = 4*m+1+1+1+1 by omega,
      show 2*(m+1) = 2*m+1+1 by omega]
    repeat rw [partialSum_succ]
    have e0 : twoPositiveOneNegative (3*m) = 2*(2*m) := by
      unfold twoPositiveOneNegative; split <;> omega
    have e1 : twoPositiveOneNegative (3*m+1) = 2*(2*m+1) := by
      unfold twoPositiveOneNegative; split <;> (try split) <;> omega
    have e2 : twoPositiveOneNegative (3*m+1+1) = 2*m+1 := by
      unfold twoPositiveOneNegative; split <;> (try split) <;> omega
    simp only [Function.comp_apply,e0,e1,e2]
    rw [show 4*m = 2*(2*m) by omega,show 2*(2*m)+1+1 = 2*(2*m+1) by omega,
      show 2*(2*m)+3 = 2*(2*m+1)+1 by omega]
    simp only [hterm_even,hterm_odd]
    push_cast
    field_simp <;> ring

theorem alternating_harmonic_rearranged :
    SeriesHasSum (fun n => (-1:ℝ)^(twoPositiveOneNegative n)/(twoPositiveOneNegative n+1:ℝ))
      (3/2*Real.log 2) := by
  change SeriesHasSum (hterm ∘ twoPositiveOneNegative) (3/2*Real.log 2)
  have hd : SeriesHasSum hterm (Real.log 2) := alternating_harmonic.1
  have htop (k : ℕ) (hk : 0 < k) : Tendsto (fun n : ℕ => k*n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (by nlinarith)
  have hblocks : Tendsto (fun m : ℕ => partialSum (hterm ∘ twoPositiveOneNegative) (3*m))
      atTop (𝓝 (3/2*Real.log 2)) := by
    have h := (hd.comp (htop 4 (by decide))).add ((hd.comp (htop 2 (by decide))).const_mul (1/2:ℝ))
    rw [show Real.log 2 + 1/2*Real.log 2 = 3/2*Real.log 2 by ring] at h
    exact h.congr (fun m => (block_sum m).symm)
  have hm : Tendsto (fun n : ℕ => n/3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (3*b)] with n hn
    omega
  have hv (n : ℕ) :
      |partialSum (hterm ∘ twoPositiveOneNegative) n -
        partialSum (hterm ∘ twoPositiveOneNegative) (3*(n/3))| ≤ 2/((n/3:ℕ)+1:ℝ) := by
    let m := n/3
    have he0 : (hterm ∘ twoPositiveOneNegative) (3*m) = 1/(4*(m:ℝ)+1) := by
      have h : twoPositiveOneNegative (3*m) = 2*(2*m) := by
        unfold twoPositiveOneNegative; split <;> omega
      rw [Function.comp_apply,h,hterm_even]
      push_cast
      ring
    have he1 : (hterm ∘ twoPositiveOneNegative) (3*m+1) = 1/(4*(m:ℝ)+3) := by
      have h : twoPositiveOneNegative (3*m+1) = 2*(2*m+1) := by
        unfold twoPositiveOneNegative; split <;> (try split) <;> omega
      rw [Function.comp_apply,h,hterm_even]
      push_cast
      ring
    have hb0 : 1/(4*(m:ℝ)+1) ≤ 1/((m:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hb1 : 1/(4*(m:ℝ)+3) ≤ 1/((m:ℝ)+1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m])
    change |partialSum (hterm ∘ twoPositiveOneNegative) n -
      partialSum (hterm ∘ twoPositiveOneNegative) (3*m)| ≤ 2/((m:ℝ)+1)
    rw [show 2/((m:ℝ)+1) = 2*(1/((m:ℝ)+1)) by ring]
    rcases (show n = 3*m ∨ n = 3*m+1 ∨ n = 3*m+1+1 by dsimp [m]; omega) with h|h|h
    · simp [h]; positivity
    · rw [h,partialSum_succ,he0,add_sub_cancel_left,abs_of_nonneg (by positivity)]
      linarith [show 0 ≤ 1/((m:ℝ)+1) by positivity]
    · rw [h,partialSum_succ,partialSum_succ,he0,he1,add_assoc,add_sub_cancel_left,
        abs_of_nonneg (by positivity)]
      linarith
  have hsmall : Tendsto (fun n : ℕ => partialSum (hterm ∘ twoPositiveOneNegative) n -
        partialSum (hterm ∘ twoPositiveOneNegative) (3*(n/3))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero (fun _ => abs_nonneg _) hv
    have hi : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,← div_eq_mul_inv,mul_zero] using
      (hi.comp hm).const_mul (2:ℝ)
  have h := hsmall.add (hblocks.comp hm)
  simpa [SeriesHasSum,Function.comp_def] using h

end Ch11
