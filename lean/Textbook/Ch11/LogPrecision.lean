import Textbook.Ch11.Audit

namespace Ch11

open Filter
open scoped Topology

noncomputable def fastLogTerm (n : ℕ) : ℝ := 2*(1/3:ℝ)^(2*n+1)/(2*n+1:ℝ)

theorem fast_log_two :
    SeriesHasSum fastLogTerm (Real.log 2) ∧
    (∀ N, 0 ≤ Real.log 2 - partialSum fastLogTerm N ∧
      Real.log 2 - partialSum fastLogTerm N ≤
        2*(1/3:ℝ)^(2*N+1)/((2*N+1:ℝ)*(1-(1/3:ℝ)^2))) ∧
    Real.log 2 - partialSum fastLogTerm 8 ≤ (9:ℝ)/(68*3^17) := by
  have heq : (fun k : ℕ => (2:ℝ)*(1/(2*k+1))*(1/(2*(1:ℝ)+1))^(2*k+1)) =
      fastLogTerm := by
    funext k
    unfold fastLogTerm
    norm_num
    ring
  have hs := Real.hasSum_log_one_add_inv (a := (1:ℝ)) one_pos
  rw [heq] at hs
  have hs' : HasSum fastLogTerm (Real.log 2) := by norm_num at hs ⊢; exact hs
  have ht (N : ℕ) :
      0 ≤ Real.log 2 - partialSum fastLogTerm N ∧
      Real.log 2 - partialSum fastLogTerm N ≤
        2*(1/3:ℝ)^(2*N+1)/((2*N+1:ℝ)*(1-(1/3:ℝ)^2)) := by
    let A : ℝ := 2*(1/3:ℝ)^(2*N+1)/(2*N+1:ℝ)
    let q : ℝ := (1/3:ℝ)^2
    have hg := hasSum_geometric_of_norm_lt_one (show ‖q‖ < 1 by norm_num [q])
    have hshift : Summable (fun j => fastLogTerm (j+N)) :=
      (summable_nat_add_iff N).2 hs'.summable
    have hrem : Real.log 2 - partialSum fastLogTerm N =
        ∑' j, fastLogTerm (j+N) := by
      have he := hs'.summable.sum_add_tsum_nat_add N
      rw [hs'.tsum_eq] at he
      unfold partialSum
      linarith
    have hb (j : ℕ) : fastLogTerm (j+N) ≤ A*q^j := by
      unfold fastLogTerm
      have hpow : 2*(j+N)+1 = (2*N+1)+2*j := by omega
      rw [hpow,pow_add,pow_mul]
      have hn : (2*N+1:ℝ) ≤ 2*((j:ℝ)+N)+1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
      have hp : 0 < (2*N+1:ℝ) := by positivity
      push_cast
      dsimp [A,q]
      rw [← mul_assoc]
      calc
        _ ≤ (2*(1/3:ℝ)^(2*N+1)*((1/3:ℝ)^2)^j)/(2*N+1:ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hp hn
        _ = _ := by ring
    have hle := hshift.tsum_le_tsum hb (hg.summable.mul_left A)
    rw [hg.summable.tsum_mul_left,hg.tsum_eq] at hle
    rw [hrem]
    refine ⟨tsum_nonneg (fun _ => by unfold fastLogTerm; positivity),?_⟩
    rw [← div_eq_mul_inv] at hle
    dsimp only [A,q] at hle
    rw [div_div] at hle
    exact hle
  refine ⟨hs'.tendsto_sum_nat,ht,(ht 8).2.trans ?_⟩
  norm_num

end Ch11
