import Textbook.Ch02.Logic

/- Concrete epsilon proofs using Chapter 2's eventual rules only.
   Chapter 3 identifies these statements with filter convergence. -/
namespace Ch02Applications
open Ch02

noncomputable def reciprocal (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
noncomputable def shifted (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
noncomputable def changed (n : ℕ) : ℝ := if n = 0 then 100 else reciprocal n

theorem reciprocal_small (ε : ℝ) (hε : 0 < ε) :
    Eventually tailFilter (fun n => |reciprocal n| < ε) := by
  apply eventually_mono (F := tailFilter)
    (Ch02Eventually.eventually_reciprocal ε hε)
  intro n hn
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  change |1 / ((n : ℝ) + 1)| < ε
  rw [abs_of_pos hpos]
  exact hn

theorem shifted_small (ε : ℝ) (hε : 0 < ε) :
    Eventually tailFilter (fun n => |shifted n| < ε) := by
  apply eventually_mono (reciprocal_small ε hε) -- 将倒数估计传给较小的项
  intro n hn
  have hle : |shifted n| ≤ |reciprocal n| := by
    have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [shifted, reciprocal, abs_of_pos h1, abs_of_pos h2]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  exact lt_of_le_of_lt hle hn

theorem sum_small (ε : ℝ) (hε : 0 < ε) :
    Eventually tailFilter
      (fun n => |reciprocal n + shifted n| < ε) := by
  have hu := reciprocal_small (ε / 2) (half_pos hε)
  have hv := shifted_small (ε / 2) (half_pos hε)
  apply eventually_mono (eventually_and hu hv) -- 合并两个ε/2要求
  intro n hn
  calc
    |reciprocal n + shifted n|
        ≤ |reciprocal n| + |shifted n| := abs_add_le _ _
    _ < ε := by linarith [hn.1, hn.2]          -- 两个距离界相加

theorem square_small (ε : ℝ) (hε : 0 < ε) :
    Eventually tailFilter (fun n => |reciprocal n ^ 2| < ε) := by
  have hImp : Eventually tailFilter
      (fun n => |reciprocal n| < ε → |reciprocal n ^ 2| < ε) := by
    apply eventually_mono (reciprocal_small 1 zero_lt_one)
    intro n hn hεn
    have hnonneg : 0 ≤ reciprocal n := by unfold reciprocal; positivity
    rw [abs_of_nonneg hnonneg] at hn hεn
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith                                -- 0≤u<1时，u²≤u<ε
  exact eventually_mp hImp (reciprocal_small ε hε)

theorem reciprocal_changed_eq :
    EventuallyEq tailFilter reciprocal changed := by
  refine ⟨1, ?_⟩                             -- 从第1项起两数列相等
  intro n hn
  have hne : n ≠ 0 := by omega
  simp [changed, hne]

theorem changed_small (ε : ℝ) (hε : 0 < ε) :
    Eventually tailFilter (fun n => |changed n| < ε) := by
  exact eventually_subst (P := fun t : ℝ => |t| < ε)
    reciprocal_changed_eq (reciprocal_small ε hε)

end Ch02Applications
