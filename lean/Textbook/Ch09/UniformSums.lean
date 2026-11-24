import Textbook.Ch09.Tagged

namespace Ch09

open Set MeasureTheory Filter Topology
open scoped Interval

private theorem sum_indices (n : ℕ) :
    (∑ k ∈ Finset.range n, (k:ℝ)) = (n:ℝ)*((n:ℝ)-1)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

private theorem sum_indices_sq (n : ℕ) :
    (∑ k ∈ Finset.range n, (k:ℝ)^2) = (n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

/-- Left, right and midpoint tags on the equal-width partition of the unit interval. -/
theorem uniform_linear_sums (n : ℕ) (hn : 0 < n) :
    ((∑ k ∈ Finset.range n, (k:ℝ)/n)/n = ((n:ℝ)-1)/(2*n)) ∧
    ((∑ k ∈ Finset.range n, ((k:ℝ)+1)/n)/n = ((n:ℝ)+1)/(2*n)) ∧
    ((∑ k ∈ Finset.range n, ((k:ℝ)+1/2)/n)/n = 1/2) := by
  have hn' : (n:ℝ) ≠ 0 := by positivity
  constructor
  · rw [← Finset.sum_div, sum_indices]
    field_simp
    <;> ring
  · constructor
    · rw [← Finset.sum_div, Finset.sum_add_distrib, sum_indices]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp
      <;> ring
    · rw [← Finset.sum_div, Finset.sum_add_distrib, sum_indices]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      <;> ring

theorem uniform_square_sum_formula (n : ℕ) (hn : 0 < n) :
    ((∑ k ∈ Finset.range n, ((k:ℝ)/n)^2)/n) =
      ((n:ℝ)-1)*(n:ℝ)*(2*(n:ℝ)-1)/(6*(n:ℝ)^3) := by
  have hn' : (n:ℝ) ≠ 0 := by positivity
  simp_rw [div_pow]
  rw [← Finset.sum_div,sum_indices_sq]
  field_simp
  <;> ring

private theorem fine_sums_tendsto {a b I : ℝ} {f : ℝ → ℝ} (h : HasTaggedIntegral f a b I)
    (P : ℕ → TaggedPartition a b)
    (hP : Tendsto (fun n => (P n).mesh) atTop (nhds 0)) :
    Tendsto (fun n => (P n).riemannSum f) atTop (nhds I) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := (tagged_integral_iff _ _ _ _).1 h ε hε
  filter_upwards [hP.eventually (Iio_mem_nhds hδ)] with n hn
  simpa only [Real.dist_eq] using hh (P n) hn

private theorem uniform_unit_mesh_tendsto :
    Tendsto (fun n => (uniformPartition (by norm_num : (0:ℝ) < 1) n).mesh) atTop (nhds 0) := by
  simpa only [uniform_mesh, sub_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem uniform_square_sum_limit :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n+1), ((k:ℝ)/((n:ℝ)+1))^2)/((n:ℝ)+1))
      atTop (nhds (1/3 : ℝ)) := by
  let P := uniformPartition (by norm_num : (0:ℝ) < 1)
  have h := fine_sums_tendsto tagged_integral_square P uniform_unit_mesh_tendsto
  convert h using 1
  funext n
  change (∑ k ∈ Finset.range (n+1), ((k:ℝ)/((n:ℝ)+1))^2)/((n:ℝ)+1) =
    ∑ i : Fin (n+1), (0+((i.val:ℝ)/((n:ℝ)+1))*(1-0))^2 * (P n).width i
  simp only [sub_zero,mul_one,zero_add,P,uniform_width]
  rw [Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun k : ℕ => ((k:ℝ)/((n:ℝ)+1))^2 * (1/((n:ℝ)+1)))]
  simp [div_eq_mul_inv]

theorem reciprocal_sum_log_limit :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n+1), 1/((n:ℝ)+1+((k:ℝ)+1)))
      atTop (nhds (Real.log 2)) := by
  let f (x : ℝ) := 1/(1+x)
  have hf : ContinuousOn f (Icc 0 1) := by
    apply continuousOn_const.div (by fun_prop)
    intro x hx
    linarith [hx.1]
  have he : (∫ x in (0:ℝ)..1, f x) = Real.log 2 := by
    have hd (x : ℝ) (hx : x ∈ uIcc (0:ℝ) 1) :
        HasDerivAt (fun t => Real.log (1+t)) (f x) x := by
      rw [uIcc_of_le zero_le_one] at hx
      have hn : 1+x ≠ 0 := by linarith [hx.1]
      convert (Real.hasDerivAt_log hn).comp x ((hasDerivAt_id' x).const_add 1) using 1 <;>
        first | rfl | simp [f,one_div]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hf.intervalIntegrable_of_Icc zero_le_one)]
    norm_num
  let P (n : ℕ) := uniformPartition (by norm_num : (0:ℝ) < 1) n
  let Q (n : ℕ) : TaggedPartition 0 1 :=
    { P n with
      tag := fun i => (P n).points i.succ
      tag_mem := fun i => right_mem_Icc.mpr ((P n).increasing (Fin.castSucc_lt_succ (i := i))).le }
  have htag := continuous_tagged_integral (by norm_num : (0:ℝ) < 1) hf
  rw [he] at htag
  have h := fine_sums_tendsto htag Q (show Tendsto (fun n => (P n).mesh) atTop (nhds 0)
    from uniform_unit_mesh_tendsto)
  convert h using 1
  funext n
  change (∑ k ∈ Finset.range (n+1), 1/((n:ℝ)+1+((k:ℝ)+1))) =
    ∑ i : Fin (n+1), f ((P n).points i.succ) * (P n).width i
  have hw (i : Fin (n+1)) : (P n).width i = 1/((n:ℝ)+1) := by
    simp [P, uniform_width]
  simp only [hw]
  simp only [P,uniformPartition,f,zero_add,sub_zero,mul_one,Fin.val_succ,Nat.cast_add,Nat.cast_one]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (1 / (1 + ((k:ℝ)+1)/((n:ℝ)+1))) * (1/((n:ℝ)+1)))]
  apply Finset.sum_congr rfl
  intro k _
  field_simp
  <;> ring

end Ch09
