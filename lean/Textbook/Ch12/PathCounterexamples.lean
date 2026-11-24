import Textbook.Ch12.Audit

namespace Ch12

open Filter Set
open scoped Topology

noncomputable def axisCounter (z : ℝ × ℝ) : ℝ := z.1*z.2/(z.1^2+z.2^2)
noncomputable def lineCounter (z : ℝ × ℝ) : ℝ := z.1^2*z.2/(z.1^4+z.2^2)

private theorem tendsto_path_zero {γ : ℝ → ℝ × ℝ} (h : ContinuousAt γ 0) (hzero : γ 0 = 0) :
    Tendsto γ (𝓝[≠] (0:ℝ)) (𝓝 0) := by
  rw [← hzero]
  exact h.tendsto.mono_left nhdsWithin_le_nhds

private theorem path_nonzero {γ : ℝ → ℝ × ℝ} (h : ∀ t, (γ t).1 = t) :
    ∀ᶠ t in 𝓝[≠] (0:ℝ), γ t ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with t ht he
  exact ht ((h t).symm.trans (congrArg Prod.fst he))

theorem axes_and_diagonal :
    (∀ t : ℝ, axisCounter (t,0) = 0 ∧ axisCounter (0,t) = 0) ∧
    (∀ t : ℝ, t ≠ 0 → axisCounter (t,t) = 1/2) ∧
    ¬ ∃ L, HasMultivariableLimit axisCounter 0 L := by
  have ha (t : ℝ) : axisCounter (t,0) = 0 ∧ axisCounter (0,t) = 0 := by
    simp [axisCounter]
  have hd (t : ℝ) (ht : t ≠ 0) : axisCounter (t,t) = 1/2 := by
    unfold axisCounter
    have hpos : 0 < t^2+t^2 := by positivity
    field_simp
    ring
  refine ⟨ha,hd,?_⟩
  rintro ⟨L,hL⟩
  have h0 := path_necessary (γ := fun t : ℝ => (t,0))
    (tendsto_path_zero (by fun_prop) rfl) (path_nonzero (fun _ => rfl)) hL
  have h1 := path_necessary (γ := fun t : ℝ => (t,t))
    (tendsto_path_zero (by fun_prop) rfl) (path_nonzero (fun _ => rfl)) hL
  have hz : Tendsto (fun _ : ℝ => 0) (𝓝[≠] (0:ℝ)) (𝓝 L) :=
    h0.congr (fun t => (ha t).1)
  have hh : Tendsto (fun _ : ℝ => 1/2) (𝓝[≠] (0:ℝ)) (𝓝 L) := by
    apply h1.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hd t ht
  have e0 := tendsto_nhds_unique hz tendsto_const_nhds
  have e1 := tendsto_nhds_unique hh tendsto_const_nhds
  linarith

theorem line_counter_all_lines :
    (∀ k : ℝ, Tendsto (fun t : ℝ => lineCounter (t,k*t)) (𝓝[≠] (0:ℝ)) (𝓝 0)) ∧
    (∀ t : ℝ, lineCounter (0,t) = 0) ∧
    (∀ t : ℝ, t ≠ 0 → lineCounter (t,t^2) = 1/2) ∧
    ¬ ∃ L, HasMultivariableLimit lineCounter 0 L := by
  have hv (t : ℝ) : lineCounter (0,t) = 0 := by simp [lineCounter]
  have hs (t : ℝ) (ht : t ≠ 0) : lineCounter (t,t^2) = 1/2 := by
    unfold lineCounter
    have hpos : 0 < t^4+(t^2)^2 := by positivity
    field_simp
    ring
  have hl (k : ℝ) : Tendsto (fun t : ℝ => lineCounter (t,k*t)) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    by_cases hk : k = 0
    · subst k
      simpa [lineCounter] using (tendsto_const_nhds (x := (0:ℝ)) (f := 𝓝[≠] (0:ℝ)))
    have hc : ContinuousAt (fun t : ℝ => k*t/(t^2+k^2)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num; positivity)
    have ht : Tendsto (fun t : ℝ => k*t/(t^2+k^2)) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
      change Tendsto _ _ (𝓝 (k*0/((0:ℝ)^2+k^2))) at h
      simpa only [mul_zero,zero_div] using h
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht'
    have ht₀ : t ≠ 0 := ht'
    have hpos : 0 < t^4+(k*t)^2 := by positivity
    have hpos' : 0 < t^2+k^2 := by positivity
    unfold lineCounter
    field_simp
  refine ⟨hl,hv,hs,?_⟩
  rintro ⟨L,hL⟩
  have h0 := path_necessary (γ := fun t : ℝ => (t,(0:ℝ)*t))
    (tendsto_path_zero (by fun_prop) (by simp)) (path_nonzero (fun _ => rfl)) hL
  have h1 := path_necessary (γ := fun t : ℝ => (t,t^2))
    (tendsto_path_zero (by fun_prop) (by simp)) (path_nonzero (fun _ => rfl)) hL
  have hh : Tendsto (fun _ : ℝ => 1/2) (𝓝[≠] (0:ℝ)) (𝓝 L) := by
    apply h1.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hs t ht
  have e0 := tendsto_nhds_unique h0 (hl 0)
  have e1 := tendsto_nhds_unique hh tendsto_const_nhds
  linarith

theorem separately_not_jointly_continuous :
    (∀ y : ℝ, Continuous (fun x => axisCounter (x,y))) ∧
    (∀ x : ℝ, Continuous (fun y => axisCounter (x,y))) ∧
    ¬ ContinuousAt axisCounter 0 := by
  refine ⟨fun y => ?_, fun x => ?_,?_⟩
  · by_cases hy : y = 0
    · subst y; simpa [axisCounter] using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
    unfold axisCounter
    exact Continuous.div (by fun_prop) (by fun_prop) (fun _ => by positivity)
  · by_cases hx : x = 0
    · subst x; simpa [axisCounter] using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
    unfold axisCounter
    exact Continuous.div (by fun_prop) (by fun_prop) (fun _ => by positivity)
  · intro h
    exact axes_and_diagonal.2.2 ⟨_,h.tendsto.mono_left nhdsWithin_le_nhds⟩

end Ch12
