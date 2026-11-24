import Textbook.Ch09.Tagged

namespace Ch09

open Set

/-- A point can serve as a tag in at most two cells, one on each side of it. -/
theorem TaggedPartition.tag_fiber_card {a b : ℝ} (P : TaggedPartition a b) (x : ℝ) :
    (Finset.univ.filter fun i => P.tag i = x).card ≤ 2 := by
  classical
  let side (i : Fin (P.n+1)) : Bool := decide (P.points i.castSucc = x)
  have h : Set.InjOn side ↑(Finset.univ.filter fun i => P.tag i = x) := by
    intro i hi j hj hij
    have hi' : P.tag i = x := (Finset.mem_filter.mp hi).2
    have hj' : P.tag j = x := (Finset.mem_filter.mp hj).2
    have hi := P.tag_mem i
    have hj := P.tag_mem j
    rw [hi'] at hi
    rw [hj'] at hj
    have different (p q : Fin (P.n+1)) (hpq : p < q)
        (hp : x ∈ Icc (P.points p.castSucc) (P.points p.succ))
        (hq : x ∈ Icc (P.points q.castSucc) (P.points q.succ)) : side p ≠ side q := by
      have hle : p.succ ≤ q.castSucc := by
        change p.val + 1 ≤ q.val
        omega
      have he : P.points q.castSucc = x :=
        le_antisymm hq.1 (hp.2.trans (P.increasing.monotone hle))
      have hne : P.points p.castSucc ≠ x :=
        ne_of_lt ((P.increasing (Fin.castSucc_lt_succ (i := p))).trans_le
          ((P.increasing.monotone hle).trans he.le))
      simp [side, he, hne]
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact False.elim (different i j hlt hi hj hij)
    · exact he
    · exact False.elim (different j i hgt hj hi hij.symm)
  simpa using Finset.card_le_card_of_injOn side (fun _ _ => Finset.mem_univ _) h

theorem tagged_integral_update {a b I : ℝ} {f : ℝ → ℝ}
    (h : HasTaggedIntegral f a b I) (x v : ℝ) :
    HasTaggedIntegral (Function.update f x v) a b I := by
  classical
  rw [tagged_integral_iff] at h ⊢
  intro ε hε
  obtain ⟨δ,hδ,hfine⟩ := h (ε/2) (by positivity)
  let C := |v - f x|
  let d := ε / (4*(C+1))
  have hC : 0 ≤ C := abs_nonneg _
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨min δ d, lt_min hδ hd, ?_⟩
  intro P hP
  let S := Finset.univ.filter fun i => P.tag i = x
  have hmesh : P.mesh < d := hP.trans_le (min_le_right _ _)
  have hw (i) : 0 ≤ P.width i :=
    sub_nonneg.mpr (P.increasing (Fin.castSucc_lt_succ (i := i))).le
  have hsum : P.riemannSum (Function.update f x v) - P.riemannSum f =
      ∑ i ∈ S, (v - f x)*P.width i := by
    unfold TaggedPartition.riemannSum
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : P.tag i = x <;> simp [hi, Function.update, sub_mul]
  have hb : |P.riemannSum (Function.update f x v) - P.riemannSum f| ≤ 2*(C*d) := by
    rw [hsum]
    calc
      _ ≤ ∑ i ∈ S, |(v - f x)*P.width i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ S, C*d := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left
          ((Finset.le_sup' P.width (Finset.mem_univ i)).trans hmesh.le) hC
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hd.le)
        exact_mod_cast P.tag_fiber_card x
  have he : 2*(C*d) < ε/2 := by
    dsimp [d]
    have hp : 0 < 4*(C+1) := by positivity
    rw [← mul_assoc, ← mul_div_assoc, div_lt_iff₀ hp]
    nlinarith
  have hε' := (abs_sub_le _ (P.riemannSum f) _).trans_lt
    (add_lt_add (hb.trans_lt he) (hfine P (hP.trans_le (min_le_left _ _))))
  linarith

theorem tagged_integral_finite_change {a b I : ℝ} {f g : ℝ → ℝ}
    (h : HasTaggedIntegral f a b I) (S : Finset ℝ) (he : ∀ x ∉ S, g x = f x) :
    HasTaggedIntegral g a b I := by
  classical
  induction S using Finset.induction_on generalizing g with
  | empty =>
      have hgf : g = f := funext fun x => he x (Finset.notMem_empty x)
      simpa [hgf] using h
  | @insert x S hx ih =>
      let g₀ := Function.update g x (f x)
      have hg₀ : HasTaggedIntegral g₀ a b I := ih fun y hy => by
        by_cases hyx : y = x
        · simp [g₀, hyx]
        · simpa [g₀, Function.update_of_ne hyx] using he y (by simp [hyx,hy])
      have heq : Function.update g₀ x (g x) = g := by
        funext y
        by_cases hy : y = x <;> simp [g₀, hy]
      rw [← heq]
      exact tagged_integral_update hg₀ x (g x)

theorem tagged_single_spike (a b c : ℝ) :
    HasTaggedIntegral (Function.update (fun _ => 0) c 1) a b 0 := by
  simpa using tagged_integral_update
    (show HasTaggedIntegral (fun _ => 0) a b 0 by
      simpa using (tagged_constant_integral (a := a) (b := b) (0 : ℝ))) c 1

end Ch09
