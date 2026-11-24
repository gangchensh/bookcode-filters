import Textbook.Ch06.Estimates
import Textbook.Ch04.LocalLimits

namespace Ch06
open Ch02 Ch03 Ch03Approach Ch05

theorem derivative_sequence_iff (f : ℝ → ℝ) (a d : ℝ) :
    HasDerivative f a d ↔ ∀ h : ℕ → ℝ,
      (∀ n, h n ≠ 0) → Converges h 0 →
      Converges (fun n => (f (a+h n)-f a)/h n) d := by
  rw [derivative_increment_iff]
  simpa only [Ch04Local.DomainLimit, Ch04Local.domainFilter, Set.mem_univ, true_and, punctured] using
    Ch04Local.sequential_criterion (fun h => (f (a+h)-f a)/h) Set.univ 0 d

theorem derivative_perturbation {f v : ℝ → ℝ} {a d : ℝ}
    (hd : HasDerivative f a d) (hv : v a = 0)
    (hsmall : Approaches (fun h => v (a+h)/h) (punctured 0) (neighborhoodFilter 0)) :
    HasDerivative (fun x => f x+v x) a d := by
  apply (derivative_increment_iff _ _ _).2
  have h := Ch04.limit_add ((derivative_increment_iff _ _ _).1 hd) hsmall
  rw [add_zero] at h
  have he (x : ℝ) : (f (a+x)-f a)/x + v (a+x)/x =
      ((f (a+x)+v (a+x))-(f a+v a))/x := by
    rw [hv, ← add_div]
    congr 1
    ring
  exact Ch03Rules.approaches_congr (eventually_of_forall he) h

theorem symmetric_derivative {f : ℝ → ℝ} {a d : ℝ} (hd : HasDerivative f a d) :
    Approaches (fun h => (f (a+h)-f (a-h))/(2*h)) (punctured 0) (neighborhoodFilter d) := by
  apply (increment_limit_iff _ _).2
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := (increment_limit_iff _ _).1
    ((derivative_increment_iff _ _ _).1 hd) ε hε
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have hn : h ≠ 0 := abs_pos.mp hh.1
  have hp := H h hh
  have hm := H (-h) (by simpa only [abs_neg] using hh)
  have he : (f (a+h)-f (a-h))/(2*h)-d =
      ((f (a+h)-f a)/h-d + ((f (a+(-h))-f a)/(-h)-d))/2 := by
    simp only [← sub_eq_add_neg]
    field_simp [hn]
    <;> ring
  rw [he]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), div_lt_iff₀ (by norm_num : (0:ℝ)<2)]
  exact (abs_add_le _ _).trans_lt (by linarith)

theorem abs_symmetric_not_derivative :
    (∀ h : ℝ, (|0+h|-|0-h|)/(2*h) = 0) ∧
      ¬ ∃ d, HasDerivative (abs : ℝ → ℝ) 0 d :=
  ⟨abs_symmetric_zero, abs_has_no_derivative⟩

theorem identity_quotient_center (a : ℝ) :
    HasDerivative (fun x => x) a 1 ∧
      ¬ Approaches (fun x => (x-a)/(x-a)) (neighborhoodFilter a) (neighborhoodFilter 1) := by
  refine ⟨derivative_id a, fun H => ?_⟩
  obtain ⟨δ, hδ, H⟩ := (real_iff _ _ _).1 H 1 zero_lt_one
  have hx : a ∈ Ch02Neighborhoods.epsNeighborhood a δ := by change |a-a| < δ; simpa using hδ
  have h := H hx
  change |(a-a)/(a-a)-1| < 1 at h
  norm_num at h

end Ch06
