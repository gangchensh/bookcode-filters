import Mathlib
import Textbook.Ch02.Filters
import Textbook.Ch03.LimitRules

namespace Ch09
open MeasureTheory
open scoped Interval

-- BEGIN polynomial
theorem integral_square : (∫ x : ℝ in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  rw [integral_pow]  -- 用幂函数的定积分公式重写
  norm_num  -- 端点代入后计算为1/3
-- END polynomial

-- BEGIN constant
theorem integral_constant (c a b : ℝ) :
    (∫ _ : ℝ in a..b, c) = (b - a) * c := by
  simpa using (intervalIntegral.integral_const (a := a) (b := b) c)
-- END constant

-- BEGIN ftc
theorem primitive_integral {F f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f x) x)
    (hi : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) = F b - F a := by
  -- 导数关系与可积性给出端点差
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
-- END ftc

-- BEGIN accumulation
theorem accumulation_derivative (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    HasDerivAt (fun t => ∫ x in a..t, f x) (f b) b := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable a b)  -- 连续性保证区间可积
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter
    hf.continuousAt                            -- 提供b处连续性
-- END accumulation

-- BEGIN fine_filter
def fineFilter {P : Type*} (mesh : P → ℝ) : Ch02.BookFilter P where
  sets := {U | ∃ delta > 0, {p | mesh p < delta} ⊆ U}
  univ_mem := ⟨1, by norm_num, fun _ _ => Set.mem_univ _⟩
  inter_mem := by
    intro U V hU hV
    rcases hU with ⟨d, hd, hU⟩                    -- U包含网格小于d的全部分割
    rcases hV with ⟨e, he, hV⟩                    -- V包含网格小于e的全部分割
    refine ⟨min d e, lt_min hd he, ?_⟩            -- 取两个网格上界的最小值
    intro p hp
    change mesh p < min d e at hp
    constructor
    · apply hU
      exact lt_of_lt_of_le hp (min_le_left _ _)
    · apply hV
      exact lt_of_lt_of_le hp (min_le_right _ _)
  upward := by
    intro U V hU hUV
    rcases hU with ⟨d, hd, hU⟩
    exact ⟨d, hd, fun p hp => hUV (hU hp)⟩        -- 同一网格上界仍适用于超集
-- END fine_filter

-- BEGIN fine_proper
theorem fineFilter_proper {P : Type*} (mesh : P → ℝ)
    (hsmall : ∀ d > 0, ∃ p, mesh p < d) :
    Ch02.IsProper (fineFilter mesh) := by
  rintro ⟨d, hd, hmem⟩                            -- 假定空集含有所有充分细的分割
  obtain ⟨p, hp⟩ := hsmall d hd                    -- 选到网格小于d的实际分割
  exact hmem hp                                  -- 该分割不可能属于空集
-- END fine_proper

-- BEGIN linear_integral
theorem integral_linear : (∫ x : ℝ in (0 : ℝ)..1, x) = 1 / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun t => t ^ 2 / 2) x x := by
    intro x
    convert ((hasDerivAt_id x).fun_pow 2).div_const 2 using 1 <;> simp <;> ring
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable _ _         -- 连续性提供被积函数的可积性
  have h := primitive_integral
    (F := fun t : ℝ => t ^ 2 / 2) (f := fun t => t)
    (a := 0) (b := 1) (fun x _ => hd x) hi
  calc
    (∫ x : ℝ in (0 : ℝ)..1, x) = 1 ^ 2 / 2 - 0 ^ 2 / 2 := h
    _ = 1 / 2 := by norm_num                     -- 只计算右边的端点差
-- END linear_integral

-- BEGIN mesh_integral
def HasMeshIntegral {P : Type*} (mesh sums : P → ℝ) (I : ℝ) : Prop :=
  Ch03Approach.Approaches sums (fineFilter mesh) (Ch02.neighborhoodFilter I)

theorem mesh_integral_iff {P : Type*} (mesh sums : P → ℝ) (I : ℝ) :
    HasMeshIntegral mesh sums I ↔
      ∀ ε > 0, ∃ δ > 0, ∀ p, mesh p < δ → |sums p - I| < ε := by
  rw [HasMeshIntegral, Ch03Approach.real_iff]
  rfl
-- END mesh_integral

/-- A partition with `n + 1` intervals and a tag in every closed interval. -/
structure TaggedPartition (a b : ℝ) where
  n : ℕ
  points : Fin (n + 2) → ℝ
  first : points 0 = a
  last : points (Fin.last (n + 1)) = b
  increasing : StrictMono points
  tag : Fin (n + 1) → ℝ
  tag_mem : ∀ i, tag i ∈ Set.Icc (points i.castSucc) (points i.succ)

def TaggedPartition.width {a b : ℝ} (P : TaggedPartition a b) (i : Fin (P.n + 1)) : ℝ :=
  P.points i.succ - P.points i.castSucc

noncomputable def TaggedPartition.mesh {a b : ℝ} (P : TaggedPartition a b) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty P.width

noncomputable def TaggedPartition.riemannSum {a b : ℝ}
    (f : ℝ → ℝ) (P : TaggedPartition a b) : ℝ :=
  ∑ i : Fin (P.n + 1), f (P.tag i) * P.width i

def HasTaggedIntegral (f : ℝ → ℝ) (a b I : ℝ) : Prop :=
  HasMeshIntegral (TaggedPartition.mesh (a := a) (b := b)) (TaggedPartition.riemannSum f) I

theorem tagged_integral_iff (f : ℝ → ℝ) (a b I : ℝ) :
    HasTaggedIntegral f a b I ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b,
        P.mesh < δ → |P.riemannSum f - I| < ε :=
  mesh_integral_iff _ _ _

-- BEGIN absolute
theorem integral_abs_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    |∫ x in a..b, f x| ≤ ∫ x in a..b, |f x| := by
  -- 正向区间上的积分三角不等式
  exact intervalIntegral.abs_integral_le_integral_abs hab
-- END absolute

-- BEGIN adjacent
theorem integral_adjacent {f : ℝ → ℝ} {a c b : ℝ}
    (h₁ : IntervalIntegrable f volume a c)
    (h₂ : IntervalIntegrable f volume c b) :
    (∫ x in a..c, f x) + (∫ x in c..b, f x) = ∫ x in a..b, f x := by
  exact intervalIntegral.integral_add_adjacent_intervals h₁ h₂
-- END adjacent

end Ch09

