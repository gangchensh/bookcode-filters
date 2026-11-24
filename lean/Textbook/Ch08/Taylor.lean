import Mathlib

namespace Ch08
open Asymptotics Filter
open scoped Topology

-- BEGIN asymptotic
def BookLittleO {α : Type*} (r g : α → ℝ)            -- 任意正倍数最终控制r
    (F : Filter α) : Prop :=
  ∀ ε > 0, ∀ᶠ x in F, |r x| ≤ ε * |g x|

theorem littleO_mathlib {α : Type*} (r g : α → ℝ) (F : Filter α) :
    BookLittleO r g F ↔ r =o[F] g := by
  simpa only [BookLittleO, Real.norm_eq_abs] using
    (isLittleO_iff : r =o[F] g ↔ _).symm
-- END asymptotic

-- BEGIN bigo
def BookBigO {α : Type*} (r g : α → ℝ) (F : Filter α) : Prop :=
  ∃ C ≥ 0, ∀ᶠ x in F, |r x| ≤ C * |g x|             -- 一个固定非负倍数最终控制r

theorem bigO_mathlib {α : Type*} (r g : α → ℝ) (F : Filter α) :
    BookBigO r g F ↔ r =O[F] g := by
  constructor
  · rintro ⟨C, _, hC⟩
    exact isBigO_iff.mpr ⟨C, by simpa only [Real.norm_eq_abs] using hC⟩
  · intro h
    obtain ⟨C, hC, hb⟩ := isBigO_iff'.mp h
    exact ⟨C, hC.le, by simpa only [Real.norm_eq_abs] using hb⟩
-- END bigo

-- BEGIN rules
theorem littleO_add {α : Type*} {F : Filter α} {r s g : α → ℝ}
    (hr : BookLittleO r g F) (hs : BookLittleO s g F) :
    BookLittleO (fun x => r x + s x) g F := by
  intro ε hε
  filter_upwards [hr (ε/2) (by linarith), hs (ε/2) (by linarith)] with x hx hy
  calc
    |r x + s x| ≤ |r x| + |s x| := abs_add_le _ _
    _ ≤ ε * |g x| := by linarith                -- 两个ε/2界合成同一ε界

theorem littleO_comp {α β : Type*} {F : Filter α} {G : Filter β}
    {r g : β → ℝ} {u : α → β}
    (hr : BookLittleO r g G) (hu : Tendsto u F G) :
    BookLittleO (r ∘ u) (g ∘ u) F := by
  intro ε hε
  exact hu.eventually (hr ε hε)                -- 将G中的最终范围取原像拉回F

theorem bigO_comp {α β : Type*} {F : Filter α} {G : Filter β}
    {r g : β → ℝ} {u : α → β}
    (hr : BookBigO r g G) (hu : Tendsto u F G) :
    BookBigO (r ∘ u) (g ∘ u) F := by
  obtain ⟨C, hC, h⟩ := hr
  exact ⟨C, hC, hu.eventually h⟩               -- 原像保留同一个控制常数

theorem littleO_mul_bigO {α : Type*} {F : Filter α} {r g s k : α → ℝ}
    (hr : BookLittleO r g F) (hs : BookBigO s k F) :
    BookLittleO (fun x => r x * s x) (fun x => g x * k x) F := by
  apply (littleO_mathlib _ _ _).mpr
  exact ((littleO_mathlib _ _ _).mp hr).mul_isBigO
    ((bigO_mathlib _ _ _).mp hs)                 -- 两个因子的控制合成乘积控制
-- END rules

-- BEGIN exact
theorem reciprocal_identity (h : ℝ) (hh : 1 + h ≠ 0) :
    1 / (1 + h) - (1 - h + h ^ 2) = -h ^ 3 / (1 + h) := by
  field_simp [hh]  -- 用1+h≠0清除分母
  ring  -- 核对有限多项式恒等式

theorem reciprocal_error (h : ℝ) (hh : |h| ≤ 1 / 2) :
    |1 / (1 + h) - (1 - h + h ^ 2)| ≤ 2 * |h| ^ 3 := by
  have hl : -(1 / 2 : ℝ) ≤ h := (abs_le.mp hh).1  -- 由绝对值界取出h的下界
  have hd : 0 < 1 + h := by linarith  -- 分母至少为1/2，因而为正
  rw [reciprocal_identity h (ne_of_gt hd), abs_div, abs_neg,
    abs_pow, abs_of_pos hd]
  apply (div_le_iff₀ hd).2  -- 把商的上界转为乘法不等式
  nlinarith [pow_nonneg (abs_nonneg h) 3]  -- 用1+h≥1/2及|h|³≥0完成估计
-- END exact

-- BEGIN taylor
theorem lagrange_remainder {f : ℝ → ℝ} {a x : ℝ} {n : ℕ}
    (hax : a ≠ x) (hf : ContDiffOn ℝ (n + 1) f (Set.uIcc a x)) :
    ∃ c ∈ Set.uIoo a x,
      f x - taylorWithinEval f n (Set.uIcc a x) a x =
        iteratedDeriv (n + 1) f c * (x - a) ^ (n + 1) /
          Nat.factorial (n + 1) := by
  -- 由区间光滑性取得中间点c
  exact
    taylor_mean_remainder_lagrange_iteratedDeriv hax hf
-- END taylor

-- BEGIN lagrange_bound
theorem lagrange_bound {f : ℝ → ℝ} {a x M : ℝ} {n : ℕ}
    (hax : a ≠ x) (hf : ContDiffOn ℝ (n + 1) f (Set.uIcc a x))
    (hM : ∀ c ∈ Set.uIoo a x, |iteratedDeriv (n + 1) f c| ≤ M) :
    |f x - taylorWithinEval f n (Set.uIcc a x) a x| ≤
      M * |x - a| ^ (n + 1) / Nat.factorial (n + 1) := by
  obtain ⟨c, hc, he⟩ := lagrange_remainder hax hf  -- 取严格介于端点的余项点
  have hnum := mul_le_mul_of_nonneg_right (hM c hc)
    (pow_nonneg (abs_nonneg (x - a)) (n + 1))     -- 在c处应用共同导数界
  calc
    |f x - taylorWithinEval f n (Set.uIcc a x) a x| =
        |iteratedDeriv (n + 1) f c| * |x - a| ^ (n + 1) /
          (Nat.factorial (n + 1) : ℝ) := by
      rw [he, abs_div, abs_mul, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Nat.factorial (n + 1))]
    _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)
-- END lagrange_bound

-- BEGIN cubic_scale
theorem cubic_scale_bound (r h K eps : ℝ)
    (hK : 0 ≤ K) (heps : 0 < eps)
    (hh : |h| ≤ eps / (K + 1))
    (hr : |r| ≤ K * |h| ^ 3) :
    |r| ≤ eps * |h| ^ 2 := by
  have hh' : |h| * (K + 1) ≤ eps :=
    (le_div_iff₀ (by linarith : 0 < K + 1)).mp hh
  have hk : K * |h| ≤ eps := by nlinarith [abs_nonneg h]
  calc
    |r| ≤ K * |h| ^ 3 := hr
    _ = (K * |h|) * |h| ^ 2 := by ring           -- 分出一个趋零的|h|因子
    _ ≤ eps * |h| ^ 2 :=
      mul_le_mul_of_nonneg_right hk (sq_nonneg |h|)
-- END cubic_scale

end Ch08
