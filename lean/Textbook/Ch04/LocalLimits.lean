import Textbook.Ch05.Sequences

namespace Ch04Local
open Ch02 Ch03 Ch03Approach Ch05

def domainFilter (a : ℝ) (S : Set ℝ) : BookFilter ℝ :=  -- 在定义域内接近a，并排除中心点
  nearWithin a {x | x ∈ S ∧ x ≠ a}

def DomainLimit (f : ℝ → ℝ) (S : Set ℝ) (a b : ℝ) : Prop :=
  Approaches f (domainFilter a S) (neighborhoodFilter b)  -- 本书的去心定义域极限

def IsAccumulationPoint (S : Set ℝ) (a : ℝ) : Prop :=  -- 每个去心邻域都能遇到定义域
  ∀ δ > 0, ∃ x, |x-a| < δ ∧ x ∈ S ∧ x ≠ a

theorem domain_limit_iff (f : ℝ → ℝ) (S : Set ℝ) (a b : ℝ) :
    DomainLimit f S a b ↔ ∀ ε > 0, ∃ δ > 0, ∀ x,
      |x-a| < δ → (x ∈ S ∧ x ≠ a) → |f x-b| < ε := by
  unfold DomainLimit
  rw [real_iff]                                       -- 只展开目标邻域，保留定义域条件
  rfl

theorem domain_proper {S : Set ℝ} {a : ℝ} (ha : IsAccumulationPoint S a) :
    IsProper (domainFilter a S) := by                 -- 聚点条件排除源滤子退化
  rintro ⟨δ, hδ, hempty⟩
  rcases ha δ hδ with ⟨x, hx, hS, hne⟩
  exact hempty hx ⟨hS, hne⟩

theorem domain_limit_unique {f : ℝ → ℝ} {S : Set ℝ} {a b c : ℝ}
    (ha : IsAccumulationPoint S a)
    (hb : DomainLimit f S a b) (hc : DomainLimit f S a c) : b = c :=
  Ch03Rules.real_limit_unique (domain_proper ha) hb hc  -- 复用第五章的唯一性

theorem domain_limit_congr {f g : ℝ → ℝ} {S : Set ℝ} {a b : ℝ}
    (hfg : Eventually (domainFilter a S) (fun x => f x = g x))
    (hf : DomainLimit f S a b) : DomainLimit g S a b :=
  Ch03Rules.approaches_congr hfg hf                  -- 只要求在同一源滤子上最终相等

theorem restrict_domain {f : ℝ → ℝ} {S T : Set ℝ} {a b : ℝ}
    (hTS : T ⊆ S) (hf : DomainLimit f S a b) : DomainLimit f T a b := by
  apply (domain_limit_iff _ _ _ _).2
  intro ε hε
  rcases (domain_limit_iff _ _ _ _).1 hf ε hε with ⟨δ, hδ, hδf⟩
  exact ⟨δ, hδ, fun x hx hT => hδf x hx ⟨hTS hT.1, hT.2⟩⟩

theorem limit_eventually_bounded {α : Type*} {f : α → ℝ} {F : BookFilter α} {b : ℝ}
    (hf : Approaches f F (neighborhoodFilter b)) :
    Eventually F (fun x => |f x| < |b|+1) := by       -- 有限极限给出同一源上的最终界
  apply F.upward ((real_iff _ _ _).1 hf 1 zero_lt_one)
  intro x hx
  change |f x-b| < 1 at hx
  change |f x| < |b|+1
  calc
    |f x| = |(f x-b)+b| := by rw [sub_add_cancel]
    _ ≤ |f x-b|+|b| := abs_add_le _ _
    _ < |b|+1 := by linarith

theorem limit_eventually_nonzero {α : Type*} {f : α → ℝ} {F : BookFilter α} {b : ℝ}
    (hf : Approaches f F (neighborhoodFilter b)) (hb : b ≠ 0) :
    Eventually F (fun x => f x ≠ 0) := by            -- 分母的非零极限保证最终可除
  have hpos : 0 < |b| := abs_pos.mpr hb
  apply F.upward ((real_iff _ _ _).1 hf (|b|/2) (half_pos hpos))
  intro x hx
  change |f x-b| < |b|/2 at hx
  change f x ≠ 0
  intro hzero
  rw [hzero, zero_sub, abs_neg] at hx                -- 若f(x)=0，距离等于|b|
  linarith

theorem sequence_into_domain {x : ℕ → ℝ} {S : Set ℝ} {a : ℝ}
    (hx : Converges x a) (hS : ∀ n, x n ∈ S ∧ x n ≠ a) :
    Approaches x tailFilter (domainFilter a S) := by  -- 收敛序列还须满足定义域和去心要求
  rintro V ⟨δ, hδ, hV⟩
  rcases (converges_iff x a).1 hx δ hδ with ⟨N, hN⟩
  exact ⟨N, fun n hn => hV (hN n hn) (hS n)⟩

theorem domain_limit_sequence {f : ℝ → ℝ} {S : Set ℝ} {a b : ℝ}
    (hf : DomainLimit f S a b) (x : ℕ → ℝ)
    (hx : Converges x a) (hS : ∀ n, x n ∈ S ∧ x n ≠ a) :
    Converges (fun n => f (x n)) b :=                -- 序列判别的正向是滤子复合
  Ch03Rules.approaches_comp (sequence_into_domain hx hS) hf

theorem sequential_criterion (f : ℝ → ℝ) (S : Set ℝ) (a b : ℝ) :
    DomainLimit f S a b ↔ ∀ x : ℕ → ℝ,
      (∀ n, x n ∈ S ∧ x n ≠ a) → Converges x a →
      Converges (fun n => f (x n)) b := by           -- 必须检查全部合格序列
  classical
  constructor
  · intro hf x hS hx
    exact domain_limit_sequence hf x hx hS
  · intro hseq
    by_contra hfail
    rw [domain_limit_iff] at hfail
    push Not at hfail
    rcases hfail with ⟨ε, hε, hbad⟩                  -- 一个固定ε对所有半径都失败
    have hw : ∀ n : ℕ, ∃ y : ℝ,
        |y-a| < 1/((n : ℝ)+1) ∧ (y ∈ S ∧ y ≠ a) ∧ ε ≤ |f y-b| := by
      intro n
      exact hbad (1/((n : ℝ)+1)) (by positivity)
    choose x hx using hw                             -- 在每个缩小邻域内选一个反例点
    have hxlim : Converges x a := by
      apply (converges_iff x a).2
      intro η hη
      rcases Ch02Eventually.eventually_reciprocal η hη with ⟨N, hN⟩
      exact ⟨N, fun n hn => ((hx n).1).trans (hN n hn)⟩
    have hfx := hseq x (fun n => (hx n).2.1) hxlim
    rcases (converges_iff _ b).1 hfx ε hε with ⟨N, hN⟩
    exact (not_le_of_gt (hN N le_rfl)) (hx N).2.2    -- 同一项距离既<ε又≥ε

theorem lift_domain {α : Type*} {f : α → ℝ} {F : BookFilter α}
    {T : Set ℝ} {b : ℝ}
    (hf : Approaches f F (neighborhoodFilter b))
    (hT : Eventually F (fun x => f x ∈ T ∧ f x ≠ b)) :
    Approaches f F (domainFilter b T) := by          -- 把有限极限提升到更严格的中间源
  rintro V ⟨δ, hδ, hV⟩
  apply F.upward (F.inter_mem ((real_iff _ _ _).1 hf δ hδ) hT)
  intro x hx
  exact hV hx.1 hx.2

theorem compose_domain {α : Type*} {f : α → ℝ} {g : ℝ → ℝ}
    {F : BookFilter α} {T : Set ℝ} {b c : ℝ}
    (hf : Approaches f F (neighborhoodFilter b))
    (hT : Eventually F (fun x => f x ∈ T ∧ f x ≠ b))
    (hg : DomainLimit g T b c) :
    Approaches (fun x => g (f x)) F (neighborhoodFilter c) :=
  Ch03Rules.approaches_comp (lift_domain hf hT) hg    -- 中间滤子现在准确匹配

theorem full_of_domain_and_value {f : ℝ → ℝ} {a b : ℝ}
    (hf : DomainLimit f Set.univ a b) (ha : f a = b) :
    Approaches f (neighborhoodFilter a) (neighborhoodFilter b) := by
  apply (real_iff _ _ _).2                            -- 在去心证明之外补上中心点
  intro ε hε
  rcases (domain_limit_iff _ _ _ _).1 hf ε hε with ⟨δ, hδ, hδf⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  change |f x-b| < ε
  by_cases hxa : x = a
  · simpa [hxa, ha] using hε
  · exact hδf x hx ⟨Set.mem_univ x, hxa⟩

theorem polynomial_near_one :
    Approaches (fun x : ℝ => x^2+x+1)
      (neighborhoodFilter 1) (neighborhoodFilter 3) := by
  apply (real_iff _ _ _).2
  intro ε hε
  refine ⟨min 1 (ε/4), lt_min zero_lt_one (by positivity), ?_⟩
  intro x hx
  change |x-1| < min 1 (ε/4) at hx
  change |(x^2+x+1)-3| < ε
  have hx1 := lt_of_lt_of_le hx (min_le_left 1 (ε/4))
  have hxε := lt_of_lt_of_le hx (min_le_right 1 (ε/4))
  have hrange := abs_lt.mp hx1
  have hfactor : |x+2| ≤ 4 := by rw [abs_of_pos (by linarith)]; linarith
  calc
    |(x^2+x+1)-3| = |x-1| * |x+2| := by
      rw [show (x^2+x+1)-3 = (x-1)*(x+2) by ring, abs_mul]
    _ ≤ |x-1| * 4 := mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
    _ < ε := by linarith

theorem cubic_ratio_limit :
    DomainLimit (fun x : ℝ => (x^3-1)/(x-1)) Set.univ 1 3 := by
  have hp : DomainLimit (fun x : ℝ => x^2+x+1) Set.univ 1 3 := by
    apply (domain_limit_iff _ _ _ _).2
    intro ε hε
    rcases (real_iff _ _ _).1 polynomial_near_one ε hε with ⟨δ, hδ, hδp⟩
    exact ⟨δ, hδ, fun x hx _ => hδp hx⟩
  apply domain_limit_congr (f := fun x : ℝ => x^2+x+1) (g := fun x => (x^3-1)/(x-1)) ?_ hp
  refine ⟨1, zero_lt_one, ?_⟩                       -- 约分只需x≠1，半径可取任意正数
  intro x hx hS
  have hne : x-1 ≠ 0 := sub_ne_zero.mpr hS.2
  change x^2+x+1 = (x^3-1)/(x-1)
  field_simp [hne]; ring

theorem sqrt_domain_zero :
    DomainLimit Real.sqrt (Set.Ici 0) 0 0 := by       -- 保留实平方根的自然定义域
  apply (domain_limit_iff _ _ _ _).2
  intro ε hε
  refine ⟨ε^2, by positivity, ?_⟩                   -- 取δ=ε²
  intro x hx hS
  have hxnonneg : 0 ≤ x := hS.1
  have hxlt : x < ε^2 := by
    simpa [abs_of_nonneg hxnonneg] using hx
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs2 : (Real.sqrt x)^2 = x := Real.sq_sqrt hxnonneg
  have hsmall : Real.sqrt x < ε := by nlinarith      -- 由非负性比较平方
  change |Real.sqrt x-0| < ε
  simpa [abs_of_nonneg hs] using hsmall

theorem domain_limit_sequence_eventual {f : ℝ → ℝ} {S : Set ℝ} {a b : ℝ}
    (hf : DomainLimit f S a b) {x : ℕ → ℝ} (hx : Converges x a)
    (hS : Eventually tailFilter (fun n => x n ∈ S ∧ x n ≠ a)) :
    Converges (fun n => f (x n)) b :=                -- 允许有限个不合格的初始项
  Ch03Rules.approaches_comp (lift_domain hx hS) hf

theorem damped_sine_limit :
    DomainLimit (fun x : ℝ => x*Real.sin (1/x)) Set.univ 0 0 := by
  apply (domain_limit_iff _ _ _ _).2
  intro ε hε
  refine ⟨ε, hε, ?_⟩                                -- 取δ=ε
  intro x hx hS
  have hxε : |x| < ε := by simpa only [sub_zero] using hx
  change |x*Real.sin (1/x)-0| < ε
  rw [sub_zero, abs_mul]
  calc
    |x| * |Real.sin (1/x)| ≤ |x| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
    _ < ε := by simpa using hxε                      -- 趋零因子控制整个振荡表达式

theorem continuity_sequence_test (f : ℝ → ℝ) (a : ℝ) :
    Approaches f (neighborhoodFilter a) (neighborhoodFilter (f a)) ↔
      ∀ x : ℕ → ℝ, Converges x a → Converges (fun n => f (x n)) (f a) := by
  constructor                                        -- 完整邻域允许检测数列反复取中心值
  · intro hf x hx
    exact Ch03Rules.approaches_comp hx hf
  · intro hseq
    apply full_of_domain_and_value ?_ rfl             -- 中心值条件此处自动满足
    apply (sequential_criterion f Set.univ a (f a)).2
    intro x hS hx
    exact hseq x hx                                  -- 全部趋近数列当然包含去心合格数列

end Ch04Local
