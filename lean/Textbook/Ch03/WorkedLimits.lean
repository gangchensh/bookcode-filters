import Textbook.Ch03.Approach

namespace Ch03WorkedLimits
open Ch02 Ch03 Ch03Approach

theorem constant_limit {α : Type*} (F : BookFilter α) (b : ℝ) :
    Approaches (fun _ => b) F (neighborhoodFilter b) := by                      -- 常值函数沿任意源滤子趋于其常值
  apply (real_iff _ _ _).2
  intro ε hε
  apply eventually_of_forall                                                    -- 距离界对每个输入都成立
  intro x
  simpa using hε                                                                -- |b-b|=0<ε

theorem affine_direct (a : ℝ) :                                                 -- 直接证明2x+3趋于2a+3
    Approaches (fun x : ℝ => 2*x+3)
      (neighborhoodFilter a) (neighborhoodFilter (2*a+3)) := by
  apply (real_iff _ _ _).2                                                      -- 目标：任给ε>0，距离界最终成立
  intro ε hε
  refine ⟨ε/2, half_pos hε, ?_⟩                                                 -- 取δ=ε/2
  intro x hx
  change |(2*x+3)-(2*a+3)| < ε
  change |x-a| < ε/2 at hx
  rw [show (2*x+3)-(2*a+3) = 2*(x-a) by ring, abs_mul]
  norm_num                                                                      -- 将|2|化为2
  linarith                                                                      -- 由|x-a|<ε/2推出2|x-a|<ε

theorem square_zero :                                                           -- 由定义证明x²在零处趋于零
    Approaches (fun x : ℝ => x^2)
      (neighborhoodFilter 0) (neighborhoodFilter 0) := by
  apply (real_iff _ _ _).2
  intro ε hε
  refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩                                   -- 同时要求|x|<1及|x|<ε
  intro x hx
  change |x-0| < min 1 ε at hx
  change |x^2-0| < ε
  simp only [sub_zero] at hx ⊢
  have h1 : |x| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have hεx : |x| < ε := lt_of_lt_of_le hx (min_le_right _ _)
  rw [abs_of_nonneg (sq_nonneg x)]                                              -- |x²|=x²
  nlinarith [sq_abs x, abs_nonneg x]                                            -- x²=|x|²≤|x|<ε

theorem quotient_sequence :                          -- n/(n+1)收敛于1
    Approaches (fun n : ℕ => (n : ℝ)/((n : ℝ)+1))
      tailFilter (neighborhoodFilter 1) := by
  apply (sequence_iff _ _).2
  intro ε hε
  rcases Ch02Eventually.eventually_reciprocal ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩                                     -- 复用倒数估计中的阈值
  intro n hn
  have hpos : 0 < (n : ℝ)+1 := by positivity
  have hid : (n : ℝ)/((n : ℝ)+1)-1 = -(1/((n : ℝ)+1)) := by
    field_simp; ring                                  -- 消去分母，再核对n-(n+1)=-1
  rw [hid, abs_neg, abs_of_pos (one_div_pos.mpr hpos)]
  exact hN n hn                                       -- 距离恰为1/(n+1)

theorem square_atBot :                               -- x趋于负无穷时，x²趋于正无穷
    Approaches (fun x : ℝ => x^2) (lowerFilter ℝ) (upperFilter ℝ) := by
  rintro V ⟨M, hM⟩                                   -- V包含上尾集[M,+∞)
  refine ⟨-(|M|+1), ?_⟩                              -- 在负方向取阈值B=-(|M|+1)
  intro x hx
  apply hM (x^2)
  have hnonneg := abs_nonneg M
  have hbound := le_abs_self M
  nlinarith [sq_nonneg (x+(|M|+1)), sq_nonneg (|M|)]

end Ch03WorkedLimits

namespace Ch03FilterProofs
open Ch02 Ch03Approach

theorem double_members (a : ℝ) :                      -- 直接证明每个目标成员的原像属于源滤子
    Approaches (fun x : ℝ => 2*x)
      (neighborhoodFilter a) (neighborhoodFilter (2*a)) := by
  intro V hV                                         -- 任取2a的邻域V
  rcases hV with ⟨ε, hε, hεV⟩                        -- N_ε(2a)⊆V
  refine ⟨ε/2, half_pos hε, ?_⟩                     -- 为原像构造基本邻域N_(ε/2)(a)
  intro x hx
  apply hεV                                          -- 只需证明2x属于N_ε(2a)
  change |x-a| < ε/2 at hx
  change |2*x-2*a| < ε
  rw [show 2*x-2*a = 2*(x-a) by ring, abs_mul]
  norm_num
  linarith                                            -- 验证基本邻域包含于原像

theorem constant_members {α : Type*}                                            -- 常值函数直接用全空间与向上封闭证明
    (F : BookFilter α) (b : ℝ) :
    Approaches (fun _ => b) F (neighborhoodFilter b) := by
  intro V hV
  have hb : b ∈ V := by
    rcases hV with ⟨ε, hε, hεV⟩
    apply hεV                                                                   -- 只需证明b属于基本邻域
    change |b-b| < ε
    simpa using hε                                                              -- |b-b|=0<ε
  exact F.upward F.univ_mem (fun _ _ => hb)                                     -- 常值函数下V的原像是全空间

end Ch03FilterProofs
