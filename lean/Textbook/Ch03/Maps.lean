import Textbook.Ch03.LimitRules

namespace Ch03Maps
open Ch02 Ch03 Ch03Approach

-- BEGIN image
def imageFilter {α β : Type*} (f : α → β)            -- 用原像构造像滤子
    (F : BookFilter α) : BookFilter β where
  sets := {V | f ⁻¹' V ∈ F.sets}
  univ_mem := F.univ_mem
  inter_mem := by
    intro A B hA hB
    exact F.inter_mem hA hB                         -- 原像保持交集
  upward := by
    intro A B hA hAB
    exact F.upward hA (fun x hx => hAB hx)          -- 原像保持集合包含
-- END image

-- BEGIN order
def Finer {α : Type*} (F G : BookFilter α) : Prop := -- F比G更细：F含有G的每个成员
  ∀ A, A ∈ G.sets → A ∈ F.sets

theorem approaches_image_iff {α β : Type*}
    (f : α → β) (F : BookFilter α) (G : BookFilter β) :
    Approaches f F G ↔ Finer (imageFilter f F) G := Iff.rfl

theorem image_mathlib {α β : Type*}
    (f : α → β) (F : BookFilter α) :
    toMathlib (imageFilter f F) = Filter.map f (toMathlib F) := by
  ext V                                            -- 比较任意目标集合的成员命题
  rfl
-- END order

-- BEGIN monotone
theorem source_finer {α β : Type*} {f : α → β}
    {F F' : BookFilter α} {G : BookFilter β}
    (hF : Finer F' F) (hf : Approaches f F G) :
    Approaches f F' G := by
  intro V hV
  exact hF (f ⁻¹' V) (hf V hV)                     -- 原像的最终要求在更细源中仍成立

theorem target_coarser {α β : Type*} {f : α → β}
    {F : BookFilter α} {G G' : BookFilter β}
    (hG : Finer G G') (hf : Approaches f F G) :
    Approaches f F G' := by
  intro V hV
  exact hf V (hG V hV)                             -- 较粗目标的要求已包含在原要求中
-- END monotone

-- BEGIN generated
def generatedFilter {ι α : Type*} (B : ι → Set α)
    (hI : Nonempty ι)
    (hB : ∀ i j, ∃ k, B k ⊆ B i ∩ B j) : BookFilter α where
  sets := {U | ∃ i, B i ⊆ U}                       -- 成员必须包含某个基本集合
  univ_mem := by
    rcases hI with ⟨i⟩
    exact ⟨i, Set.subset_univ _⟩
  inter_mem := by
    rintro U V ⟨i, hi⟩ ⟨j, hj⟩
    rcases hB i j with ⟨k, hk⟩                     -- 找同时落在两个基本集合内的B k
    exact ⟨k, fun x hx => ⟨hi (hk hx).1, hj (hk hx).2⟩⟩
  upward := by
    rintro U V ⟨i, hi⟩ hUV
    exact ⟨i, fun x hx => hUV (hi hx)⟩
-- END generated

-- BEGIN generated_proper
theorem generated_proper_iff {ι α : Type*} (B : ι → Set α)
    (hI : Nonempty ι) (hB : ∀ i j, ∃ k, B k ⊆ B i ∩ B j) :
    IsProper (generatedFilter B hI hB) ↔ ∀ i, (B i).Nonempty := by
  classical
  constructor
  · intro h i
    by_contra hn                                   -- 假设B i没有元素
    apply h
    exact ⟨i, fun x hx => False.elim (hn ⟨x, hx⟩)⟩
  · rintro h ⟨i, hi⟩                              -- 空集若为成员，就包含某个B i
    rcases h i with ⟨x, hx⟩
    exact hi hx                                    -- B i中的x不可能属于空集
-- END generated_proper

-- BEGIN product
def productFilter {α β : Type*}
    (F : BookFilter α) (G : BookFilter β) : BookFilter (α × β) where
  sets := {U | ∃ A ∈ F.sets, ∃ B ∈ G.sets, A ×ˢ B ⊆ U}
  univ_mem := ⟨Set.univ, F.univ_mem, Set.univ, G.univ_mem,
    Set.subset_univ _⟩
  inter_mem := by
    rintro U V ⟨A, hA, B, hB, hU⟩ ⟨C, hC, D, hD, hV⟩
    refine ⟨A ∩ C, F.inter_mem hA hC,
      B ∩ D, G.inter_mem hB hD, ?_⟩                -- 用两个交集组成新矩形
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hU ⟨hx.1, hy.1⟩, hV ⟨hx.2, hy.2⟩⟩
  upward := by
    rintro U V ⟨A, hA, B, hB, hU⟩ hUV
    exact ⟨A, hA, B, hB, fun p hp => hUV (hU hp)⟩
-- END product

-- BEGIN pair
theorem approaches_pair {α β γ : Type*}
    {F : BookFilter α} {G : BookFilter β} {H : BookFilter γ}
    {f : α → β} {g : α → γ}
    (hf : Approaches f F G) (hg : Approaches g F H) :
    Approaches (fun x => (f x, g x)) F (productFilter G H) := by
  rintro U ⟨A, hA, B, hB, hU⟩
  apply F.upward (F.inter_mem (hf A hA) (hg B hB))
  intro x hx
  exact hU hx                                      -- 两个输出要求在同一个输入范围成立
-- END pair

-- BEGIN product_proper
theorem product_proper {α β : Type*}
    {F : BookFilter α} {G : BookFilter β}
    (hF : IsProper F) (hG : IsProper G) :
    IsProper (productFilter F G) := by
  rintro ⟨A, hA, B, hB, hEmpty⟩
  rcases eventually_exists hF hA with ⟨x, hx⟩      -- 从F的成员A中取到一个点
  rcases eventually_exists hG hB with ⟨y, hy⟩      -- 从G的成员B中取到一个点
  exact hEmpty (show (x, y) ∈ A ×ˢ B from ⟨hx, hy⟩) -- 矩形中的点不可能属于空集
-- END product_proper

end Ch03Maps
