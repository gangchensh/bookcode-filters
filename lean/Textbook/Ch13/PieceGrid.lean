import Textbook.Ch13.Breakpoints

namespace Ch13

open Set Filter MeasureTheory
open scoped BigOperators Topology Interval

/-- Points of the original grid strictly inside the piece, with both endpoints. -/
noncomputable def pieceNodes {a b : ℝ} (P : Ch09.TaggedPartition a b)
    (l r : ℝ) : Finset ℝ :=
  insert l (insert r ((Finset.univ.image P.points).filter fun x => x ∈ Ioo l r))

theorem mem_pieceNodes {a b l r x : ℝ} (P : Ch09.TaggedPartition a b) :
    x ∈ pieceNodes P l r ↔ x = l ∨ x = r ∨ (∃ i, P.points i = x) ∧ x ∈ Ioo l r := by
  simp [pieceNodes]

/-- Sort the nodes and use the left endpoint as the tag on each cell. -/
noncomputable def pieceGrid {a b l r : ℝ} (P : Ch09.TaggedPartition a b)
    (hlr : l < r) : Ch09.TaggedPartition l r := by
  classical
  let s := pieceNodes P l r
  have hl : l ∈ s := (mem_pieceNodes P).2 (Or.inl rfl)
  have hr : r ∈ s := (mem_pieceNodes P).2 (Or.inr (Or.inl rfl))
  have hc : 2 ≤ s.card := by
    have hs : ({l, r} : Finset ℝ) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hl
      · simpa only [Finset.mem_singleton.mp hx] using hr
    simpa [hlr.ne] using Finset.card_le_card hs
  have hsize : s.card = (s.card - 2) + 2 := by omega
  let f := s.orderEmbOfFin hsize
  have hmem (i) : f i ∈ s := Finset.orderEmbOfFin_mem _ _ _
  have hbounds (i) : f i ∈ Icc l r := by
    rcases (mem_pieceNodes P).mp (hmem i) with h | h | ⟨_, h⟩
    · rw [h]
      exact left_mem_Icc.mpr hlr.le
    · rw [h]
      exact right_mem_Icc.mpr hlr.le
    · exact Ioo_subset_Icc_self h
  have hex (x) (hx : x ∈ s) : ∃ i, f i = x := by
    have hrange : x ∈ range f := by
      change x ∈ range (s.orderEmbOfFin hsize)
      rw [Finset.range_orderEmbOfFin]
      exact hx
    exact hrange
  refine ⟨s.card - 2, f, ?_, ?_, f.strictMono, fun i => f i.castSucc, ?_⟩
  · obtain ⟨i, hi⟩ := hex l hl
    exact le_antisymm (hi ▸ f.monotone (Fin.zero_le i)) (hbounds 0).1
  · obtain ⟨i, hi⟩ := hex r hr
    exact le_antisymm (hbounds _).2 (hi ▸ f.monotone (Fin.le_last i))
  · exact fun i => left_mem_Icc.mpr (f.monotone (Fin.castSucc_le_succ (i := i)))

theorem range_pieceGrid {a b l r : ℝ} (P : Ch09.TaggedPartition a b) (hlr : l < r) :
    range (pieceGrid P hlr).points = ↑(pieceNodes P l r) := by
  exact Finset.range_orderEmbOfFin _ _

theorem no_node_between {a b : ℝ} (P : Ch09.TaggedPartition a b)
    (i : Fin (P.n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (P.points i.castSucc) (P.points i.succ)) :
    x ∉ range P.points := by
  rintro ⟨j, rfl⟩
  have h₁ := P.increasing.lt_iff_lt.mp hx.1
  have h₂ := P.increasing.lt_iff_lt.mp hx.2
  change i.val < j.val at h₁
  change j.val < i.val + 1 at h₂
  omega

theorem pieceGrid_mesh_le {a b l r : ℝ} (P : Ch09.TaggedPartition a b)
    (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b) :
    (pieceGrid P hlr).mesh ≤ P.mesh := by
  let Q := pieceGrid P hlr
  apply Finset.sup'_le
  intro i _
  let x := Q.points i.castSucc
  let y := Q.points i.succ
  have hxy : x < y := Q.increasing (Fin.castSucc_lt_succ (i := i))
  have hx : l ≤ x := by
    rw [← Q.first]
    exact Q.increasing.monotone (Fin.zero_le _)
  have hy : y ≤ r := by
    rw [← Q.last]
    exact Q.increasing.monotone (Fin.le_last _)
  obtain ⟨j, hj⟩ := tagged_half_open_cover P
    (show y ∈ Ioc a b from ⟨hal.trans_lt (hx.trans_lt hxy), hy.trans hrb⟩)
  have hjx : P.points j.castSucc ≤ x := by
    by_contra! h
    have hnode : P.points j.castSucc ∈ pieceNodes P l r :=
      (mem_pieceNodes P).2 (Or.inr (Or.inr ⟨⟨_, rfl⟩, hx.trans_lt h, hj.1.trans_le hy⟩))
    have hrange : P.points j.castSucc ∈ range Q.points := by
      rw [range_pieceGrid]
      exact hnode
    exact no_node_between Q i ⟨h, hj.1⟩ hrange
  exact (sub_le_sub hj.2 hjx).trans (Finset.le_sup' (f := P.width) (Finset.mem_univ j))

theorem tagged_mesh_nonneg {a b : ℝ} (P : Ch09.TaggedPartition a b) :
    0 ≤ P.mesh :=
  (sub_nonneg.mpr (P.increasing (Fin.castSucc_lt_succ
    (i := (0 : Fin (P.n+1))))).le).trans
    (Finset.le_sup' (f := P.width) (Finset.mem_univ 0))

theorem pieceGrid_mesh_tendsto {X : Type*} {a b l r : ℝ} (F : Filter X)
    (P : X → Ch09.TaggedPartition a b) (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b)
    (h : Tendsto (fun x => (P x).mesh) F (𝓝 0)) :
    Tendsto (fun x => (pieceGrid (P x) hlr).mesh) F (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun x => tagged_mesh_nonneg (pieceGrid (P x) hlr))
    (fun x => pieceGrid_mesh_le (P x) hal hlr hrb)

theorem pieceGrid_length_tendsto {X V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {a b l r : ℝ} (F : Filter X) (P : X → Ch09.TaggedPartition a b)
    (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b)
    (h : Tendsto (fun x => (P x).mesh) F (𝓝 0))
    (γ v : ℝ → V) (hv : ContinuousOn v (Icc l r))
    (hc : ContinuousOn γ (Icc l r))
    (hd : ∀ t ∈ Ioo l r, HasDerivAt γ (v t) t) :
    Tendsto (fun x => polygonalSum γ (pieceGrid (P x) hlr)) F
      (𝓝 (∫ t in l..r, ‖v t‖)) := by
  have hs := (curve_length_mesh_iff γ _).mp (length_of_continuous_velocity γ v hlr hv hc hd)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hs ε hε
  filter_upwards [((pieceGrid_mesh_tendsto F P hal hlr hrb h).eventually_lt_const hδ)] with x hx
  simpa only [Real.dist_eq] using hbound (pieceGrid (P x) hlr) hx

/-- A cell of the restricted grid is the intersection with one original cell. -/
theorem pieceGrid_cell_endpoints {a b l r : ℝ} (P : Ch09.TaggedPartition a b)
    (hlr : l < r) (i : Fin ((pieceGrid P hlr).n + 1)) (j : Fin (P.n + 1))
    (hj : (pieceGrid P hlr).points i.succ ∈ Ioc (P.points j.castSucc) (P.points j.succ)) :
    (pieceGrid P hlr).points i.castSucc = max l (P.points j.castSucc) ∧
      (pieceGrid P hlr).points i.succ = min r (P.points j.succ) := by
  let Q := pieceGrid P hlr
  let x := Q.points i.castSucc
  let y := Q.points i.succ
  change y ∈ Ioc (P.points j.castSucc) (P.points j.succ) at hj
  have hxy : x < y := Q.increasing (Fin.castSucc_lt_succ (i := i))
  have hx : l ≤ x := by
    rw [← Q.first]
    exact Q.increasing.monotone (Fin.zero_le _)
  have hy : y ≤ r := by
    rw [← Q.last]
    exact Q.increasing.monotone (Fin.le_last _)
  have hrange {z : ℝ} (hz : z ∈ pieceNodes P l r) : z ∈ range Q.points := by
    rw [range_pieceGrid]
    exact hz
  have hnode (k : Fin (Q.n+2)) : Q.points k ∈ pieceNodes P l r := by
    have hk : Q.points k ∈ range Q.points := ⟨k,rfl⟩
    rwa [range_pieceGrid] at hk
  have hjx : P.points j.castSucc ≤ x := by
    by_contra! h
    exact no_node_between Q i ⟨h,hj.1⟩ (hrange ((mem_pieceNodes P).2
      (Or.inr (Or.inr ⟨⟨_,rfl⟩, hx.trans_lt h, hj.1.trans_le hy⟩))))
  constructor
  · change x = _
    refine le_antisymm ?_ (max_le hx hjx)
    by_contra! h
    rcases (mem_pieceNodes P).1 (hnode i.castSucc) with he | he | ⟨hs,_⟩
    · exact (not_lt_of_ge (le_max_left _ _) (he ▸ h))
    · exact not_lt_of_ge hy (he ▸ hxy)
    · exact no_node_between P j ⟨(le_max_right _ _).trans_lt h,hxy.trans_le hj.2⟩ hs
  · change y = _
    refine le_antisymm (le_min hy hj.2) ?_
    by_contra! h
    rcases (mem_pieceNodes P).1 (hnode i.succ) with he | he | ⟨hs,_⟩
    · exact (not_lt_of_ge hx (he ▸ hxy))
    · exact not_lt_of_ge (min_le_left _ _) (he ▸ h)
    · exact no_node_between P j ⟨hj.1,h.trans_le (min_le_right _ _)⟩ hs

/-- Positive overlaps with original cells index the cells of the restricted grid. -/
theorem pieceGrid_overlap_bijective {a b l r : ℝ} (P : Ch09.TaggedPartition a b)
    (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b) :
    ∃ e : Fin ((pieceGrid P hlr).n + 1) ≃
        {j : Fin (P.n + 1) // max l (P.points j.castSucc) < min r (P.points j.succ)},
      ∀ i, (pieceGrid P hlr).points i.castSucc = max l (P.points (e i).val.castSucc) ∧
        (pieceGrid P hlr).points i.succ = min r (P.points (e i).val.succ) := by
  classical
  let Q := pieceGrid P hlr
  have hcover (i : Fin (Q.n+1)) :
      ∃ j : Fin (P.n+1), Q.points i.succ ∈ Ioc (P.points j.castSucc) (P.points j.succ) := by
    apply tagged_half_open_cover P
    constructor
    · rw [← Q.first] at hal
      exact hal.trans_lt (Q.increasing (by simp))
    · rw [← Q.last] at hrb
      exact (Q.increasing.monotone (Fin.le_last _)).trans hrb
  let pick (i : Fin (Q.n+1)) := Classical.choose (hcover i)
  have hpick i := Classical.choose_spec (hcover i)
  have hend i := pieceGrid_cell_endpoints P hlr i (pick i) (hpick i)
  let f (i : Fin (Q.n+1)) :
      {j : Fin (P.n+1) // max l (P.points j.castSucc) < min r (P.points j.succ)} :=
    ⟨pick i, by
      rw [← (hend i).1, ← (hend i).2]
      exact Q.increasing (Fin.castSucc_lt_succ (i := i))⟩
  have hinj : Function.Injective f := by
    intro i k h
    have hp : pick i = pick k := congrArg Subtype.val h
    have he : Q.points i.succ = Q.points k.succ := by
      rw [(hend i).2, (hend k).2, hp]
    exact Fin.succ_injective _ (Q.increasing.injective he)
  have hsurj : Function.Surjective f := by
    intro j
    let y := min r (P.points j.val.succ)
    have hyl : l < y := (le_max_left _ _).trans_lt j.property
    have hyr : y ≤ r := min_le_left _ _
    have hyP : y ∈ Ioc (P.points j.val.castSucc) (P.points j.val.succ) :=
      ⟨(le_max_right _ _).trans_lt j.property, min_le_right _ _⟩
    have hyn : y ∈ pieceNodes P l r := by
      rcases eq_or_lt_of_le hyr with h | h
      · exact (mem_pieceNodes P).2 (Or.inr (Or.inl h))
      · have he : P.points j.val.succ = y := (min_eq_right (by
          by_contra! hn
          simp [y, min_eq_left hn.le] at h)).symm
        exact (mem_pieceNodes P).2 (Or.inr (Or.inr ⟨⟨_,he⟩,hyl,h⟩))
    have hyrange : y ∈ range Q.points := by
      rw [range_pieceGrid]
      exact hyn
    obtain ⟨i, hi⟩ := tagged_half_open_cover Q (show y ∈ Ioc l r from ⟨hyl,hyr⟩)
    have hey : Q.points i.succ = y := by
      refine le_antisymm ?_ hi.2
      by_contra! hn
      exact no_node_between Q i ⟨hi.1,hn⟩ hyrange
    refine ⟨i, Subtype.ext ?_⟩
    exact tagged_half_open_unique P (hpick i) (hey.symm ▸ hyP)
  exact ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩, hend⟩

/-- Summing over a piece is summing over its positive intersections with the original cells. -/
theorem sum_pieceGrid_cells {a b l r : ℝ} (P : Ch09.TaggedPartition a b)
    (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b) (weight : ℝ → ℝ → ℝ) :
    let Q := pieceGrid P hlr
    (∑ i : Fin (Q.n+1), weight (Q.points i.castSucc) (Q.points i.succ)) =
      ∑ j : Fin (P.n+1),
        if max l (P.points j.castSucc) < min r (P.points j.succ) then
          weight (max l (P.points j.castSucc)) (min r (P.points j.succ)) else 0 := by
  classical
  dsimp only
  obtain ⟨e, he⟩ := pieceGrid_overlap_bijective P hal hlr hrb
  calc
    _ = ∑ j : {j : Fin (P.n+1) // max l (P.points j.castSucc) < min r (P.points j.succ)},
        weight (max l (P.points j.val.castSucc)) (min r (P.points j.val.succ)) := by
      apply Fintype.sum_equiv e
      intro i
      rw [(he i).1, (he i).2]
    _ = _ := by
      rw [← Finset.sum_filter]
      symm
      exact Finset.sum_subtype _ (by simp) _

theorem tagged_cell_pos {a b : ℝ} (P : Ch09.TaggedPartition a b) (i : Fin (P.n+1)) :
    P.points i.castSucc < P.points i.succ :=
  P.increasing (Fin.castSucc_lt_succ (i := i))

/-- The same refined sum, grouped either by smooth piece or by original cell. -/
theorem regroup_pieceGrid_sums {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) {a b : ℝ} (P B : Ch09.TaggedPartition a b) :
    (∑ i : Fin (B.n+1), polygonalSum γ (pieceGrid P (tagged_cell_pos B i))) =
      ∑ j : Fin (P.n+1), polygonalSum γ (pieceGrid B (tagged_cell_pos P j)) := by
  let weight (l r : ℝ) := ‖γ r - γ l‖
  have hs (U W : Ch09.TaggedPartition a b) (i : Fin (W.n+1)) :
      polygonalSum γ (pieceGrid U (tagged_cell_pos W i)) =
        ∑ j : Fin (U.n+1),
          if max (W.points i.castSucc) (U.points j.castSucc) <
              min (W.points i.succ) (U.points j.succ) then
            weight (max (W.points i.castSucc) (U.points j.castSucc))
              (min (W.points i.succ) (U.points j.succ)) else 0 :=
    sum_pieceGrid_cells U
      ((W.subinterval_subset i (left_mem_Icc.mpr (tagged_cell_pos W i).le)).1)
      (tagged_cell_pos W i)
      ((W.subinterval_subset i (right_mem_Icc.mpr (tagged_cell_pos W i).le)).2) weight
  simp only [hs]
  rw [Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext i
  rw [max_comm (B.points i.castSucc), min_comm (B.points i.succ)]

private noncomputable def edgeSum (w : ℝ → ℝ → ℝ) : ℝ → List ℝ → ℝ → ℝ
  | l, [], r => w l r
  | l, t :: ts, r => w l t + edgeSum w t ts r

private theorem edgeSum_ofFn (w : ℝ → ℝ → ℝ) (n : ℕ) (p : Fin (n+2) → ℝ) :
    edgeSum w (p 0) (List.ofFn (fun i : Fin n => p i.succ.castSucc))
        (p (Fin.last (n+1))) =
      ∑ i : Fin (n+1), w (p i.castSucc) (p i.succ) := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    change w (p 0) (p 1) + _ = w (p 0) (p 1) + _
    congr 1
    exact ih (fun i => p i.succ)

private theorem chordLength_subdivisionFromList {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) {l r : ℝ} (h : l ≤ r) (xs : List ℝ)
    (hs : xs.Pairwise (· ≤ ·)) (hx : ∀ x ∈ xs, x ∈ Icc l r) :
    chordLength γ (subdivisionFromList h xs hs hx) =
      edgeSum (fun x y => ‖γ y - γ x‖) l xs r := by
  induction xs generalizing l with
  | nil => rfl
  | cons t ts ih =>
    simp only [subdivisionFromList, chordLength, edgeSum]
    exact congrArg (‖γ t - γ l‖ + ·) (ih _ hs.tail _)

theorem polygonalSum_pieceGrid_eq_subdivideAt {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) {a b l r : ℝ} (B : Ch09.TaggedPartition a b) (hlr : l < r) :
    polygonalSum γ (pieceGrid B hlr) =
      chordLength γ (subdivideAt hlr.le (Finset.univ.image B.points)) := by
  let Q := pieceGrid B hlr
  let q (i : Fin Q.n) := Q.points i.succ.castSucc
  let s := (Finset.univ.image B.points).filter (fun t => t ∈ Ioo l r)
  have hq : (List.ofFn q).SortedLT :=
    (List.pairwise_ofFn.mpr (fun i j hij => Q.increasing (Nat.succ_lt_succ hij))).sortedLT
  have hlist : List.ofFn q = s.sort := by
    apply hq.eq_of_mem_iff s.sortedLT_sort
    intro x
    rw [List.mem_ofFn', Finset.mem_sort]
    constructor
    · rintro ⟨i,rfl⟩
      have hm : q i ∈ range Q.points := ⟨i.succ.castSucc,rfl⟩
      rw [range_pieceGrid] at hm
      have hleft : l < q i := by
        rw [← Q.first]
        apply Q.increasing
        exact Nat.succ_pos _
      have hright : q i < r := by
        rw [← Q.last]
        apply Q.increasing
        exact Nat.succ_lt_succ i.isLt
      rcases (mem_pieceNodes B).1 hm with h | h | ⟨⟨j,hj⟩,hj'⟩
      · exact (ne_of_gt hleft h).elim
      · exact (ne_of_lt hright h).elim
      · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩,hj'⟩
    · intro hx
      obtain ⟨hj,hint⟩ := Finset.mem_filter.mp hx
      obtain ⟨j,_,he⟩ := Finset.mem_image.mp hj
      have hm : x ∈ range Q.points := by
        rw [range_pieceGrid]
        exact (mem_pieceNodes B).2 (Or.inr (Or.inr ⟨⟨j,he⟩,hint⟩))
      obtain ⟨i,hi⟩ := hm
      have h0 : i.val ≠ 0 := by
        intro h
        have hi0 : i = 0 := Fin.ext h
        exact ne_of_gt hint.1 ((hi0 ▸ hi).symm.trans Q.first)
      have hn : i.val ≠ Q.n+1 := by
        intro h
        have hin : i = Fin.last (Q.n+1) := Fin.ext h
        exact ne_of_lt hint.2 ((hin ▸ hi).symm.trans Q.last)
      refine ⟨⟨i.val-1,by omega⟩,?_⟩
      change Q.points _ = x
      exact (congrArg Q.points (Fin.ext (by change i.val - 1 + 1 = i.val; omega))).trans hi
  have hsum := edgeSum_ofFn (fun x y => ‖γ y - γ x‖) Q.n Q.points
  change _ = polygonalSum γ Q at hsum
  change polygonalSum γ Q = chordLength γ (subdivideAt hlr.le (Finset.univ.image B.points))
  rw [← hsum, Q.first, Q.last, hlist]
  unfold subdivideAt
  rw [chordLength_subdivisionFromList]

theorem length_of_piecewise_continuous_velocity_of_chord_bound {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {a b K : ℝ} (B : Ch09.TaggedPartition a b) (γ : ℝ → V)
    (v : Fin (B.n+1) → ℝ → V)
    (hv : ∀ i, ContinuousOn (v i) (Icc (B.points i.castSucc) (B.points i.succ)))
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ i, ∀ t ∈ Ioo (B.points i.castSucc) (B.points i.succ), HasDerivAt γ (v i t) t)
    (hK : 0 ≤ K)
    (hL : ∀ x y, a ≤ x → x ≤ y → y ≤ b → ‖γ y - γ x‖ ≤ K*(y-x)) :
    HasPolygonalLength (Ch09.TaggedPartition.mesh (a := a) (b := b)) (polygonalSum γ)
      (∑ i, ∫ t in B.points i.castSucc..B.points i.succ, ‖v i t‖) := by
  let mesh := Ch09.TaggedPartition.mesh (a := a) (b := b)
  let F := Filter.comap mesh (𝓝 0)
  let parts (i : Fin (B.n+1)) (P : Ch09.TaggedPartition a b) :=
    polygonalSum γ (pieceGrid P (tagged_cell_pos B i))
  have hm : Tendsto mesh F (𝓝 0) := Filter.tendsto_comap
  have hpiece (i : Fin (B.n+1)) :
      Tendsto (parts i) F (𝓝 (∫ t in B.points i.castSucc..B.points i.succ, ‖v i t‖)) := by
    have hs := B.subinterval_subset i
    exact pieceGrid_length_tendsto F id
      (hs (left_mem_Icc.mpr (tagged_cell_pos B i).le)).1
      (tagged_cell_pos B i) (hs (right_mem_Icc.mpr (tagged_cell_pos B i).le)).2
      hm γ (v i) (hv i) (hc.mono hs) (hd i)
  let points := Finset.univ.image B.points
  have herror (P : Ch09.TaggedPartition a b) :
      0 ≤ (∑ i, parts i P) - polygonalSum γ P ∧
        (∑ i, parts i P) - polygonalSum γ P ≤ (points.card : ℝ)*K*mesh P := by
    have hsum : (∑ i, parts i P) =
        ∑ j : Fin (P.n+1), chordLength γ (subdivideAt (tagged_cell_pos P j).le points) := by
      change (∑ i, polygonalSum γ (pieceGrid P (tagged_cell_pos B i))) = _
      rw [regroup_pieceGrid_sums]
      exact Finset.sum_congr rfl (fun j _ => polygonalSum_pieceGrid_eq_subdivideAt γ B _)
    rw [hsum]
    exact actual_breakpoint_error γ P points hK hL
  have hlim := finite_piece_length_limit F Finset.univ parts
    (fun i => ∫ t in B.points i.castSucc..B.points i.succ, ‖v i t‖)
    (polygonalSum γ) mesh ((points.card : ℝ)*K) hm (fun i _ => hpiece i)
    (by simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using herror)
  apply (curve_length_mesh_iff γ _).mpr
  intro ε hε
  have he := Metric.tendsto_nhds.mp hlim ε hε
  change (∀ᶠ P in Filter.comap mesh (𝓝 0), _) at he
  rw [Filter.eventually_comap, Metric.eventually_nhds_iff] at he
  obtain ⟨δ,hδ,hδ'⟩ := he
  refine ⟨δ,hδ,fun P hP => ?_⟩
  have hdist : dist (mesh P) 0 < δ := by
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (tagged_mesh_nonneg P)]
  simpa only [Real.dist_eq] using hδ' hdist P rfl

private theorem chord_bound_of_chain {V : Type*} [NormedAddCommGroup V]
    (γ : ℝ → V) (K : ℝ) (n : ℕ) (p : Fin (n+2) → ℝ)
    (h : ∀ i : Fin (n+1), ‖γ (p i.succ) - γ (p i.castSucc)‖ ≤
      K * (p i.succ - p i.castSucc)) :
    ‖γ (p (Fin.last (n+1))) - γ (p 0)‖ ≤ K * (p (Fin.last (n+1)) - p 0) := by
  induction n with
  | zero => exact h 0
  | succ n ih =>
    let z := p (Fin.last (n+2))
    have h₁ : ‖γ (p 1) - γ (p 0)‖ ≤ K * (p 1 - p 0) := h 0
    have h₂ : ‖γ z - γ (p 1)‖ ≤ K * (z - p 1) :=
      ih (fun i => p i.succ) (fun i => h i.succ)
    calc
      _ ≤ ‖γ z - γ (p 1)‖ + ‖γ (p 1) - γ (p 0)‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (γ z - γ (p 1)) (γ (p 1) - γ (p 0))
      _ ≤ _ := by
        change _ ≤ K * (z - p 0)
        linarith

/-- The folded polygonal length converges to the sum of the speed integrals. -/
theorem length_of_piecewise_continuous_velocity {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {a b : ℝ} (B : Ch09.TaggedPartition a b) (γ : ℝ → V)
    (v : Fin (B.n+1) → ℝ → V)
    (hv : ∀ i, ContinuousOn (v i) (Icc (B.points i.castSucc) (B.points i.succ)))
    (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ i, ∀ t ∈ Ioo (B.points i.castSucc) (B.points i.succ), HasDerivAt γ (v i t) t) :
    HasPolygonalLength (Ch09.TaggedPartition.mesh (a := a) (b := b)) (polygonalSum γ)
      (∑ i, ∫ t in B.points i.castSucc..B.points i.succ, ‖v i t‖) := by
  classical
  have hb (i : Fin (B.n+1)) :
      ∃ M : ℝ, ∀ t ∈ Icc (B.points i.castSucc) (B.points i.succ), ‖v i t‖ ≤ M := by
    obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image (hv i).norm
    exact ⟨M,fun t ht => hM ⟨t,ht,rfl⟩⟩
  choose M hM using hb
  let K := Finset.univ.sup' Finset.univ_nonempty (fun i => max 0 (M i))
  have hKi (i : Fin (B.n+1)) : max 0 (M i) ≤ K :=
    Finset.le_sup' (f := fun i => max 0 (M i)) (Finset.mem_univ i)
  apply length_of_piecewise_continuous_velocity_of_chord_bound B γ v hv hc hd
    ((le_max_left 0 (M 0)).trans (hKi 0))
  intro x y hax hxy hyb
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  let Q := pieceGrid B hxy
  have hadj (i : Fin (Q.n+1)) :
      ‖γ (Q.points i.succ) - γ (Q.points i.castSucc)‖ ≤ K * Q.width i := by
    obtain ⟨e, he⟩ := pieceGrid_overlap_bijective B hax hxy hyb
    let j := (e i).val
    have hsub : Icc (Q.points i.castSucc) (Q.points i.succ) ⊆
        Icc (B.points j.castSucc) (B.points j.succ) := by
      apply Icc_subset_Icc
      · rw [(he i).1]
        exact le_max_right _ _
      · rw [(he i).2]
        exact min_le_right _ _
    apply chord_bound_on_piece γ (v j) (tagged_cell_pos Q i).le
      (hc.mono (hsub.trans (B.subinterval_subset j))) ((hv j).mono hsub)
    · intro t ht
      have hleft := (hsub (left_mem_Icc.mpr (tagged_cell_pos Q i).le)).1
      have hright := (hsub (right_mem_Icc.mpr (tagged_cell_pos Q i).le)).2
      exact hd j t ⟨hleft.trans_lt ht.1, ht.2.trans_le hright⟩
    · intro t ht
      exact (hM j t (hsub ht)).trans ((le_max_right _ _).trans (hKi j))
  have hchain := chord_bound_of_chain γ K Q.n Q.points hadj
  rwa [Q.first,Q.last] at hchain

end Ch13
