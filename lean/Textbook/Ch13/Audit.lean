import Textbook.Ch09.Tagged
import Textbook.Ch13.MultipleIntegrals

namespace Ch13

open MeasureTheory Set
open scoped BigOperators Interval ENNReal

/-- Each Cartesian cell has its own tag, independent of the tags in other cells. -/
structure RectPartition (a b c d : ℝ) where
  x : Ch09.TaggedPartition a b
  y : Ch09.TaggedPartition c d
  tag : Fin (x.n + 1) → Fin (y.n + 1) → ℝ × ℝ
  tag_x : ∀ i j, (tag i j).1 ∈ Icc (x.points i.castSucc) (x.points i.succ)
  tag_y : ∀ i j, (tag i j).2 ∈ Icc (y.points j.castSucc) (y.points j.succ)

noncomputable def rectangleMesh {a b c d : ℝ} (P : RectPartition a b c d) : ℝ :=
  max P.x.mesh P.y.mesh

noncomputable def rectangleSum {a b c d : ℝ}
    (f : ℝ × ℝ → ℝ) (P : RectPartition a b c d) : ℝ :=
  ∑ i, ∑ j, f (P.tag i j) * (P.x.width i * P.y.width j)

def HasRectangleIntegral (f : ℝ × ℝ → ℝ) (a b c d I : ℝ) : Prop :=
  Ch09.HasMeshIntegral (rectangleMesh (a := a) (b := b) (c := c) (d := d))
    (rectangleSum f) I

theorem rectangle_mesh_iff (f : ℝ × ℝ → ℝ) (a b c d I : ℝ) :
    HasRectangleIntegral f a b c d I ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P : RectPartition a b c d,
        rectangleMesh P < δ → |rectangleSum f P - I| < ε := by
  exact Ch09.mesh_integral_iff _ _ _

theorem rectangle_arbitrarily_fine {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (δ : ℝ) (hδ : 0 < δ) : ∃ P : RectPartition a b c d, rectangleMesh P < δ := by
  obtain ⟨X, hx⟩ := Ch09.arbitrarily_fine hab δ hδ
  obtain ⟨Y, hy⟩ := Ch09.arbitrarily_fine hcd δ hδ
  exact ⟨⟨X, Y, fun i j => (X.tag i, Y.tag j), fun i _ => X.tag_mem i,
    fun _ j => Y.tag_mem j⟩, max_lt hx hy⟩

theorem rectangle_filter_proper {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Ch02.IsProper (Ch09.fineFilter (rectangleMesh (a := a) (b := b) (c := c) (d := d))) :=
  Ch09.fineFilter_proper _ (rectangle_arbitrarily_fine hab hcd)

def HasRegionIntegral (a b c d : ℝ) (D : Set (ℝ × ℝ))
    (f : ℝ × ℝ → ℝ) (I : ℝ) : Prop :=
  D ⊆ Icc a b ×ˢ Icc c d ∧ HasRectangleIntegral (D.indicator f) a b c d I

theorem region_fubini (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) (f : ℝ × ℝ → ℝ)
    (hf : IntegrableOn f D (volume.prod volume)) :
    (∫ z in D, f z ∂volume.prod volume) =
      (∫ x : ℝ, ∫ y : ℝ, D.indicator f (x,y)) ∧
    (∫ z in D, f z ∂volume.prod volume) =
      (∫ y : ℝ, ∫ x : ℝ, D.indicator f (x,y)) := by
  have hi := (integrable_indicator_iff hD).2 hf
  rw [← integral_indicator hD]
  exact ⟨integral_prod _ hi, (integral_prod _ hi).trans
    (swap_integrals (fun x y => D.indicator f (x,y)) hi)⟩

theorem nonnegative_tonelli (f : ℝ × ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ z, f z ∂volume.prod volume) = (∫⁻ x : ℝ, ∫⁻ y : ℝ, f (x,y)) ∧
    (∫⁻ z, f z ∂volume.prod volume) = (∫⁻ y : ℝ, ∫⁻ x : ℝ, f (x,y)) := by
  exact ⟨lintegral_prod _ hf.aemeasurable, lintegral_prod_symm _ hf.aemeasurable⟩

theorem vector_interval_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ t in a..b, v t‖ ≤ ∫ t in a..b, ‖v t‖ := by
  exact intervalIntegral.norm_integral_le_integral_norm hab

def HasPolygonalLength {P : Type*} (mesh polygonalSum : P → ℝ) (L : ℝ) : Prop :=
  Ch09.HasMeshIntegral mesh polygonalSum L

theorem polygonal_length_iff {P : Type*} (mesh polygonalSum : P → ℝ) (L : ℝ) :
    HasPolygonalLength mesh polygonalSum L ↔
      ∀ ε > 0, ∃ δ > 0, ∀ p, mesh p < δ → |polygonalSum p - L| < ε := by
  exact Ch09.mesh_integral_iff mesh polygonalSum L

noncomputable def polygonalSum {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (γ : ℝ → E) (P : Ch09.TaggedPartition a b) : ℝ :=
  ∑ i : Fin (P.n + 1), ‖γ (P.points i.succ) - γ (P.points i.castSucc)‖

theorem curve_length_mesh_iff {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    (γ : ℝ → E) (L : ℝ) :
    HasPolygonalLength (P := Ch09.TaggedPartition a b)
      Ch09.TaggedPartition.mesh (polygonalSum γ) L ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P : Ch09.TaggedPartition a b,
        P.mesh < δ → |polygonalSum γ P - L| < ε := by
  exact polygonal_length_iff _ _ _

structure BoxPartition (a b c d e g : ℝ) where
  xy : RectPartition a b c d
  z : Ch09.TaggedPartition e g
  tag : Fin (xy.x.n + 1) → Fin (xy.y.n + 1) → Fin (z.n + 1) → ℝ × ℝ × ℝ
  tag_x : ∀ i j k, (tag i j k).1 ∈ Icc (xy.x.points i.castSucc) (xy.x.points i.succ)
  tag_y : ∀ i j k, (tag i j k).2.1 ∈ Icc (xy.y.points j.castSucc) (xy.y.points j.succ)
  tag_z : ∀ i j k, (tag i j k).2.2 ∈ Icc (z.points k.castSucc) (z.points k.succ)

noncomputable def boxMesh {a b c d e g : ℝ} (P : BoxPartition a b c d e g) : ℝ :=
  max (rectangleMesh P.xy) P.z.mesh

noncomputable def boxSum {a b c d e g : ℝ}
    (f : ℝ × ℝ × ℝ → ℝ) (P : BoxPartition a b c d e g) : ℝ :=
  ∑ i, ∑ j, ∑ k, f (P.tag i j k) * (P.xy.x.width i * P.xy.y.width j * P.z.width k)

def HasBoxIntegral (a b c d e g : ℝ) (f : ℝ × ℝ × ℝ → ℝ) (I : ℝ) : Prop :=
  Ch09.HasMeshIntegral (boxMesh (a := a) (b := b) (c := c) (d := d) (e := e) (g := g))
    (boxSum f) I

theorem box_mesh_iff (a b c d e g : ℝ) (f : ℝ × ℝ × ℝ → ℝ) (I : ℝ) :
    HasBoxIntegral a b c d e g f I ↔
      ∀ ε > 0, ∃ δ > 0, ∀ P : BoxPartition a b c d e g,
        boxMesh P < δ → |boxSum f P - I| < ε := by
  exact Ch09.mesh_integral_iff _ _ _

theorem box_arbitrarily_fine {a b c d e g : ℝ} (hab : a < b) (hcd : c < d) (heg : e < g)
    (δ : ℝ) (hδ : 0 < δ) : ∃ P : BoxPartition a b c d e g, boxMesh P < δ := by
  obtain ⟨Q, hQ⟩ := rectangle_arbitrarily_fine hab hcd δ hδ
  obtain ⟨Z, hZ⟩ := Ch09.arbitrarily_fine heg δ hδ
  exact ⟨⟨Q, Z, fun i j k => ((Q.tag i j).1, (Q.tag i j).2, Z.tag k),
    fun i j _ => Q.tag_x i j, fun i j _ => Q.tag_y i j, fun _ _ k => Z.tag_mem k⟩,
    max_lt hQ hZ⟩

theorem change_variables {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    (D : Set E) (Φ : E → E) (J : E → E →L[ℝ] E) (f : E → ℝ)
    (hD : MeasurableSet D) (hJ : ∀ x ∈ D, HasFDerivWithinAt Φ (J x) D x)
    (hΦ : InjOn Φ D) (hf : IntegrableOn f (Φ '' D)) :
    IntegrableOn (fun x => |(J x).det| * f (Φ x)) D ∧
    (∫ x in Φ '' D, f x) = ∫ x in D, |(J x).det| * f (Φ x) := by
  exact ⟨(integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hJ hΦ f).1 hf,
    integral_image_eq_integral_abs_det_fderiv_smul volume hD hJ hΦ f⟩

end Ch13
