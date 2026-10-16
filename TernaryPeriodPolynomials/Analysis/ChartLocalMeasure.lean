module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Local measures in genuine open charts, using their source embeddings. -/
noncomputable section
namespace TernaryPoly.ChartLocalMeasure

open MeasureTheory Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- An actual open chart is a measurable embedding on its source. -/
theorem chart_measurableEmbedding (e : OpenPartialHomeomorph X Y) :
    MeasurableEmbedding (fun x : e.source => e x) := by
  exact (MeasurableEmbedding.subtype_coe e.open_target.measurableSet).comp
    e.toHomeomorphSourceTarget.toMeasurableEquiv.measurableEmbedding

/-- Pull back on the chart source, then extend the measure by zero. -/
def localMeasure (e : OpenPartialHomeomorph X Y) (μ : Measure Y) : Measure X :=
  Measure.map (fun x : e.source => (x : X))
    (Measure.comap (fun x : e.source => e x) μ)

/-- This construction measures exactly the chart image of the part inside its source. -/
theorem localMeasure_apply (e : OpenPartialHomeomorph X Y) (μ : Measure Y) (s : Set X) :
    localMeasure e μ s = μ (e '' (s ∩ e.source)) := by
  unfold localMeasure
  rw [(MeasurableEmbedding.subtype_coe e.open_source.measurableSet).map_apply,
    (chart_measurableEmbedding e).comap_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨hx, x.property⟩, rfl⟩
  · rintro ⟨x, ⟨hs, hx⟩, rfl⟩
    exact ⟨⟨x, hx⟩, hs, rfl⟩

/-- A chart-local measure is supported on its actual open source. -/
theorem localMeasure_restrict_source (e : OpenPartialHomeomorph X Y) (μ : Measure Y) :
    (localMeasure e μ).restrict e.source = localMeasure e μ := by
  ext s hs
  rw [Measure.restrict_apply hs, localMeasure_apply, localMeasure_apply]
  simp only [inter_assoc, inter_self]

/-- Every measurable subset of the source has a measurable chart image. -/
theorem measurableSet_image (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hs : MeasurableSet s) (hsub : s ⊆ e.source) : MeasurableSet (e '' s) := by
  have h := (chart_measurableEmbedding e).measurableSet_image.mpr
    (measurable_subtype_coe hs)
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Exact overlap compatibility follows from preservation of the coordinate measure. -/
theorem localMeasure_compatible (e f : OpenPartialHomeomorph X Y) (μ : Measure Y)
    (hpres : ∀ (s : Set Y), MeasurableSet s → s ⊆ (e.symm.trans f).source →
      μ ((e.symm.trans f) '' s) = μ s) :
    (localMeasure e μ).restrict f.source = (localMeasure f μ).restrict e.source := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, localMeasure_apply, localMeasure_apply]
  let D := e '' ((s ∩ f.source) ∩ e.source)
  have hm : MeasurableSet D := measurableSet_image e
    ((hs.inter f.open_source.measurableSet).inter e.open_source.measurableSet) inter_subset_right
  have hD : D ⊆ (e.symm.trans f).source := by
    rintro _ ⟨x, hx, rfl⟩
    change e x ∈ e.target ∧ e.symm (e x) ∈ f.source
    exact ⟨e.map_source hx.2, by rw [e.left_inv hx.2]; exact hx.1.2⟩
  have hi : (e.symm.trans f) '' D = f '' ((s ∩ e.source) ∩ f.source) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩, ?_⟩
      change f x = f (e.symm (e x))
      rw [e.left_inv hx.2]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e x, ⟨x, ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩, rfl⟩, ?_⟩
      change f (e.symm (e x)) = f x
      rw [e.left_inv hx.1.2]
  have h := hpres D hm hD
  rw [hi] at h
  exact h.symm

end TernaryPoly.ChartLocalMeasure
