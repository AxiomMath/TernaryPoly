module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
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
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Local finiteness of a density measure at points where the density is continuous. -/
namespace TernaryPoly.ContinuousDensityLocallyFinite
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsLocallyFiniteMeasure μ]

/-- Continuity at just one point suffices for local finiteness at that point. -/
theorem finiteAt_withDensity {f : X → ℝ} {x : X} (hf : ContinuousAt f x) :
    (μ.withDensity (fun y => ENNReal.ofReal (f y))).FiniteAtFilter (𝓝 x) := by
  have hh : ContinuousAt (fun y => (f y).toNNReal) x :=
    continuous_real_toNNReal.continuousAt.comp hf
  obtain ⟨U, ⟨⟨hUx, hUo⟩, hUf⟩, hμU⟩ :=
    (μ.finiteAt_nhds x).exists_mem_basis ((nhds_basis_opens' x).restrict_subset
      (hh.tendsto.eventually_le_const (lt_add_one _)))
  refine ⟨U, hUx, ?_⟩
  rw [withDensity_apply _ hUo.measurableSet]
  exact setLIntegral_lt_top_of_bddAbove hμU.ne
    ⟨(f x).toNNReal + 1, forall_mem_image.mpr hUf⟩

end TernaryPoly.ContinuousDensityLocallyFinite
