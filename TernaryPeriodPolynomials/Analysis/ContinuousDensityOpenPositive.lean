module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.OpenPos
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

/-! A locally positive continuous density gives positive mass to neighborhoods. -/
namespace TernaryPoly.ContinuousDensityOpenPositive
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [μ.IsOpenPosMeasure]

/-- Only pointwise continuity and positivity are needed; no global regularity is assumed. -/
theorem withDensity_pos {f : X → ℝ} {x : X} (hf : ContinuousAt f x) (hp : 0 < f x)
    {U : Set X} (hU : U ∈ 𝓝 x) : 0 < (μ.withDensity (fun y => ENNReal.ofReal (f y))) U := by
  let c := f x / 2
  have hc : 0 < c := half_pos hp
  have hbound : {y | c < f y} ∈ 𝓝 x := hf (lt_mem_nhds (half_lt_self hp))
  let V := interior (U ∩ {y | c < f y})
  have hxV : x ∈ V := mem_interior_iff_mem_nhds.mpr (inter_mem hU hbound)
  have hsub : V ⊆ U := interior_subset.trans inter_subset_left
  have hpos : 0 < μ V := isOpen_interior.measure_pos μ ⟨x, hxV⟩
  have hle : ENNReal.ofReal c * μ V ≤ (μ.withDensity (fun y => ENNReal.ofReal (f y))) V := by
    rw [withDensity_apply _ isOpen_interior.measurableSet]
    have h := lintegral_mono_ae (μ := μ.restrict V)
      (ae_restrict_of_forall_mem isOpen_interior.measurableSet (fun y (hy : y ∈ V) =>
        ENNReal.ofReal_le_ofReal (le_of_lt (interior_subset hy).2)))
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h
  exact ((ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) (ne_of_gt hpos)).trans_le hle).trans_le (measure_mono hsub)

end TernaryPoly.ContinuousDensityOpenPositive
