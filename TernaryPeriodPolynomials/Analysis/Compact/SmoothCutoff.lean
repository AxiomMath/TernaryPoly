module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Data.String.Defs
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.GroupTheory.QuotientGroup.ModEq
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Smooth compact cutoffs equal to one near a prescribed compact subset of an open set. -/
noncomputable section
namespace TernaryPoly.CompactSmoothCutoff
open Set Filter
open scoped ContDiff Topology Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The support stays inside the genuine open chart while equality to one holds on a neighborhood. -/
theorem exists_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      ∀ x ∈ K, φ =ᶠ[𝓝 x] 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter Metric.isOpen_ball).mem_nhdsSet.mpr (subset_inter hKU hR))
  have hVc : IsCompact (closure V) :=
    (isCompact_closedBall (0 : E) R).of_isClosed_subset isClosed_closure
      (hVU.trans (inter_subset_right.trans Metric.ball_subset_closedBall))
  obtain ⟨W, hW, hKW, hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨φ, hφ, _, hs, h1⟩ := exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, E) (n := ⊤) hV isClosed_closure hWV
  refine ⟨φ, contMDiff_iff_contDiff.mp hφ, ?_, ?_, ?_⟩
  · change IsCompact (closure (Function.support φ))
    rw [hs]
    exact hVc
  · change closure (Function.support φ) ⊆ U
    rw [hs]
    exact hVU.trans inter_subset_left
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (h1 y).mp (subset_closure hy)

end TernaryPoly.CompactSmoothCutoff
