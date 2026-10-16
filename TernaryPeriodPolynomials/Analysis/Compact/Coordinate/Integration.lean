module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations
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
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Order.Monotone.Extension
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

/-! Genuine coordinate integration by parts for smooth compactly supported fields. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A compactly supported C¹ scalar function has zero integrated directional derivative. -/
theorem integral_fderiv_eq_zero {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (v : E) : ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf one_ne_zero
  have h := (LipschitzWith.const (1 : ℝ)).integral_lineDeriv_mul_eq (μ := μ) hC hc (-v)
  simp_rw [(hf.differentiable one_ne_zero).differentiableAt.lineDeriv_eq_fderiv] at h
  simpa [lineDeriv] using h.symm

/-- Only the first factor must have compact support; the second may be any C¹ function. -/
theorem integral_fderiv_mul {f g : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport f) (v : E) :
    ∫ x, fderiv ℝ f x v * g x ∂μ = -(∫ x, f x * fderiv ℝ g x v ∂μ) := by
  have hfg := integral_fderiv_eq_zero (μ := μ) (hf.mul hg) hc.mul_right v
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hi1 : Integrable (fun x => fderiv ℝ f x v * g x) μ :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_right
  have hi2 : Integrable (fun x => f x * fderiv ℝ g x v) μ :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport hc.mul_right
  have heq : (fun x => fderiv ℝ (fun y => f y * g y) x v) =
      (fun x => fderiv ℝ f x v * g x + f x * fderiv ℝ g x v) := by
    funext x
    change (fderiv ℝ (f * g) x) v = _
    rw [fderiv_mul (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [heq, integral_add hi1 hi2] at hfg
  exact eq_neg_of_add_eq_zero_left hfg

end TernaryPoly.CompactCoordinateIntegration
