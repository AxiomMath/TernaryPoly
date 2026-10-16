module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Actual mass-preserving dilations of scalar kernels and the invariant derivative moment. -/
noncomputable section
namespace TernaryPoly.ScaledScalarKernel
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dilation with the actual dimension-dependent Haar density. -/
def dilate (c : ℝ) (κ : E → ℝ) (x : E) : ℝ :=
  c ^ Module.finrank ℝ E * κ (c • x)

theorem integral_dilate (μ : Measure E) [μ.IsAddHaarMeasure]
    (c : ℝ) (hc : 0 < c) (κ : E → ℝ) :
    ∫ x, dilate c κ x ∂μ = ∫ x, κ x ∂μ := by
  unfold dilate
  rw [integral_const_mul, μ.integral_comp_smul_of_nonneg κ c (hR := hc.le)]
  simp only [smul_eq_mul]
  field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_comp_dilation (κ : E → ℝ) (c : ℝ) (x v : E)
    (hκ : DifferentiableAt ℝ κ (c • x)) :
    fderiv ℝ (fun y => κ (c • y)) x v = c * fderiv ℝ κ (c • x) v := by
  have h := hκ.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
  change HasFDerivAt (fun y => κ (c • y)) _ x at h
  rw [h.fderiv]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_dilate (κ : E → ℝ) (c : ℝ) (x v : E)
    (hκ : DifferentiableAt ℝ κ (c • x)) :
    fderiv ℝ (dilate c κ) x v = c ^ Module.finrank ℝ E * c * fderiv ℝ κ (c • x) v := by
  have h := (hκ.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)).const_mul
    (c ^ Module.finrank ℝ E)
  change HasFDerivAt (dilate c κ) _ x at h
  rw [h.fderiv]
  simp [mul_assoc]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The distance factor exactly cancels the derivative scaling in the commutator envelope. -/
theorem derivativeMoment_dilate (κ : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hκ : Differentiable ℝ κ) (v x : E) :
    ‖x‖ * ‖fderiv ℝ (dilate c κ) x v‖ =
      dilate c (fun z => ‖z‖ * ‖fderiv ℝ κ z v‖) x := by
  rw [fderiv_dilate κ c x v (hκ _)]
  simp only [dilate, norm_mul, Real.norm_of_nonneg hc.le,
    Real.norm_of_nonneg (pow_nonneg hc.le _), norm_smul]
  ring

/-- The true first-order commutator derivative moment is independent of the smoothing scale. -/
theorem integral_derivativeMoment_dilate (μ : Measure E) [μ.IsAddHaarMeasure]
    (κ : E → ℝ) (c : ℝ) (hc : 0 < c) (hκ : Differentiable ℝ κ) (v : E) :
    ∫ x, ‖x‖ * ‖fderiv ℝ (dilate c κ) x v‖ ∂μ =
      ∫ x, ‖x‖ * ‖fderiv ℝ κ x v‖ ∂μ := by
  simp_rw [derivativeMoment_dilate κ c hc hκ v]
  exact integral_dilate μ c hc _

end TernaryPoly.ScaledScalarKernel
