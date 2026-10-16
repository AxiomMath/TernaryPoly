module

public import TernaryPeriodPolynomials.Analysis.ScaledScalarKernelRegularity
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

@[expose] public section


/-! One genuine normalized compact smooth kernel, with its actual mass-preserving family. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory ScaledScalarKernel
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A fixed actual smooth bump with inner radius one and outer radius two. -/
def bump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Normalize using the actual Haar integral, then dilate with the actual Jacobian factor. -/
def kernel (c : ℝ) : E → ℝ := dilate c ((bump E).normed μ)

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem kernel_nonneg (c : ℝ) (hc : 0 ≤ c) (x : E) : 0 ≤ kernel E μ c x :=
  nonneg_dilate _ c hc (bump E).nonneg_normed x

theorem kernel_integral (c : ℝ) (hc : 0 < c) : ∫ x, kernel E μ c x ∂μ = 1 := by
  rw [kernel, integral_dilate μ c hc]
  exact (bump E).integral_normed

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem kernel_contDiff (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (kernel E μ c) :=
  contDiff_dilate _ c (bump E).contDiff_normed

theorem kernel_compact (c : ℝ) (hc : c ≠ 0) : HasCompactSupport (kernel E μ c) :=
  compact_dilate _ c hc (bump E).hasCompactSupport_normed

end TernaryPoly.CompactScalarMollifier
