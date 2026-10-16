module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
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
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Quantitative Euclidean smoothing by an actual normalized compact smooth kernel. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open MeasureTheory Measure ContinuousLinearMap
open scoped Convolution ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Convolution with a nonnegative normalized bump preserves the Lipschitz constant. -/
theorem lipschitzWith_normed_convolution (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hi (x : E) : Integrable (fun t => φ.normed μ t • f (x - t)) μ :=
    (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
      (lsmul ℝ ℝ) (φ.continuous_normed (μ := μ)) (hf.continuous.locallyIntegrable (μ := μ)) x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖(∫ t, φ.normed μ t • f (x - t) ∂μ) -
    (∫ t, φ.normed μ t • f (y - t) ∂μ)‖ ≤ (K : ℝ) * dist x y
  rw [← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ t, ‖φ.normed μ t • f (x - t) - φ.normed μ t • f (y - t)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, φ.normed μ t * ((K : ℝ) * dist x y) ∂μ := by
      apply integral_mono ((hi x).sub (hi y)).norm (φ.integrable_normed.mul_const _)
      intro t
      change ‖φ.normed μ t • f (x - t) - φ.normed μ t • f (y - t)‖ ≤ _
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [← dist_eq_norm, dist_sub_right] using hf.dist_le_mul (x - t) (y - t)
    _ = (K : ℝ) * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The actual convolution is smooth at every order. -/
theorem contDiff_normed_convolution (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ContDiff ℝ ∞ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed (hf.continuous.locallyIntegrable (μ := μ))

/-- The derivative bound follows from the proved Lipschitz bound. -/
theorem norm_fderiv_normed_convolution_le (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : E) :
    ‖fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ ≤ K :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_normed_convolution φ hf)

/-- Uniform approximation error is at most the Lipschitz constant times the kernel radius. -/
theorem dist_normed_convolution_le_mul_radius (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : E) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x) (f x) ≤ (K : ℝ) * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left hy.le K.coe_nonneg)

/-- Averaging preserves the closed unit interval. -/
theorem normed_convolution_mem_Icc (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfr : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : E) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x ∈ Set.Icc (0 : ℝ) 1 := by
  have hi : Integrable (fun t => φ.normed μ t * f (x - t)) μ :=
    (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
      (lsmul ℝ ℝ) (φ.continuous_normed (μ := μ)) (hf.continuous.locallyIntegrable (μ := μ)) x
  change 0 ≤ (∫ t, φ.normed μ t * f (x - t) ∂μ) ∧ (∫ t, φ.normed μ t * f (x - t) ∂μ) ≤ 1
  constructor
  · exact integral_nonneg (fun t => mul_nonneg (φ.nonneg_normed t) (hfr _).1)
  · rw [← φ.integral_normed (μ := μ)]
    apply integral_mono hi φ.integrable_normed
    intro t
    exact mul_le_of_le_one_right (φ.nonneg_normed t) (hfr _).2

/-- Arbitrarily accurate smooth Lipschitz approximation, preserving the original constant. -/
theorem exists_smooth_lipschitz_approx (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧
      (∀ x, dist (g x) (f x) < ε) ∧
      ((∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) := by
  let r := ε / ((K : ℝ) + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨φ.normed μ ⋆[lsmul ℝ ℝ, μ] f, contDiff_normed_convolution φ hf,
    lipschitzWith_normed_convolution φ hf, ?_, fun hfr x => normed_convolution_mem_Icc φ hf hfr x⟩
  intro x
  apply (dist_normed_convolution_le_mul_radius φ hf x).trans_lt
  change (K : ℝ) * r < ε
  have he : ((K : ℝ) + 1) * r = ε := by dsimp [r]; field_simp
  nlinarith

end TernaryPoly.PolynomialFormConnection
