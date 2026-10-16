module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Cutoff.Gradient

@[expose] public section


/-! A scope-stable name for the actual dual Riemannian differential norm. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open scoped ContDiff Manifold

open scoped Bundle SymmetricSpaceRiemannian in
/-- The literal operator norm of the actual quotient scalar differential. -/
def scalarSlope (χ : OrbitSpace → ℝ) (q : OrbitSpace) : ℝ := ‖scalarDifferential χ q‖

open scoped Bundle SymmetricSpaceRiemannian in
theorem scalarSlope_nonneg (χ : OrbitSpace → ℝ) (q : OrbitSpace) : 0 ≤ scalarSlope χ q :=
  ContinuousLinearMap.opNorm_nonneg _

theorem liftScalar_derivative_slope_bound (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) {B : ℝ}
    (hb : ∀ q, scalarSlope χ q ≤ B) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) :
    |fderiv ℝ (SmoothDeRhamGluing.liftScalar χ) x v| ≤
      B * Real.sqrt (SymmetricSpaceTraceMetric.coordinatePair x v v) :=
  liftScalar_derivative_metric_bound χ hχ hb x hx v

theorem cutoff_scalarSlope_bound (c : BoundedCutoffSequence) (j : ℕ) (q : OrbitSpace) :
    scalarSlope (c.toFun j) q ≤ c.bound / ((j : ℝ) + 1) := c.differential_bound j q

end TernaryPoly.PolynomialFormConnection
