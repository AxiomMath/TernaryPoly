module

public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.OperatorLocality

@[expose] public section


/-! Germ-locality of the genuine exterior differential and its actual local adjoint. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration ContinuousAlternatingMap
open Filter
open scoped Topology

theorem localAdjoint_congr (n k : ℕ) {w z : Coordinates → FormValue n (k + 1)}
    {x : Coordinates} (h : w =ᶠ[𝓝 x] z) : localAdjoint n k w x = localAdjoint n k z x := by
  apply congrArg (coordinates n k).symm
  funext i
  apply weightedMatrixAdjoint_congr
  intro j
  filter_upwards [h] with y hy
  simp only [components, hy]

/-- Outside the closed support the actual exterior derivative is zero. -/
theorem extDeriv_eq_zero_of_notMem_tsupport (n k : ℕ) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hx : x ∉ tsupport w) : extDeriv w x = 0 := by
  change (alternatizeUncurryFinCLM ℝ Coordinates (PolynomialCoefficientMetric.Coefficients n)
    (n := k)) (fderiv ℝ w x) = 0
  rw [fderiv_of_notMem_tsupport ℝ hx, clm_map_zero]

end TernaryPoly.PolynomialFormCoordinates
