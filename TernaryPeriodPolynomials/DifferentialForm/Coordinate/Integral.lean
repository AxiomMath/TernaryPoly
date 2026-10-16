module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Norm
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.Integral
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral

@[expose] public section

/-! Actual finite-component integral estimates before passage to the quotient Hilbert space. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open MeasureTheory PolynomialFormMetric SymmetricSpaceCharts CompactSquareIntegral
open scoped ContDiff

theorem integral_components_le_norm (n k : ℕ) (f : Coordinates → FormValue n k)
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    (∑ i, ∫ x, ‖components n k f i x‖^2) ≤
      ((Fintype.card (Index n k) : ℝ) * ‖(coordinates n k).toContinuousLinearMap‖^2) * ∫ x, ‖f x‖^2 := by
  have h := FiniteCoordinateSquare.compact_integral_coordinates_le_square
    (E := Coordinates) (F := FormValue n k) (I := Index n k) volume (coordinates n k) f
    hf.continuous hcf
  simpa only [components] using h

end TernaryPoly.PolynomialFormCoordinates
