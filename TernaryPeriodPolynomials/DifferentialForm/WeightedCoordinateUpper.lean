module

public import TernaryPeriodPolynomials.DifferentialForm.WeightedSquare
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.IntegralUpper
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Norm

@[expose] public section


/-! Actual compact weighted energy controlled directly by scalar coordinate squares. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory PolynomialFormMetric SymmetricSpaceCharts CompactSquareIntegral
open scoped ContDiff

theorem exists_compact_weighted_coordinate_upper (n k : ℕ) {K : Set Coordinates}
    (hK : IsCompact K) (hKpos : K ⊆ positiveCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Coordinates → FormValue n k,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ K →
      (∫ x, weightedSquare n k w x) ≤ C * ∑ i, ∫ x, ‖components n k w i x‖^2 := by
  obtain ⟨d,C,_,hC,hbound⟩ := compact_integral_weighted_bounds n k hK hKpos
  refine ⟨C * ‖(coordinates n k).symm.toContinuousLinearMap‖^2, mul_nonneg hC (sq_nonneg _), ?_⟩
  intro w hw hcw hsw
  have hcoord := FiniteCoordinateSquare.compact_integral_square_le_coordinates
    (E := Coordinates) (F := FormValue n k) (I := Index n k) volume (coordinates n k) w hw.continuous hcw
  exact (hbound w hw hcw hsw).2.trans
    ((mul_le_mul_of_nonneg_left hcoord hC).trans_eq (mul_assoc C _ _).symm)

end TernaryPoly.PolynomialFormCoordinates
