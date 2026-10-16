module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator

@[expose] public section



/-! Degree-0 specialization of the energy-current divergence formula. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open scoped ContDiff

/-- The actual anticommutator provides a scalar expression suitable for quotient descent, at k = 0:
no second summand (unlike `weightedDivergence_energyCurrent_two`). -/
theorem weightedDivergence_energyCurrent_zero (n : ℕ) {w : Coordinates → FormValue n 0}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    weightedDivergence (energyCurrent n 0 w) x =
      2 * formPairing n 0 x (w x) (symmetricContraction n 0 x (covariantExterior n 0 w x)) := by
  rw [weightedDivergence_energyCurrent n 0 hw x hx, ← covariant_contraction_anticommutator_zero n w x hx]

end TernaryPeriodPolynomials.Argument.Coercivity
