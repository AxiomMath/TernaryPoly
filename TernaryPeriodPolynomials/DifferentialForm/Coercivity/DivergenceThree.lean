module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.Three
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDivergence

@[expose] public section



/-! Degree-3 specialization of the energy-current divergence formula, mirroring
`weightedDivergence_energyCurrent_two`
(`TernaryPeriodPolynomials/DifferentialForm/Connection/Energy/CurrentDivergence.lean`) one level up via
`covariant_contraction_anticommutator_three`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open scoped ContDiff

/-- The actual anticommutator provides a scalar expression suitable for quotient descent, at
degree 3, mirroring `weightedDivergence_energyCurrent_two`. -/
theorem weightedDivergence_energyCurrent_three (n : ℕ) {w : Coordinates → FormValue n 3}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    weightedDivergence (energyCurrent n 3 w) x =
      2 * formPairing n 3 x (w x)
        (symmetricContraction n 3 x (covariantExterior n 3 w x) +
          covariantExterior n 2 (fun y => symmetricContraction n 2 y (w y)) x) := by
  rw [weightedDivergence_energyCurrent n 3 hw x hx,
    covariant_contraction_anticommutator_three n w x hx
      (((hw x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))]

end TernaryPeriodPolynomials.Argument.Coercivity
