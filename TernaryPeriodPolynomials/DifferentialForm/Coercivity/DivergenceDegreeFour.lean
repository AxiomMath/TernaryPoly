module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.DegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDivergence

@[expose] public section



/-! Degree-4 specialization of the energy-current divergence formula, mirroring
`weightedDivergence_energyCurrent_three` (`DivergenceThree.lean`) one level up via
`covariant_contraction_anticommutator_four`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open scoped ContDiff

/-- The actual anticommutator provides a scalar expression suitable for quotient descent, at
degree 4, mirroring `weightedDivergence_energyCurrent_three`. -/
theorem weightedDivergence_energyCurrent_four (n : ℕ) {w : Coordinates → FormValue n 4}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    weightedDivergence (energyCurrent n 4 w) x =
      2 * formPairing n 4 x (w x)
        (symmetricContraction n 4 x (covariantExterior n 4 w x) +
          covariantExterior n 3 (fun y => symmetricContraction n 3 y (w y)) x) := by
  rw [weightedDivergence_energyCurrent n 4 hw x hx,
    covariant_contraction_anticommutator_four n w x hx
      (((hw x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))]

end TernaryPeriodPolynomials.Argument.Coercivity
