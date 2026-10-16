module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.AnticommutatorOne
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDivergence

@[expose] public section



/-! Degree-1 specialization of the energy-current divergence formula, mirroring
`TernaryPeriodPolynomials.Argument.Coercivity.weightedDivergence_energyCurrent_three`
(`Proofs/Coercivity/DivergenceThree.lean`) one level down via
`covariant_contraction_anticommutator_one`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open scoped ContDiff

/-- The actual anticommutator provides a scalar expression suitable for quotient descent, at
degree 1, mirroring `weightedDivergence_energyCurrent_three`. -/
theorem weightedDivergence_energyCurrent_one (n : ℕ) {w : Coordinates → FormValue n 1}
    (hw : ContDiffOn ℝ ∞ w positiveCoordinates) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    weightedDivergence (energyCurrent n 1 w) x =
      2 * formPairing n 1 x (w x)
        (symmetricContraction n 1 x (covariantExterior n 1 w x) +
          covariantExterior n 0 (fun y => symmetricContraction n 0 y (w y)) x) := by
  rw [weightedDivergence_energyCurrent n 1 hw x hx,
    covariant_contraction_anticommutator_one n w x hx
      (((hw x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))]

end TernaryPeriodPolynomials.Argument.CoercivityOne
