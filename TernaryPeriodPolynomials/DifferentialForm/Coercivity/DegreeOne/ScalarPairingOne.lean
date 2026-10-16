module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ScalarPairing
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Splitting

@[expose] public section



/-! The degree-0 Hilbert-adjoint identity for `compactCovariantExterior`, mirroring
`TernaryPoly.PolynomialFormGeometricEnergy.inner_covariantExterior_one` one level down. Unlike
the degree-3 `ScalarPairingThree.lean` (which has to build its own
`inner_symmetricExterior_three`, since the original authors only went up through degree two),
`inner_symmetricExterior_one` already exists in the original library, so only this one new wrapper is
needed for the degree-1 "lower" cross term, using the degree-0 `inner_symmetricExterior_zero` (`Proofs/Coercivity/ScalarPairing.lean`, read-only reference). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.CoercivityOne

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SmoothCoveringDeRham Set
open TernaryPeriodPolynomials.Argument.Coercivity (inner_symmetricExterior_zero)

/-- The degree-0 Hilbert-adjoint identity for `compactCovariantExterior`, mirroring
`inner_covariantExterior_one`. -/
theorem inner_covariantExterior_zero (n : ℕ) (a : Core n 0) (b : Core n 1) :
    inner ℝ (inclusion n 1 (compactCovariantExterior n 0 a)) (inclusion n 1 b) =
      inner ℝ (inclusion n 0 a) (inclusion n 0 (compactCovariantAdjoint n 0 b)) := by
  calc
    _ = inner ℝ (inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)) (inclusion n 1 b) -
        inner ℝ (inclusion n 1 (compactSymmetricExterior n 0 a)) (inclusion n 1 b) :=
      (congrArg (fun w => inner ℝ w (inclusion n 1 b)) (inclusion_covariantExterior n 0 a)).trans
        (inner_sub_left _ _ _)
    _ = inner ℝ (inclusion n 0 a) (inclusion n 0 (compactAdjoint n 0 b)) -
        inner ℝ (inclusion n 0 a) (inclusion n 0 (compactSymmetricContraction n 0 b)) :=
      congrArg₂ (· - ·) (inner_compactDifferential_compactAdjoint n 0 a b) (inner_symmetricExterior_zero n a b)
    _ = _ := (inner_sub_right _ _ _).symm.trans
      (congrArg (inner ℝ (inclusion n 0 a)) (inclusion_covariantAdjoint n 0 b).symm)

end TernaryPeriodPolynomials.Argument.CoercivityOne
