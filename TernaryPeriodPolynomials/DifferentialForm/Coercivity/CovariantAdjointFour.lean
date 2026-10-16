module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ScalarPairingFour

@[expose] public section



/-! Degree-4 specialization of `inner_covariantExterior_one`/`inner_covariantExterior_two`
(`TernaryPoly.PolynomialFormGeometricEnergySplitting`): the Hilbert-adjoint relation between
`compactCovariantExterior n 4` and `compactCovariantAdjoint n 4`, needed to connect the degree-5
mixed energy to the degree-5 mixed operator. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Degree-4 mirror of `inner_covariantExterior_one`/`inner_covariantExterior_two`. -/
theorem inner_covariantExterior_four (n : ℕ) (a : Core n 4) (b : Core n 5) :
    inner ℝ (inclusion n 5 (compactCovariantExterior n 4 a)) (inclusion n 5 b) =
      inner ℝ (inclusion n 4 a) (inclusion n 4 (compactCovariantAdjoint n 4 b)) := by
  calc
    _ = inner ℝ (inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a))
          (inclusion n 5 b) -
        inner ℝ (inclusion n 5 (compactSymmetricExterior n 4 a)) (inclusion n 5 b) :=
      (congrArg (fun w => inner ℝ w (inclusion n 5 b)) (inclusion_covariantExterior n 4 a)).trans
        (inner_sub_left _ _ _)
    _ = inner ℝ (inclusion n 4 a) (inclusion n 4 (compactAdjoint n 4 b)) -
        inner ℝ (inclusion n 4 a) (inclusion n 4 (compactSymmetricContraction n 4 b)) :=
      congrArg₂ (· - ·) (inner_compactDifferential_compactAdjoint n 4 a b)
        (inner_symmetricExterior_four n a b)
    _ = _ := (inner_sub_right _ _ _).symm.trans
      (congrArg (inner ℝ (inclusion n 4 a)) (inclusion_covariantAdjoint n 4 b).symm)

end TernaryPeriodPolynomials.Argument.Coercivity
