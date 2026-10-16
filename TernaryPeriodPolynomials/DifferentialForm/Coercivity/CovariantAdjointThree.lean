module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.ScalarPairingThree
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Splitting

@[expose] public section



/-! Degree-3 specialization of `inner_covariantExterior_one`/`inner_covariantExterior_two`
(`TernaryPoly.PolynomialFormGeometricEnergySplitting`), one level up from those and one level down
from `inner_covariantExterior_four` (`CovariantAdjointFour.lean`): the Hilbert-adjoint relation
between `compactCovariantExterior n 3` and `compactCovariantAdjoint n 3`, needed to connect the
degree-4 mixed energy (`MixedEnergyDegreeFour.lean`) to the degree-4 mixed operator. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Degree-3 mirror of `inner_covariantExterior_one`/`inner_covariantExterior_two`/
`inner_covariantExterior_four`. -/
theorem inner_covariantExterior_three (n : ℕ) (a : Core n 3) (b : Core n 4) :
    inner ℝ (inclusion n 4 (compactCovariantExterior n 3 a)) (inclusion n 4 b) =
      inner ℝ (inclusion n 3 a) (inclusion n 3 (compactCovariantAdjoint n 3 b)) := by
  calc
    _ = inner ℝ (inclusion n 4 (compactDifferential (deckRepresentation n) isOpen_univ 3 a))
          (inclusion n 4 b) -
        inner ℝ (inclusion n 4 (compactSymmetricExterior n 3 a)) (inclusion n 4 b) :=
      (congrArg (fun w => inner ℝ w (inclusion n 4 b)) (inclusion_covariantExterior n 3 a)).trans
        (inner_sub_left _ _ _)
    _ = inner ℝ (inclusion n 3 a) (inclusion n 3 (compactAdjoint n 3 b)) -
        inner ℝ (inclusion n 3 a) (inclusion n 3 (compactSymmetricContraction n 3 b)) :=
      congrArg₂ (· - ·) (inner_compactDifferential_compactAdjoint n 3 a b)
        (inner_symmetricExterior_three n a b)
    _ = _ := (inner_sub_right _ _ _).symm.trans
      (congrArg (inner ℝ (inclusion n 3 a)) (inclusion_covariantAdjoint n 3 b).symm)

end TernaryPeriodPolynomials.Argument.Coercivity
