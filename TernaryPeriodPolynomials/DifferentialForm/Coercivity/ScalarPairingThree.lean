module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AdjointThree
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Compact
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Transitions

@[expose] public section



/-! Degree-3 specializations of the quotient-descended scalar/Hilbert pairing identities relating
`compactSymmetricExterior`/`compactSymmetricContraction` as mutual adjoints, mirroring
`ScalarPairingFour.lean`'s degree-4 `scalarPairing_symmetricExterior_four`/`inner_symmetricExterior_four`
one level down via the pointwise adjoint fact `symmetricExterior_three_adjoint` proved in
`AdjointThree.lean`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise-descended scalar pairing identity at degree 3, mirroring
`scalarPairing_symmetricExterior_four` one level down. -/
theorem scalarPairing_symmetricExterior_three (n : ℕ) (a : Core n 3) (b : Core n 4) (q : OrbitSpace) :
    scalarPairing n 4 (compactSymmetricExterior n 3 a).val b.val q =
      scalarPairing n 3 a.val (compactSymmetricContraction n 3 b).val q := by
  change formPairing n 4 (coordinateChart (chosenLift q))
    ((compactSymmetricExterior n 3 a).val.val.val _) (b.val.val.val (coordinateChart (chosenLift q))) =
    formPairing n 3 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))
      ((compactSymmetricContraction n 3 b).val.val.val _)
  calc
    _ = formPairing n 4 (coordinateChart (chosenLift q))
        (symmetricExterior n 3 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))) (b.val.val.val (coordinateChart (chosenLift q))) :=
      congrArg (fun z => formPairing n 4 (coordinateChart (chosenLift q)) z (b.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricExterior_apply n 3 a (coordinateChart (chosenLift q)))
    _ = _ := (symmetricExterior_three_adjoint n _ (extract_mem (chosenLift q)) _ _).trans
      (congrArg (formPairing n 3 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricContraction_apply n 3 b (coordinateChart (chosenLift q))).symm)

/-- Hilbert-level adjointness at degree 3, mirroring `inner_symmetricExterior_four` one level
down. -/
theorem inner_symmetricExterior_three (n : ℕ) (a : Core n 3) (b : Core n 4) :
    inner ℝ (inclusion n 4 (compactSymmetricExterior n 3 a)) (inclusion n 4 b) =
      inner ℝ (inclusion n 3 a) (inclusion n 3 (compactSymmetricContraction n 3 b)) := by
  exact (inner_inclusion n 4 (compactSymmetricExterior n 3 a) b).trans
    ((integral_congr_ae (Filter.Eventually.of_forall (scalarPairing_symmetricExterior_three n a b))).trans
      (inner_inclusion n 3 a (compactSymmetricContraction n 3 b)).symm)

end TernaryPeriodPolynomials.Argument.Coercivity
