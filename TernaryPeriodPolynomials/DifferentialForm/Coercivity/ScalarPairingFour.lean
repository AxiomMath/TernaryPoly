module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AdjointFour

@[expose] public section



/-! Degree-4 specializations of the quotient-descended scalar/Hilbert pairing identities relating
`compactSymmetricExterior`/`compactSymmetricContraction` as mutual adjoints, mirroring
`ScalarPairing.lean`'s degree-0 `scalarPairing_symmetricExterior_zero`/`inner_symmetricExterior_zero`
via the pointwise adjoint fact `symmetricExterior_four_adjoint` proved in `AdjointFour.lean`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise-descended scalar pairing identity at degree 4, mirroring
`scalarPairing_symmetricExterior_zero`. -/
theorem scalarPairing_symmetricExterior_four (n : ℕ) (a : Core n 4) (b : Core n 5) (q : OrbitSpace) :
    scalarPairing n 5 (compactSymmetricExterior n 4 a).val b.val q =
      scalarPairing n 4 a.val (compactSymmetricContraction n 4 b).val q := by
  change formPairing n 5 (coordinateChart (chosenLift q))
    ((compactSymmetricExterior n 4 a).val.val.val _) (b.val.val.val (coordinateChart (chosenLift q))) =
    formPairing n 4 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))
      ((compactSymmetricContraction n 4 b).val.val.val _)
  calc
    _ = formPairing n 5 (coordinateChart (chosenLift q))
        (symmetricExterior n 4 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))) (b.val.val.val (coordinateChart (chosenLift q))) :=
      congrArg (fun z => formPairing n 5 (coordinateChart (chosenLift q)) z (b.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricExterior_apply n 4 a (coordinateChart (chosenLift q)))
    _ = _ := (symmetricExterior_four_adjoint n _ (extract_mem (chosenLift q)) _ _).trans
      (congrArg (formPairing n 4 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricContraction_apply n 4 b (coordinateChart (chosenLift q))).symm)

/-- Hilbert-level adjointness at degree 4, mirroring `inner_symmetricExterior_zero`. -/
theorem inner_symmetricExterior_four (n : ℕ) (a : Core n 4) (b : Core n 5) :
    inner ℝ (inclusion n 5 (compactSymmetricExterior n 4 a)) (inclusion n 5 b) =
      inner ℝ (inclusion n 4 a) (inclusion n 4 (compactSymmetricContraction n 4 b)) := by
  exact (inner_inclusion n 5 (compactSymmetricExterior n 4 a) b).trans
    ((integral_congr_ae (Filter.Eventually.of_forall (scalarPairing_symmetricExterior_four n a b))).trans
      (inner_inclusion n 4 a (compactSymmetricContraction n 4 b)).symm)

end TernaryPeriodPolynomials.Argument.Coercivity
