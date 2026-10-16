module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Adjoint

@[expose] public section



/-! Degree-0 specializations of the quotient-descended scalar/Hilbert pairing identities relating
`compactSymmetricExterior`/`compactSymmetricContraction` as mutual adjoints, mirroring
`scalarPairing_symmetricExterior_one`/`inner_symmetricExterior_one` (degree 1) via the pointwise
adjoint fact `symmetricExterior_zero_adjoint` proved in `Adjoint.lean`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Pointwise-descended scalar pairing identity at degree 0, mirroring
`scalarPairing_symmetricExterior_one`. -/
theorem scalarPairing_symmetricExterior_zero (n : ℕ) (a : Core n 0) (b : Core n 1) (q : OrbitSpace) :
    scalarPairing n 1 (compactSymmetricExterior n 0 a).val b.val q =
      scalarPairing n 0 a.val (compactSymmetricContraction n 0 b).val q := by
  change formPairing n 1 (coordinateChart (chosenLift q))
    ((compactSymmetricExterior n 0 a).val.val.val _) (b.val.val.val (coordinateChart (chosenLift q))) =
    formPairing n 0 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))
      ((compactSymmetricContraction n 0 b).val.val.val _)
  calc
    _ = formPairing n 1 (coordinateChart (chosenLift q))
        (symmetricExterior n 0 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))) (b.val.val.val (coordinateChart (chosenLift q))) :=
      congrArg (fun z => formPairing n 1 (coordinateChart (chosenLift q)) z (b.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricExterior_apply n 0 a (coordinateChart (chosenLift q)))
    _ = _ := (symmetricExterior_zero_adjoint n _ (extract_mem (chosenLift q)) _ _).trans
      (congrArg (formPairing n 0 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricContraction_apply n 0 b (coordinateChart (chosenLift q))).symm)

/-- Hilbert-level adjointness at degree 0, mirroring `inner_symmetricExterior_one`. -/
theorem inner_symmetricExterior_zero (n : ℕ) (a : Core n 0) (b : Core n 1) :
    inner ℝ (inclusion n 1 (compactSymmetricExterior n 0 a)) (inclusion n 1 b) =
      inner ℝ (inclusion n 0 a) (inclusion n 0 (compactSymmetricContraction n 0 b)) := by
  exact (inner_inclusion n 1 (compactSymmetricExterior n 0 a) b).trans
    ((integral_congr_ae (Filter.Eventually.of_forall (scalarPairing_symmetricExterior_zero n a b))).trans
      (inner_inclusion n 0 a (compactSymmetricContraction n 0 b)).symm)

end TernaryPeriodPolynomials.Argument.Coercivity
