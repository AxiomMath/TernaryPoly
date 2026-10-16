module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Compact
public import TernaryPeriodPolynomials.DifferentialForm.QuotientPairing

@[expose] public section

/-! Actual quotient integrals of the symmetric-connection algebraic energy. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientBundle PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection PolynomialFormCoordinates
open SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceRiemannian
open SmoothCoveringDeRham SmoothLocalDeRham Set MeasureTheory
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

theorem scalarPairing_symmetricExterior_one (n : ℕ)
    (a : CompactSupportForm (deckRepresentation n) univ 1) (b : CompactSupportForm (deckRepresentation n) univ 2) (q : OrbitSpace) :
    scalarPairing n 2 (compactSymmetricExterior n 1 a).val b.val q =
      scalarPairing n 1 a.val (compactSymmetricContraction n 1 b).val q := by
  change formPairing n 2 (coordinateChart (chosenLift q))
    ((compactSymmetricExterior n 1 a).val.val.val _) (b.val.val.val (coordinateChart (chosenLift q))) =
    formPairing n 1 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))
      ((compactSymmetricContraction n 1 b).val.val.val _)
  calc
    _ = formPairing n 2 (coordinateChart (chosenLift q))
        (symmetricExterior n 1 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))) (b.val.val.val (coordinateChart (chosenLift q))) :=
      congrArg (fun z => formPairing n 2 (coordinateChart (chosenLift q)) z (b.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricExterior_apply n 1 a (coordinateChart (chosenLift q)))
    _ = _ := (symmetricExterior_one_adjoint n _ (extract_mem (chosenLift q)) _ _).trans
      (congrArg (formPairing n 1 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricContraction_apply n 1 b (coordinateChart (chosenLift q))).symm)

theorem scalarPairing_symmetricExterior_two (n : ℕ)
    (a : CompactSupportForm (deckRepresentation n) univ 2) (b : CompactSupportForm (deckRepresentation n) univ 3) (q : OrbitSpace) :
    scalarPairing n 3 (compactSymmetricExterior n 2 a).val b.val q =
      scalarPairing n 2 a.val (compactSymmetricContraction n 2 b).val q := by
  change formPairing n 3 (coordinateChart (chosenLift q))
    ((compactSymmetricExterior n 2 a).val.val.val _) (b.val.val.val (coordinateChart (chosenLift q))) =
    formPairing n 2 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))
      ((compactSymmetricContraction n 2 b).val.val.val _)
  calc
    _ = formPairing n 3 (coordinateChart (chosenLift q))
        (symmetricExterior n 2 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))) (b.val.val.val (coordinateChart (chosenLift q))) :=
      congrArg (fun z => formPairing n 3 (coordinateChart (chosenLift q)) z (b.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricExterior_apply n 2 a (coordinateChart (chosenLift q)))
    _ = _ := (symmetricExterior_two_adjoint n _ (extract_mem (chosenLift q)) _ _).trans
      (congrArg (formPairing n 2 (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q))))
        (compactSymmetricContraction_apply n 2 b (coordinateChart (chosenLift q))).symm)

@[simp] theorem scalarPairing_symmetricExterior_self (n k : ℕ)
    (a : CompactSupportForm (deckRepresentation n) univ k) (q : OrbitSpace) :
    scalarPairing n (k + 1) (compactSymmetricExterior n k a).val (compactSymmetricExterior n k a).val q =
    formPairing n (k + 1) (coordinateChart (chosenLift q))
      (symmetricExterior n k (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q))))
      (symmetricExterior n k (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))) :=
  congrArg₂ (formPairing n (k + 1) (coordinateChart (chosenLift q)))
    (compactSymmetricExterior_apply n k a _) (compactSymmetricExterior_apply n k a _)

@[simp] theorem scalarPairing_symmetricContraction_self (n k : ℕ)
    (a : CompactSupportForm (deckRepresentation n) univ (k + 1)) (q : OrbitSpace) :
    scalarPairing n k (compactSymmetricContraction n k a).val (compactSymmetricContraction n k a).val q =
    formPairing n k (coordinateChart (chosenLift q))
      (symmetricContraction n k (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q))))
      (symmetricContraction n k (coordinateChart (chosenLift q)) (a.val.val.val (coordinateChart (chosenLift q)))) :=
  congrArg₂ (formPairing n k (coordinateChart (chosenLift q)))
    (compactSymmetricContraction_apply n k a _) (compactSymmetricContraction_apply n k a _)

end TernaryPoly.PolynomialFormGeometricEnergy
