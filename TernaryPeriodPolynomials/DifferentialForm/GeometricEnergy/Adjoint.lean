module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.RealPullback

@[expose] public section


/-! Genuine pointwise symmetric-connection adjoints throughout the positive-form space. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem symmetricExterior_one_adjoint (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n 1) (b : FormValue n 2) :
    formPairing n 2 x (symmetricExterior n 1 x a) b =
      formPairing n 1 x a (symmetricContraction n 1 x b) := by
  obtain ⟨g,hg,he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let c := realFormPullback n 1 g y a
  let d := realFormPullback n 2 g y b
  have hc := realFormPullback_spec n 1 g y a
  have hd := realFormPullback_spec n 2 g y b
  calc
    formPairing n 2 (coordinateAction g y) (symmetricExterior n 1 (coordinateAction g y) a) b =
        formPairing n 2 y (symmetricExterior n 1 y c) d :=
      formPairing_real n 2 g hg y hy _ _ _ _ (symmetricExterior_real n 1 g hg y hy a c hc) hd
    _ = formPairing n 1 y c (symmetricContraction n 1 y d) :=
      symmetricExterior_one_basepoint_adjoint n c d
    _ = formPairing n 1 (coordinateAction g y) a (symmetricContraction n 1 (coordinateAction g y) b) :=
      (formPairing_real n 1 g hg y hy _ _ _ _ hc (symmetricContraction_real n 1 g hg y hy b d hd)).symm

theorem symmetricExterior_two_adjoint (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (a : FormValue n 2) (b : FormValue n 3) :
    formPairing n 3 x (symmetricExterior n 2 x a) b =
      formPairing n 2 x a (symmetricContraction n 2 x b) := by
  obtain ⟨g,hg,he⟩ := exists_normalized_real_frame x hx
  rw [← he]
  let y := coordinateChart basepoint
  have hy : y ∈ positiveCoordinates := extract_mem basepoint
  let c := realFormPullback n 2 g y a
  let d := realFormPullback n 3 g y b
  have hc := realFormPullback_spec n 2 g y a
  have hd := realFormPullback_spec n 3 g y b
  calc
    formPairing n 3 (coordinateAction g y) (symmetricExterior n 2 (coordinateAction g y) a) b =
        formPairing n 3 y (symmetricExterior n 2 y c) d :=
      formPairing_real n 3 g hg y hy _ _ _ _ (symmetricExterior_real n 2 g hg y hy a c hc) hd
    _ = formPairing n 2 y c (symmetricContraction n 2 y d) :=
      symmetricExterior_two_basepoint_adjoint n c d
    _ = formPairing n 2 (coordinateAction g y) a (symmetricContraction n 2 (coordinateAction g y) b) :=
      (formPairing_real n 2 g hg y hy _ _ _ _ hc (symmetricContraction_real n 2 g hg y hy b d hd)).symm

/-- The algebraic square has the actual sum-of-squares energy at every genuine point. -/
theorem symmetricHodgeTwo_energy (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates) (a : FormValue n 2) :
    formPairing n 2 x (symmetricHodgeTwo n x a) a =
      formPairing n 1 x (symmetricContraction n 1 x a) (symmetricContraction n 1 x a) +
      formPairing n 3 x (symmetricExterior n 2 x a) (symmetricExterior n 2 x a) := by
  rw [symmetricHodgeTwo, formPairing_add_left, symmetricExterior_one_adjoint n x hx]
  congr 1
  rw [formPairing_symm n 2 x hx, ← symmetricExterior_two_adjoint n x hx]

end TernaryPoly.PolynomialFormGeometricEnergy
