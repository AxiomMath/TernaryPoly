module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.TracelessCoboundary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_conjugate_trace (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (matrix.inv * direction * matrix.val) = Matrix.trace direction := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, matrix.val_inv, one_mul]

theorem binary_conjugate_identity_line_derivative (matrix : BinaryRealGL)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (row column : Fin 2) :
    HasDerivAt (fun parameter => (matrix⁻¹ * binaryIdentityLine direction parameter * matrix).val row column)
      ((matrix.inv * direction * matrix.val) row column) 0 := by
  let conjugation : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.mulRight ℝ matrix.val).comp (LinearMap.mulLeft ℝ matrix.inv))
  have computed := conjugation.hasFDerivAt.comp_hasDerivAt 0 (binaryIdentityLine_hasDerivAt direction)
  have matrix_derivative : HasDerivAt
      (fun parameter => (matrix⁻¹ * binaryIdentityLine direction parameter * matrix).val)
      (matrix.inv * direction * matrix.val) 0 := by
    convert! computed using 1
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp matrix_derivative row) column

theorem binaryCohomologicalDerivedOperator_covariance
    (cusp : CuspidalRepresentation) (degree : ℕ) (matrix : BinaryRealGL)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace direction = 0)
    (vectors : BinaryDegreeMonomial (degree + 1) → cusp.smooth) :
    binaryCohomologicalDerivedOperator cusp degree direction
        (binaryCohomologicalRepresentation cusp degree matrix vectors) =
      binaryCohomologicalRepresentation cusp degree matrix
        (binaryCohomologicalDerivedOperator cusp degree (matrix.inv * direction * matrix.val) vectors) := by
  have left_derivative := binaryCohomologicalHilbertAction_path_hasDerivAt cusp degree
    (binaryCohomologicalRepresentation cusp degree matrix vectors)
    (binaryIdentityLine direction) direction 0 (binaryIdentityLine_zero direction)
    (binaryIdentityLine_entry_hasDerivAt direction) traceless
  have conjugate_traceless : Matrix.trace (matrix.inv * direction * matrix.val) = 0 := by
    rw [binary_conjugate_trace, traceless]
  have inside_derivative := binaryCohomologicalHilbertAction_path_hasDerivAt cusp degree vectors
    (fun parameter => matrix⁻¹ * binaryIdentityLine direction parameter * matrix)
    (matrix.inv * direction * matrix.val) 0
    (by rw [binaryIdentityLine_zero]; simp)
    (binary_conjugate_identity_line_derivative matrix direction) conjugate_traceless
  have right_derivative := ((binaryCohomologicalHilbertAction cusp degree matrix).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 inside_derivative
  have equality :
      (fun parameter => binaryCohomologicalHilbertAction cusp degree (binaryIdentityLine direction parameter)
        (fun monomial => (binaryCohomologicalRepresentation cusp degree matrix vectors monomial).val)) =
      (fun parameter => binaryCohomologicalHilbertAction cusp degree matrix
        (binaryCohomologicalHilbertAction cusp degree
          (matrix⁻¹ * binaryIdentityLine direction parameter * matrix) (fun monomial => (vectors monomial).val))) := by
    funext parameter
    simp only [binaryCohomologicalHilbertAction_smooth]
    change (fun monomial =>
      (binaryCohomologicalRepresentation cusp degree (binaryIdentityLine direction parameter)
        (binaryCohomologicalRepresentation cusp degree matrix vectors) monomial).val) =
      (fun monomial => (binaryCohomologicalRepresentation cusp degree matrix
        (binaryCohomologicalRepresentation cusp degree
          (matrix⁻¹ * binaryIdentityLine direction parameter * matrix) vectors) monomial).val)
    have group_equality : binaryIdentityLine direction parameter * matrix =
        matrix * (matrix⁻¹ * binaryIdentityLine direction parameter * matrix) := by simp [mul_assoc]
    have vector_equality := congrArg (fun element => binaryCohomologicalRepresentation cusp degree element vectors) group_equality
    simp only [map_mul, Module.End.mul_apply] at vector_equality
    rw [vector_equality]
    simp only [map_mul, Module.End.mul_apply]
  have right_derivative' := right_derivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun parameter => congrFun equality parameter))
  have result := left_derivative.unique right_derivative'
  change (fun monomial => (binaryCohomologicalDerivedOperator cusp degree direction
    (binaryCohomologicalRepresentation cusp degree matrix vectors) monomial).val) =
    binaryCohomologicalHilbertAction cusp degree matrix
      (fun monomial => (binaryCohomologicalDerivedOperator cusp degree (matrix.inv * direction * matrix.val) vectors monomial).val) at result
  rw [binaryCohomologicalHilbertAction_smooth] at result
  funext monomial
  exact Subtype.ext (congrFun result monomial)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
