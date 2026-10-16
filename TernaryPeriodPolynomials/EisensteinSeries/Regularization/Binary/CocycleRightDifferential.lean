module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.DerivedCovariance

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryCocycle_right_differential_equation
    (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (identity : ∀ first second, cocycle (first * second) = cocycle first +
      binaryCohomologicalRepresentation cusp degree first (cocycle second))
    (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace direction = 0) :
    fderiv ℝ (binaryCocycleHilbertFamily cusp degree cocycle) matrix.val (direction * matrix.val) =
      (fun monomial => (binaryCocycleInfinitesimal cusp degree cocycle smooth finite direction monomial).val) +
        (fun monomial => (binaryCohomologicalDerivedOperator cusp degree direction (cocycle matrix) monomial).val) := by
  let family := binaryCocycleHilbertFamily cusp degree cocycle
  have line_derivative := binaryIdentityLine_hasDerivAt direction
  have at_one := ((binaryCocycleHilbertFamily_contDiffAt cusp degree cocycle smooth 1).differentiableAt (by simp)).hasFDerivAt
  have cocycle_derivative := at_one.comp_hasDerivAt_of_eq 0 line_derivative (by rw [binaryIdentityLine_zero])
  have action_derivative := binaryCohomologicalHilbertAction_path_hasDerivAt cusp degree (cocycle matrix)
    (binaryIdentityLine direction) direction 0 (binaryIdentityLine_zero direction)
    (binaryIdentityLine_entry_hasDerivAt direction) traceless
  have right_derivative := cocycle_derivative.add action_derivative
  let right : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ matrix.val)
  have product_derivative := right.hasFDerivAt.comp_hasDerivAt 0 line_derivative
  have at_matrix := ((binaryCocycleHilbertFamily_contDiffAt cusp degree cocycle smooth matrix).differentiableAt (by simp)).hasFDerivAt
  have left_derivative := at_matrix.comp_hasDerivAt_of_eq 0 product_derivative
    (by change matrix.val = (binaryIdentityLine direction 0).val * matrix.val; rw [binaryIdentityLine_zero]; simp)
  have equality :
      (fun parameter => family (right (binaryIdentityLine direction parameter).val)) =
      (fun parameter => family (binaryIdentityLine direction parameter).val +
        binaryCohomologicalHilbertAction cusp degree (binaryIdentityLine direction parameter)
          (fun monomial => (cocycle matrix monomial).val)) := by
    funext parameter
    have value : right (binaryIdentityLine direction parameter).val =
        (binaryIdentityLine direction parameter * matrix).val := rfl
    rw [value]
    rw [binaryCohomologicalHilbertAction_smooth]
    funext monomial
    change (cocycle (invertibleMatrix (binaryIdentityLine direction parameter * matrix).val) monomial).val =
      (cocycle (invertibleMatrix (binaryIdentityLine direction parameter).val) monomial).val +
        (binaryCohomologicalRepresentation cusp degree (binaryIdentityLine direction parameter) (cocycle matrix) monomial).val
    rw [invertibleMatrix_val, invertibleMatrix_val, identity]
    rfl
  have right_derivative' := right_derivative.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun parameter => congrFun equality parameter))
  have result := left_derivative.unique right_derivative'
  change fderiv ℝ family matrix.val (direction * matrix.val) =
    fderiv ℝ family 1 direction +
      (fun monomial => (binaryCohomologicalDerivedOperator cusp degree direction (cocycle matrix) monomial).val) at result
  rw [binaryCocycleHilbertFamily_identity_derivative cusp degree cocycle smooth finite direction] at result
  exact result

theorem binaryCocycleInfinitesimal_group_relation
    (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (identity : ∀ first second, cocycle (first * second) = cocycle first +
      binaryCohomologicalRepresentation cusp degree first (cocycle second))
    (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace direction = 0) :
    binaryCocycleInfinitesimal cusp degree cocycle smooth finite direction +
      binaryCohomologicalDerivedOperator cusp degree direction (cocycle matrix) =
      binaryCohomologicalRepresentation cusp degree matrix
        (binaryCocycleInfinitesimal cusp degree cocycle smooth finite (matrix.inv * direction * matrix.val)) := by
  have right := binaryCocycle_right_differential_equation cusp degree cocycle smooth finite identity matrix direction traceless
  have left := binaryCocycle_left_differential_equation cusp degree cocycle smooth identity matrix (matrix.inv * direction * matrix.val)
  have tangent : matrix.val * (matrix.inv * direction * matrix.val) = direction * matrix.val := by
    rw [← mul_assoc, ← mul_assoc, matrix.val_inv, one_mul]
  rw [tangent, right, binaryCocycleHilbertFamily_identity_derivative cusp degree cocycle smooth finite,
    binaryCohomologicalHilbertAction_smooth] at left
  funext monomial
  apply Subtype.ext
  exact congrFun left monomial

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
