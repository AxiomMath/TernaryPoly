module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.MatrixDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PolynomialDerivative TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryMatrixDerivative
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientDerivative

def complexDirection (direction : BinaryMatrix) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun row column => (direction row column : ℂ)

noncomputable def polynomialOperator (degree : ℕ) (direction : BinaryMatrix) : Module.End ℂ Binary.Poly :=
  (((degree : ℂ) + 1) / 2 * ((direction 0 0 + direction 1 1 : ℝ) : ℂ)) • LinearMap.id +
    (variableDerivative (-complexDirection direction)).toLinearMap

theorem binaryCoefficient_coe (degree : ℕ) (matrix : BinaryRealGL)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    (binaryCoefficient degree matrix polynomial).val = (matrix.val.det : ℂ)⁻¹ •
      Binary.substitute (fun row column => (matrix⁻¹.val row column : ℂ)) polynomial.val := by
  rw [binaryCoefficient, Binary.homogeneousAction_coe, Binary.action_apply]
  change Binary.determinantCharacter (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix) • _ = _
  congr 1
  change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)).val ^ (-1 : ℤ)) = _
  have determinantMap : (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)).val =
      (matrix.val.det : ℂ) := (RingHom.map_det (algebraMap ℝ ℂ) matrix.val).symm
  rw [determinantMap, zpow_neg_one]

theorem inverse_path_zero (direction : BinaryMatrix) :
    (fun row column => ((invertibleMatrix (path direction 0))⁻¹.val row column : ℂ)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [path_zero, show invertibleMatrix (1 : BinaryMatrix) = 1 from invertibleMatrix_units 1]
  ext row column
  fin_cases row <;> fin_cases column <;> simp

theorem substitute_inverse_derivative (direction : BinaryMatrix) (polynomial : Binary.Poly)
    (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun parameter => (Binary.substitute (fun row column => ((invertibleMatrix (path direction parameter))⁻¹.val row column : ℂ)) polynomial).coeff monomial)
      ((variableDerivative (-complexDirection direction) polynomial).coeff monomial) 0 := by
  apply substitute_derivative _ _ 0 (inverse_path_zero direction)
  intro row column
  have derivative := (inverse_entry_derivative direction row column).ofReal_comp
  simp only [Complex.ofReal_neg] at derivative
  exact derivative

theorem coefficient_path_derivative (degree : ℕ) (direction : BinaryMatrix)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun parameter =>
      normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (path direction parameter)))) (((degree : ℂ) + 3) / 2) *
        (binaryCoefficient degree (invertibleMatrix (path direction parameter)) polynomial).val.coeff monomial)
      ((polynomialOperator degree direction polynomial.val).coeff monomial) 0 := by
  let exponent : ℂ := ((degree : ℂ) + 3) / 2
  have determinantNonzero : ((path direction 0).det : ℂ) ≠ 0 := by simp [path_zero]
  have inverseDeterminant := (determinant_derivative direction).ofReal_comp.inv determinantNonzero
  have substitution := substitute_inverse_derivative direction polynomial.val monomial
  have modelDerivative := ((normPower_derivative exponent direction).mul inverseDeterminant).mul substitution
  have matrixOne : invertibleMatrix (path direction 0) = (1 : BinaryRealGL) := by
    rw [path_zero]; exact invertibleMatrix_units 1
  have atOne : normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (path direction 0)))) exponent = 1 := by
    rw [matrixOne, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, map_one, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one]
  have substitutionAtOne : (Binary.substitute (fun row column => ((invertibleMatrix (path direction 0))⁻¹.val row column : ℂ)) polynomial.val).coeff monomial =
      polynomial.val.coeff monomial := by
    rw [inverse_path_zero, Binary.substitute_one]
    rfl
  have valueEquality :
      (exponent * ((direction 0 0 + direction 1 1 : ℝ) : ℂ) - ((direction 0 0 + direction 1 1 : ℝ) : ℂ)) *
          polynomial.val.coeff monomial +
        (variableDerivative (-complexDirection direction) polynomial.val).coeff monomial =
      (polynomialOperator degree direction polynomial.val).coeff monomial := by
    simp only [polynomialOperator, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Derivation.coeFn_coe, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_smul, smul_eq_mul, exponent]
    ring
  have adjusted : HasDerivAt (fun parameter =>
      normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (path direction parameter)))) exponent *
        ((path direction parameter).det : ℂ)⁻¹ *
          (Binary.substitute
            (fun row column => ((invertibleMatrix (path direction parameter))⁻¹.val row column : ℂ)) polynomial.val).coeff monomial)
      ((polynomialOperator degree direction polynomial.val).coeff monomial) 0 := by
    apply modelDerivative.congr_deriv
    change (exponent * ((direction 0 0 + direction 1 1 : ℝ) : ℂ) * ((path direction 0).det : ℂ)⁻¹ +
        normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (path direction 0)))) exponent *
          (-((direction 0 0 + direction 1 1 : ℝ) : ℂ) / ((path direction 0).det : ℂ) ^ 2)) *
        (Binary.substitute
          (fun row column => ((invertibleMatrix (path direction 0))⁻¹.val row column : ℂ)) polynomial.val).coeff monomial +
      (normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (path direction 0)))) exponent *
        ((path direction 0).det : ℂ)⁻¹) *
        (variableDerivative (-complexDirection direction) polynomial.val).coeff monomial = _
    rw [atOne, substitutionAtOne]
    simp only [path_zero, Matrix.det_one, Complex.ofReal_one, inv_one, one_pow,
      div_one, mul_one, one_mul]
    exact valueEquality
  apply adjusted.congr_of_eventuallyEq
  filter_upwards [path_invertible direction] with parameter invertibility
  rw [binaryCoefficient_coe, MvPolynomial.coeff_smul, smul_eq_mul, invertibleMatrix_val _ invertibility]
  exact (mul_assoc _ _ _).symm

/-- The exact coefficient matrix is the trace twist plus inverse-substitution differentiation. -/
theorem coefficientDerivative_eq (degree : ℕ) (direction : BinaryMatrix) (index other : Index (degree + 1)) :
    coefficientDerivative degree direction index other =
      (polynomialOperator degree direction (basisMonomial other).val).coeff index.val := by
  have regularity := ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientRegularity.multiplier_contDiffAt degree index other 1 (by simp)).differentiableAt
    (by simp)).hasFDerivAt
  have derivative := regularity.comp_hasDerivAt_of_eq 0 (path_derivative direction) (path_zero direction).symm
  exact derivative.unique (coefficient_path_derivative degree direction (basisMonomial other) index.val)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientDerivative
