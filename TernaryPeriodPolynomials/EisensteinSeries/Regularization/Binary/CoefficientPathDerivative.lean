module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.MatrixPathDerivative
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.CompactReduction
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_determinantCharacter_hasDerivAt_traceless
    (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (traceless : Matrix.trace tangent = 0) :
    HasDerivAt (fun t => Binary.determinantCharacter (-1)
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) (path t))) 0 point := by
  have determinant := binary_matrix_det_hasDerivAt_one (fun t => (path t).val) tangent point
    (by simp [identity]) derivative
  rw [traceless] at determinant
  have inverse : HasDerivAt (fun t => ((path t).val.det)⁻¹) 0 point := by
    convert! determinant.inv (path point).det_ne_zero using 1
    simp
  have complex_inverse := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt point inverse
  convert! complex_inverse using 1
  ext t
  simp [Binary.determinantCharacter, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem binary_normPower_hasDerivAt_traceless
    (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (traceless : Matrix.trace tangent = 0) (exponent : ℂ) :
    HasDerivAt (fun t => normPower (GeneralLinearGroup.det (atInfinity (path t))) exponent) 0 point := by
  have determinant := binary_matrix_det_hasDerivAt_one (fun t => (path t).val) tangent point
    (by simp [identity]) derivative
  rw [traceless] at determinant
  have logarithm : HasDerivAt (fun t => Real.log (path t).val.det) 0 point := by
    simpa only [zero_div] using determinant.log (path point).det_ne_zero
  have complex_logarithm := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt point logarithm
  have exponential := (complex_logarithm.const_mul exponent).cexp
  convert! exponential using 1
  · ext t
    simp [det_atInfinity_binary, normPower_realAdeleUnit, GeneralLinearGroup.val_det_apply, Real.log_abs]
  · simp

theorem binary_coefficient_hasDerivAt_traceless
    (degree : ℕ) (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (traceless : Matrix.trace tangent = 0)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t => (binaryCoefficient degree (path t) polynomial).val.coeff monomial)
      ((binarySubstitutionDifferential 1
        (fun row column => -(tangent row column : ℂ)) polynomial.val).coeff monomial) point := by
  let inverse_path (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) (path t)⁻¹).val
  have inverse_derivative (row column : Fin 2) :
      HasDerivAt (fun t => inverse_path t row column) (-(tangent row column : ℂ)) point := by
    have computed := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt point
      (binary_group_inv_hasDerivAt_one path tangent point identity derivative row column)
    convert! computed using 1
    simp
  have inverse_identity : inverse_path point = 1 := by simp [inverse_path, identity]
  have substitution := binary_substitute_hasDerivAt inverse_path
    (fun row column => -(tangent row column : ℂ)) point inverse_derivative polynomial.val monomial
  rw [inverse_identity] at substitution
  have character := binary_determinantCharacter_hasDerivAt_traceless path tangent point identity derivative traceless
  convert! character.mul substitution using 1
  simp [identity]

theorem binary_twistedCoefficient_hasDerivAt_traceless
    (degree : ℕ) (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (traceless : Matrix.trace tangent = 0)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t => (normPower (GeneralLinearGroup.det (atInfinity (path t))) (((degree : ℂ) + 3) / 2) •
        binaryCoefficient degree (path t) polynomial).val.coeff monomial)
      ((binarySubstitutionDifferential 1
        (fun row column => -(tangent row column : ℂ)) polynomial.val).coeff monomial) point := by
  have coefficient := binary_coefficient_hasDerivAt_traceless degree path tangent point identity derivative traceless polynomial monomial
  have norm_power := binary_normPower_hasDerivAt_traceless path tangent point identity derivative traceless (((degree : ℂ) + 3) / 2)
  convert! norm_power.mul coefficient using 1
  simp [identity, binary_atInfinity_one, normPower_one]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
