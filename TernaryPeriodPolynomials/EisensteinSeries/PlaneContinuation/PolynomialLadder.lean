module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.CoefficientDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PolynomialDerivative TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientDerivative TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PolynomialLadder

noncomputable def plusVariable : Binary.Poly := MvPolynomial.X 0 + Complex.I • MvPolynomial.X 1

noncomputable def minusVariable : Binary.Poly := MvPolynomial.X 0 - Complex.I • MvPolynomial.X 1

noncomputable def rotation : Derivation ℂ Binary.Poly Binary.Poly := variableDerivative (-complexDirection rotationMatrix)

noncomputable def diagonal : Derivation ℂ Binary.Poly Binary.Poly := variableDerivative (-complexDirection diagonalMatrix)

noncomputable def symmetric : Derivation ℂ Binary.Poly Binary.Poly := variableDerivative (-complexDirection symmetricMatrix)

noncomputable def raising : Derivation ℂ Binary.Poly Binary.Poly := diagonal - Complex.I • symmetric

noncomputable def lowering : Derivation ℂ Binary.Poly Binary.Poly := diagonal + Complex.I • symmetric

theorem rotation_plus : rotation plusVariable = -Complex.I • plusVariable := by
  simp [rotation, variableDerivative, plusVariable, complexDirection, rotationMatrix,
    Binary.linearForm, Fin.sum_univ_two, smul_add, smul_smul, Complex.I_mul_I]
  module

theorem rotation_minus : rotation minusVariable = Complex.I • minusVariable := by
  simp [rotation, variableDerivative, minusVariable, complexDirection, rotationMatrix,
    Binary.linearForm, Fin.sum_univ_two, smul_sub, smul_smul, Complex.I_mul_I]
  module

theorem diagonal_plus : diagonal plusVariable = -minusVariable := by
  simp [diagonal, variableDerivative, plusVariable, minusVariable, complexDirection,
    diagonalMatrix, Binary.linearForm, Fin.sum_univ_two]
  module

theorem diagonal_minus : diagonal minusVariable = -plusVariable := by
  simp [diagonal, variableDerivative, plusVariable, minusVariable, complexDirection,
    diagonalMatrix, Binary.linearForm, Fin.sum_univ_two]
  module

theorem symmetric_plus : symmetric plusVariable = -Complex.I • minusVariable := by
  simp [symmetric, variableDerivative, plusVariable, minusVariable, complexDirection,
    symmetricMatrix, Binary.linearForm, Fin.sum_univ_two, smul_sub, smul_smul, Complex.I_mul_I]
  module

theorem symmetric_minus : symmetric minusVariable = Complex.I • plusVariable := by
  simp [symmetric, variableDerivative, plusVariable, minusVariable, complexDirection,
    symmetricMatrix, Binary.linearForm, Fin.sum_univ_two, smul_add, smul_smul, Complex.I_mul_I]
  module

theorem raising_plus : raising plusVariable = (-2 : ℂ) • minusVariable := by
  simp only [raising, Derivation.sub_apply, Derivation.smul_apply, diagonal_plus, symmetric_plus,
    smul_smul]
  norm_num
  module

theorem raising_minus : raising minusVariable = 0 := by
  simp [raising, diagonal_minus, symmetric_minus, smul_smul]

theorem lowering_plus : lowering plusVariable = 0 := by
  simp [lowering, diagonal_plus, symmetric_plus, smul_smul]

theorem lowering_minus : lowering minusVariable = (-2 : ℂ) • plusVariable := by
  simp only [lowering, Derivation.add_apply, Derivation.smul_apply, diagonal_minus, symmetric_minus,
    smul_smul]
  norm_num
  module

theorem polynomialOperator_rotation (degree : ℕ) :
    polynomialOperator degree rotationMatrix = rotation.toLinearMap := by
  simp [polynomialOperator, rotationMatrix, rotation, Complex.ofReal_zero]

theorem polynomialOperator_diagonal (degree : ℕ) :
    polynomialOperator degree diagonalMatrix = diagonal.toLinearMap := by
  simp [polynomialOperator, diagonalMatrix, diagonal, Complex.ofReal_zero]

theorem polynomialOperator_symmetric (degree : ℕ) :
    polynomialOperator degree symmetricMatrix = symmetric.toLinearMap := by
  simp [polynomialOperator, symmetricMatrix, symmetric, Complex.ofReal_zero]

noncomputable def monomial (plus minus : ℕ) : Binary.Poly := plusVariable ^ plus * minusVariable ^ minus

theorem plusVariable_homogeneous : plusVariable.IsHomogeneous 1 := by
  exact (MvPolynomial.isHomogeneous_X ℂ 0).add
    ((Binary.HomogeneousPoly 1).smul_mem Complex.I (MvPolynomial.isHomogeneous_X ℂ 1))

theorem minusVariable_homogeneous : minusVariable.IsHomogeneous 1 := by
  exact (MvPolynomial.isHomogeneous_X ℂ 0).sub
    ((Binary.HomogeneousPoly 1).smul_mem Complex.I (MvPolynomial.isHomogeneous_X ℂ 1))

theorem monomial_homogeneous (plus minus : ℕ) : (monomial plus minus).IsHomogeneous (plus + minus) := by
  simpa only [monomial, one_mul] using (plusVariable_homogeneous.pow plus).mul (minusVariable_homogeneous.pow minus)

theorem eigen_pow (derivation : Derivation ℂ Binary.Poly Binary.Poly) (polynomial : Binary.Poly)
    (eigenvalue : ℂ) (eigen : derivation polynomial = eigenvalue • polynomial) (power : ℕ) :
    derivation (polynomial ^ power) = ((power : ℂ) * eigenvalue) • polynomial ^ power := by
  induction power with
  | zero => simp
  | succ power inductionHypothesis =>
      rw [pow_succ, Derivation.leibniz, inductionHypothesis, eigen]
      simp only [smul_eq_mul, mul_smul_comm, Nat.cast_add, Nat.cast_one]
      rw [mul_comm polynomial (polynomial ^ power)]
      module

theorem rotation_monomial (plus minus : ℕ) :
    rotation (monomial plus minus) = (Complex.I * ((minus : ℂ) - plus)) • monomial plus minus := by
  rw [monomial, Derivation.leibniz, eigen_pow rotation plusVariable (-Complex.I) rotation_plus,
    eigen_pow rotation minusVariable Complex.I rotation_minus]
  simp only [smul_eq_mul, mul_smul_comm]
  rw [mul_comm (minusVariable ^ minus) (plusVariable ^ plus)]
  module

theorem raising_monomial (plus minus : ℕ) :
    raising (monomial (plus + 1) minus) = (-2 * (plus + 1 : ℂ)) • monomial plus (minus + 1) := by
  rw [monomial, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow,
    raising_plus, raising_minus]
  simp only [Nat.add_sub_cancel, smul_eq_mul, mul_smul_comm, nsmul_eq_mul]
  simp only [monomial, pow_succ, Algebra.smul_def]
  push_cast
  ring

theorem lowering_monomial (plus minus : ℕ) :
    lowering (monomial plus (minus + 1)) = (-2 * (minus + 1 : ℂ)) • monomial (plus + 1) minus := by
  rw [monomial, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow,
    lowering_plus, lowering_minus]
  simp only [Nat.add_sub_cancel, smul_eq_mul, mul_smul_comm, nsmul_eq_mul]
  simp only [monomial, pow_succ, Algebra.smul_def]
  push_cast
  ring

theorem raising_endpoint (minus : ℕ) : raising (monomial 0 minus) = 0 := by
  simp [monomial, Derivation.leibniz_pow, raising_minus]

theorem lowering_endpoint (plus : ℕ) : lowering (monomial plus 0) = 0 := by
  simp [monomial, Derivation.leibniz_pow, lowering_plus]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PolynomialLadder
