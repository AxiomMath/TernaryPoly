module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Ladder

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientDerivative
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.StandardCoefficient

noncomputable def exponents (first second : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 first + Finsupp.single 1 second

theorem exponents_zero (first second : ℕ) : exponents first second 0 = first := by simp [exponents]

theorem exponents_one (first second : ℕ) : exponents first second 1 = second := by simp [exponents]

theorem exponents_degree (first second : ℕ) : (exponents first second).degree = first + second := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two, exponents]

theorem exponents_reconstruct (monomial : Fin 2 →₀ ℕ) : exponents (monomial 0) (monomial 1) = monomial := by
  ext position
  fin_cases position <;> simp [exponents]

noncomputable def standardMonomial (first second : ℕ) : Binary.Poly := MvPolynomial.X 0 ^ first * MvPolynomial.X 1 ^ second

theorem standardMonomial_eq (first second : ℕ) : standardMonomial first second = MvPolynomial.monomial (exponents first second) 1 := by
  simp only [standardMonomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one, exponents]

theorem basisMonomial_eq (degree : ℕ) (index : Index degree) :
    (basisMonomial index).val = standardMonomial (index.val 0) (index.val 1) := by
  rw [standardMonomial_eq, exponents_reconstruct]
  rfl

theorem diagonal_first : PolynomialLadder.diagonal (MvPolynomial.X 0) = (-1 : ℂ) • MvPolynomial.X 0 := by
  simp [PolynomialLadder.diagonal, PolynomialDerivative.variableDerivative, complexDirection,
    diagonalMatrix, Binary.linearForm]

theorem diagonal_second : PolynomialLadder.diagonal (MvPolynomial.X 1) = (1 : ℂ) • MvPolynomial.X 1 := by
  simp [PolynomialLadder.diagonal, PolynomialDerivative.variableDerivative, complexDirection,
    diagonalMatrix, Binary.linearForm]

theorem diagonal_monomial (first second : ℕ) :
    PolynomialLadder.diagonal (standardMonomial first second) = ((second : ℂ) - first) • standardMonomial first second := by
  rw [standardMonomial, Derivation.leibniz,
    PolynomialLadder.eigen_pow PolynomialLadder.diagonal (MvPolynomial.X 0) (-1) diagonal_first,
    PolynomialLadder.eigen_pow PolynomialLadder.diagonal (MvPolynomial.X 1) 1 diagonal_second]
  simp only [smul_eq_mul, mul_smul_comm]
  rw [mul_comm (MvPolynomial.X 1 ^ second) (MvPolynomial.X 0 ^ first)]
  module

theorem coefficientDerivative_diagonal (degree : ℕ) (index other : Index (degree + 1)) :
    coefficientDerivative degree diagonalMatrix index other =
      if other = index then ((index.val 1 : ℂ) - index.val 0) else 0 := by
  classical
  rw [coefficientDerivative_eq, PolynomialLadder.polynomialOperator_diagonal]
  change (PolynomialLadder.diagonal (basisMonomial other).val).coeff index.val = _
  rw [basisMonomial_eq, diagonal_monomial, ← basisMonomial_eq]
  simp only [MvPolynomial.coeff_smul, basisMonomial, MvPolynomial.coeff_monomial, Subtype.val_inj, smul_eq_mul]
  by_cases same : other = index
  · subst other
    simp
  · simp [same]

theorem operator_diagonal_coordinate (data : CuspidalRepresentation) (degree : ℕ)
    (vectors : Vectors data degree) (index : Index (degree + 1)) :
    operator data degree diagonalMatrix vectors index = diagonalOperator data (vectors index) +
      ((index.val 1 : ℂ) - index.val 0) • vectors index := by
  classical
  change directionalOperator data diagonalMatrix (vectors index) +
    (∑ other : Index (degree + 1), coefficientDerivative degree diagonalMatrix index other • vectors other) = _
  simp only [coefficientDerivative_diagonal, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem real_eigen_zero (data : CuspidalRepresentation) (direction : BinaryMatrix) (vector : data.smooth)
    (eigenvalue : ℝ) (nonzero : eigenvalue ≠ 0)
    (eigen : directionalOperator data direction vector = (eigenvalue : ℂ) • vector) : vector = 0 := by
  by_contra vectorNonzero
  have normNonzero : (‖vector.val‖ : ℂ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    apply Complex.ofReal_ne_zero.mpr
    exact norm_ne_zero_iff.mpr (fun vanishing => vectorNonzero (Subtype.ext vanishing))
  have equality := LieDifferentiation.directionalOperator_inner data vector vector direction
  rw [eigen] at equality
  change inner ℂ vector.val ((eigenvalue : ℂ) • vector.val) +
    inner ℂ ((eigenvalue : ℂ) • vector.val) vector.val = 0 at equality
  rw [inner_smul_right, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K] at equality
  have scalarEquality : (eigenvalue : ℂ) + eigenvalue = 0 := by
    apply mul_right_cancel₀ normNonzero
    rw [add_mul, zero_mul]
    exact equality
  have realEquality : eigenvalue + eigenvalue = 0 := by exact_mod_cast scalarEquality
  exact nonzero (by linarith)

theorem unbalanced_coordinate_zero (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (invariant : operator data degree diagonalMatrix vectors = 0)
    (index : Index (degree + 1)) (unbalanced : index.val 0 ≠ index.val 1) : vectors index = 0 := by
  apply real_eigen_zero data diagonalMatrix (vectors index) ((index.val 0 : ℝ) - index.val 1)
    (sub_ne_zero.mpr (by exact_mod_cast unbalanced))
  have equality := congrFun invariant index
  rw [operator_diagonal_coordinate] at equality
  change diagonalOperator data (vectors index) + ((index.val 1 : ℂ) - index.val 0) • vectors index = 0 at equality
  calc
    directionalOperator data diagonalMatrix (vectors index) = -(((index.val 1 : ℂ) - index.val 0) • vectors index) :=
      eq_neg_of_add_eq_zero_left equality
    _ = _ := by
      push_cast
      module

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.StandardCoefficient
