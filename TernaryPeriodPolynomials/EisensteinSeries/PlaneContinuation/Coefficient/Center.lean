module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Invariants

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientDerivative
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.StandardCoefficient TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientCenter

noncomputable def euler : Derivation ℂ Binary.Poly Binary.Poly :=
  PolynomialDerivative.variableDerivative (-complexDirection (1 : BinaryMatrix))

theorem euler_variable (position : Fin 2) : euler (MvPolynomial.X position) = (-1 : ℂ) • MvPolynomial.X position := by
  fin_cases position <;>
    simp [euler, PolynomialDerivative.variableDerivative, complexDirection, Binary.linearForm]

theorem euler_monomial (first second : ℕ) : euler (standardMonomial first second) =
    (-((first : ℂ) + second)) • standardMonomial first second := by
  rw [standardMonomial, Derivation.leibniz,
    PolynomialLadder.eigen_pow euler (MvPolynomial.X 0) (-1) (euler_variable 0),
    PolynomialLadder.eigen_pow euler (MvPolynomial.X 1) (-1) (euler_variable 1)]
  simp only [smul_eq_mul, mul_smul_comm]
  rw [mul_comm (MvPolynomial.X 1 ^ second) (MvPolynomial.X 0 ^ first)]
  module

theorem polynomialOperator_identity_basis (degree : ℕ) (index : Index (degree + 1)) :
    polynomialOperator degree (1 : BinaryMatrix) (basisMonomial index).val = 0 := by
  change ((((degree : ℂ) + 1) / 2 * (((1 : BinaryMatrix) 0 0 + (1 : BinaryMatrix) 1 1 : ℝ) : ℂ)) •
    (basisMonomial index).val + euler (basisMonomial index).val) = 0
  rw [basisMonomial_eq, euler_monomial]
  have degreeEquality : (index.val 0 : ℂ) + index.val 1 = (degree : ℂ) + 1 := by
    exact_mod_cast CoefficientCoordinates.index_degree (degree + 1) index
  rw [degreeEquality]
  norm_num
  module

theorem coefficientDerivative_identity (degree : ℕ) (index other : Index (degree + 1)) :
    coefficientDerivative degree (1 : BinaryMatrix) index other = 0 := by
  rw [coefficientDerivative_eq, polynomialOperator_identity_basis, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem operator_identity {degree : ℕ} (data : InducingData degree) :
    operator data.cusp degree (1 : BinaryMatrix) = 0 := by
  apply LinearMap.ext
  intro vectors
  funext index
  change directionalOperator data.cusp 1 (vectors index) +
    ∑ other : Index (degree + 1), coefficientDerivative degree 1 index other • vectors other = 0
  simp only [CentralDifferentiation.directionalOperator_identity data, coefficientDerivative_identity,
    zero_smul, Finset.sum_const_zero, add_zero]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientCenter
