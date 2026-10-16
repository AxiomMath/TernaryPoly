module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PolynomialLadder

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientDerivative
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientTensor

noncomputable def tensor (data : CuspidalRepresentation) (degree : ℕ) (polynomial : Binary.Poly)
    (vector : data.smooth) : Vectors data degree :=
  fun index => polynomial.coeff index.val • vector

theorem tensor_add (data : CuspidalRepresentation) (degree : ℕ) (first second : Binary.Poly)
    (vector : data.smooth) : tensor data degree (first + second) vector =
      tensor data degree first vector + tensor data degree second vector := by
  funext index
  exact add_smul _ _ _

theorem tensor_smul (data : CuspidalRepresentation) (degree : ℕ) (scalar : ℂ) (polynomial : Binary.Poly)
    (vector : data.smooth) : tensor data degree (scalar • polynomial) vector = scalar • tensor data degree polynomial vector := by
  funext index
  simp only [tensor, MvPolynomial.coeff_smul, smul_eq_mul, mul_smul, Pi.smul_apply]

theorem tensor_zero (data : CuspidalRepresentation) (degree : ℕ) (vector : data.smooth) :
    tensor data degree 0 vector = 0 := by
  funext index
  simp [tensor]

theorem tensor_vector_add (data : CuspidalRepresentation) (degree : ℕ) (polynomial : Binary.Poly)
    (first second : data.smooth) : tensor data degree polynomial (first + second) =
      tensor data degree polynomial first + tensor data degree polynomial second := by
  funext index
  exact smul_add _ _ _

theorem tensor_vector_smul (data : CuspidalRepresentation) (degree : ℕ) (polynomial : Binary.Poly)
    (scalar : ℂ) (vector : data.smooth) : tensor data degree polynomial (scalar • vector) =
      scalar • tensor data degree polynomial vector := by
  funext index
  exact smul_comm _ _ _

theorem polynomialOperator_coefficients (degree : ℕ) (direction : BinaryMatrix)
    (polynomial : Binary.Poly) (homogeneous : polynomial.IsHomogeneous (degree + 1)) (index : Index (degree + 1)) :
    ∑ other : Index (degree + 1),
      (polynomialOperator degree direction (basisMonomial other).val).coeff index.val *
        polynomial.coeff other.val =
      (polynomialOperator degree direction polynomial).coeff index.val := by
  have reconstruction := polynomial_reconstruct (degree + 1) ⟨polynomial, homogeneous⟩
  have equality := congrArg (fun value : Binary.HomogeneousPoly (degree + 1) =>
    (polynomialOperator degree direction value.val).coeff index.val) reconstruction
  change (polynomialOperator degree direction
    (∑ other : Index (degree + 1), polynomial.coeff other.val • basisMonomial other).val).coeff index.val = _ at equality
  simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm] using equality

/-- The actual infinitesimal coefficient action satisfies the tensor product rule. -/
theorem operator_tensor (data : CuspidalRepresentation) (degree : ℕ) (direction : BinaryMatrix)
    (polynomial : Binary.Poly) (homogeneous : polynomial.IsHomogeneous (degree + 1)) (vector : data.smooth) :
    operator data degree direction (tensor data degree polynomial vector) =
      tensor data degree polynomial (directionalOperator data direction vector) +
        tensor data degree (polynomialOperator degree direction polynomial) vector := by
  funext index
  change directionalOperator data direction (polynomial.coeff index.val • vector) +
    ∑ other : Index (degree + 1), coefficientDerivative degree direction index other •
      (polynomial.coeff other.val • vector) = _
  simp only [map_smul, coefficientDerivative_eq, ← mul_smul, ← Finset.sum_smul,
    polynomialOperator_coefficients degree direction polynomial homogeneous index]
  rfl

theorem rotation_tensor (data : CuspidalRepresentation) (degree plus minus : ℕ)
    (degreeEquality : plus + minus = degree + 1) (vector : data.smooth) :
    operator data degree LieOperators.rotationMatrix (tensor data degree (PolynomialLadder.monomial plus minus) vector) =
      tensor data degree (PolynomialLadder.monomial plus minus) (LieOperators.rotationOperator data vector) +
        (Complex.I * ((minus : ℂ) - plus)) • tensor data degree (PolynomialLadder.monomial plus minus) vector := by
  have homogeneous : (PolynomialLadder.monomial plus minus).IsHomogeneous (degree + 1) :=
    degreeEquality ▸ PolynomialLadder.monomial_homogeneous plus minus
  rw [operator_tensor data degree _ _ homogeneous, PolynomialLadder.polynomialOperator_rotation]
  change _ + tensor data degree (PolynomialLadder.rotation (PolynomialLadder.monomial plus minus)) vector = _
  rw [PolynomialLadder.rotation_monomial, tensor_smul]
  rfl

theorem raising_tensor (data : CuspidalRepresentation) (degree : ℕ) (polynomial : Binary.Poly)
    (homogeneous : polynomial.IsHomogeneous (degree + 1)) (vector : data.smooth) :
    (operator data degree LieOperators.diagonalMatrix - Complex.I • operator data degree LieOperators.symmetricMatrix)
        (tensor data degree polynomial vector) =
      tensor data degree polynomial (LieOperators.raising data vector) +
        tensor data degree (PolynomialLadder.raising polynomial) vector := by
  change operator data degree LieOperators.diagonalMatrix (tensor data degree polynomial vector) -
    Complex.I • operator data degree LieOperators.symmetricMatrix (tensor data degree polynomial vector) = _
  rw [operator_tensor data degree _ _ homogeneous, operator_tensor data degree _ _ homogeneous,
    PolynomialLadder.polynomialOperator_diagonal, PolynomialLadder.polynomialOperator_symmetric]
  funext index
  simp only [tensor, LieOperators.raising, LieOperators.diagonalOperator, LieOperators.symmetricOperator,
    PolynomialLadder.raising, Derivation.sub_apply, Derivation.smul_apply, Derivation.coeFn_coe,
    LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul, smul_sub, sub_smul,
    smul_add, smul_smul]
  module

theorem lowering_tensor (data : CuspidalRepresentation) (degree : ℕ) (polynomial : Binary.Poly)
    (homogeneous : polynomial.IsHomogeneous (degree + 1)) (vector : data.smooth) :
    (operator data degree LieOperators.diagonalMatrix + Complex.I • operator data degree LieOperators.symmetricMatrix)
        (tensor data degree polynomial vector) =
      tensor data degree polynomial (LieOperators.lowering data vector) +
        tensor data degree (PolynomialLadder.lowering polynomial) vector := by
  change operator data degree LieOperators.diagonalMatrix (tensor data degree polynomial vector) +
    Complex.I • operator data degree LieOperators.symmetricMatrix (tensor data degree polynomial vector) = _
  rw [operator_tensor data degree _ _ homogeneous, operator_tensor data degree _ _ homogeneous,
    PolynomialLadder.polynomialOperator_diagonal, PolynomialLadder.polynomialOperator_symmetric]
  funext index
  simp only [tensor, LieOperators.lowering, LieOperators.diagonalOperator, LieOperators.symmetricOperator,
    PolynomialLadder.lowering, Derivation.add_apply, Derivation.smul_apply, Derivation.coeFn_coe,
    LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_smul, smul_eq_mul, smul_add, add_smul,
    smul_smul]
  module

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientTensor
