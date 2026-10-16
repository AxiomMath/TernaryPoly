module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.AdelicDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.CuspFormDimension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cohomological_realize_zero_of_upperHalfForm_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (zero : cuspUpperHalfForm cusp weight vector 1 = 0)
    (matrix : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det matrix : ℝ)) :
    cusp.realize vector (atInfinity matrix) = 0 := by
  have orbit_zero (point : UpperHalfPlane) : cuspUpperHalfOrbit cusp vector 1 point = 0 := by
    rw [cuspUpperHalfOrbit_of_holomorphic cusp weight vector 1 point point.im_pos]
    have value := congrFun zero point
    change cuspHolomorphicFunction cusp weight vector 1 point = 0 at value
    rw [value, smul_zero]
  have action := cohomological_upperHalfOrbit_action cohomological weight vector rotation 1 matrix positive
    UpperHalfPlane.I
  rw [orbit_zero, mul_zero] at action
  simpa only [one_mul, cuspUpperHalfOrbit_apply, UpperHalfPlane.coe_I, binaryUpperHalfPoint_I,
    binary_atInfinity_one, mul_one] using action

theorem cuspPrincipalLowestForm_integral_detection
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (weight_positive : 0 < weight) (vector : cuspPrincipalLowestSubmodule cusp weight)
    (zero : ∀ matrix : GeneralLinearGroup (Fin 2) IntegralAdeles,
      cuspPrincipalLowestForm cohomological weight weight_positive
        (cuspPrincipalLowestIntegralAction cusp weight matrix vector) = 0) : vector = 0 := by
  apply Subtype.ext
  apply cusp.injective
  funext argument
  obtain ⟨rational, realMatrix, integralMatrix, positive, decomposition⟩ :=
    binary_adelic_rational_positive_integral argument
  let translated := cuspPrincipalLowestIntegralAction cusp weight integralMatrix vector
  have form_zero : cuspUpperHalfForm cusp weight translated.val 1 = 0 := by
    funext point
    exact congrArg (fun form : CuspForm binaryRealPrincipalLevel (weight : ℤ) => form point)
      (zero integralMatrix)
  have scalar_zero := cohomological_realize_zero_of_upperHalfForm_zero cohomological weight translated.val
    translated.property.2.1 form_zero realMatrix positive
  change cusp.realize vector.val argument = cusp.realize 0 argument
  rw [map_zero]
  change cusp.realize vector.val argument = 0
  rw [decomposition, mul_assoc, cusp.leftRational]
  have equivariant := cusp.equivariant (atFinite (GeneralLinearGroup.map integralEmbedding integralMatrix))
    vector.val (atInfinity realMatrix)
  change cusp.realize translated.val (atInfinity realMatrix) =
    cusp.realize vector.val (atInfinity realMatrix * atFinite (GeneralLinearGroup.map integralEmbedding integralMatrix))
    at equivariant
  exact equivariant.symm.trans scalar_zero

theorem cuspPrincipalLowestForm_finite_detection
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (weight_positive : 0 < weight) :
    ∃ representatives : Finset (GeneralLinearGroup (Fin 2) IntegralAdeles),
      ∀ vector : cuspPrincipalLowestSubmodule cusp weight,
        (∀ matrix ∈ representatives, cuspPrincipalLowestForm cohomological weight weight_positive
          (cuspPrincipalLowestIntegralAction cusp weight matrix vector) = 0) → vector = 0 := by
  obtain ⟨representatives, covers⟩ := binary_integral_finite_representatives
  refine ⟨representatives, ?_⟩
  intro vector zero
  apply cuspPrincipalLowestForm_integral_detection cohomological weight weight_positive vector
  intro matrix
  obtain ⟨representative, member, same⟩ := covers matrix
  rw [← cuspPrincipalLowestIntegralAction_same_reduction cusp weight representative matrix same]
  exact zero representative member

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
