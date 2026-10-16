module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FinitePeriodDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PrimitiveSegment
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.ArithmeticPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspFiniteEndpointPeriodIntegral (degree : ℕ) (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) (point : ℂ) : ℂ :=
  ∫ parameter : ℝ in 0..1,
    let position := Complex.I + parameter • (point - Complex.I)
    (point - Complex.I) * ((position.im ^ halfWeight : ℝ) : ℂ) *
      goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
        (cuspSmoothAction cusp (atInfinity (invertibleMatrix (binaryUpperSectionMatrix position))) vector) *
      functional (binaryPointPower (degree + 1) position)

theorem cuspClassicalFiniteAverageFamily_scalar (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) (point : UpperHalfPlane) :
    cuspClassicalFormMap cusp halfWeight negative
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent vector) point =
        point.im ^ halfWeight •
          cuspClassicalFiniteAverage cusp halfWeight exponent convergent vector (binarySymmetricSection point) := by
  rw [cuspClassicalFiniteAverageFamily_apply cusp central_positive halfWeight negative exponent convergent]
  have form_value := congrFun (cuspClassicalFormMap_coe cusp halfWeight negative
    (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent vector)) point
  change _ = point.im ^ halfWeight • cusp.realize
    (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent vector).val
      (1 * atInfinity (invertibleMatrix (binaryUpperSectionMatrix point))) at form_value
  rw [one_mul, binaryUpperSectionMatrix_coe point, invertibleMatrix_coe] at form_value
  exact form_value.trans (congrArg (fun value : ℂ => point.im ^ halfWeight • value)
    (congrFun (cuspClassicalFiniteAverageOperator_realization cusp central_positive halfWeight negative
      exponent convergent vector) (binarySymmetricSection point)))

theorem cuspClassicalFiniteAverageFamily_endpoint_scalar (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0)
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re)
    (vector : cuspClassicalVectors cusp halfWeight) (point : UpperHalfPlane) :
    cuspClassicalFormMap cusp halfWeight negative
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint) vector) point =
      point.im ^ halfWeight • goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
        (cuspSmoothAction cusp (atInfinity (binarySymmetricSection point)) vector.val) := by
  rw [cuspClassicalFiniteAverageFamily_scalar cusp central_positive halfWeight negative _ convergent,
    cuspClassicalFiniteAverage_endpoint]

theorem cuspClassicalFiniteAverageFamily_endpoint_primitive (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0)
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re)
    (vector : cuspClassicalVectors cusp halfWeight)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) (point : ℂ) (positive : 0 < point.im) :
    functional (classicalBinaryPrimitive
      (cuspClassicalFormMap cusp halfWeight negative
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
          ((degree : ℂ) / 2 + 3 + cohomologicalPoint) vector)) (degree + 1) point) =
      cuspFiniteEndpointPeriodIntegral degree cusp halfWeight vector.val functional point := by
  rw [classicalBinaryPrimitive_segment_integral _ _ _ point positive, cuspFiniteEndpointPeriodIntegral]
  apply intervalIntegral.integral_congr
  intro parameter member
  dsimp only
  let position : UpperHalfPlane := ⟨Complex.I + parameter • (point - Complex.I),
    upperHalfPlane_straightPath ⟨point, positive⟩ (by simpa only [Set.uIcc_of_le zero_le_one] using member)⟩
  have position_eq : UpperHalfPlane.ofComplex (Complex.I + parameter • (point - Complex.I)) = position :=
    UpperHalfPlane.ofComplex_apply position
  rw [classicalBinaryForm, map_smul, smul_eq_mul, position_eq,
    cuspClassicalFiniteAverageFamily_endpoint_scalar degree cusp central_positive halfWeight negative convergent]
  have section_eq : invertibleMatrix (binaryUpperSectionMatrix (position : ℂ)) = binarySymmetricSection position := by
    rw [binaryUpperSectionMatrix_coe position, invertibleMatrix_coe]
  change (point - Complex.I) * ((position.im ^ halfWeight •
    goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
      (cuspSmoothAction cusp (atInfinity (binarySymmetricSection position)) vector.val)) *
    functional (binaryPointPower (degree + 1) position)) = _
  change _ = (point - Complex.I) * ((position.im ^ halfWeight : ℝ) : ℂ) *
    goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
      (cuspSmoothAction cusp (atInfinity (invertibleMatrix (binaryUpperSectionMatrix (position : ℂ)))) vector.val) *
    functional (binaryPointPower (degree + 1) position)
  rw [section_eq, Complex.real_smul]
  ring

theorem cuspClassicalFiniteAverageFamily_endpoint_arithmetic_value (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0)
    (weight_eq : -2 * halfWeight = ((degree + 1 : ℕ) : ℤ) + 2) (even : Even (degree + 1))
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re)
    (vector : cuspClassicalVectors cusp halfWeight) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    functional (classicalArithmeticCocycle
      (cuspClassicalFormMap cusp halfWeight negative
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
          ((degree : ℂ) / 2 + 3 + cohomologicalPoint) vector)) (degree + 1) weight_eq even twist parity sign matrix) =
      (let point : ℂ := ((GeneralLinearGroup.map (Int.castRingHom ℝ) matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ)
       (2 : ℂ)⁻¹ * (cuspFiniteEndpointPeriodIntegral degree cusp halfWeight vector.val functional point +
         (-1 : ℂ) ^ parity * cuspFiniteEndpointPeriodIntegral degree cusp halfWeight vector.val
           (functional.comp (binaryParityReflection (degree + 1))) (binaryComplexReflection point))) := by
  let point : UpperHalfPlane := GeneralLinearGroup.map (Int.castRingHom ℝ) matrix • UpperHalfPlane.I
  let form := cuspClassicalFormMap cusp halfWeight negative
    (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
      ((degree : ℂ) / 2 + 3 + cohomologicalPoint) vector)
  rw [classicalArithmeticCocycle_apply, classicalParityPrimitive, map_smul, map_add, map_smul, smul_eq_mul, smul_eq_mul]
  change (2 : ℂ)⁻¹ * (functional (classicalBinaryPrimitive form (degree + 1) point) + (-1 : ℂ) ^ parity *
    (functional.comp (binaryParityReflection (degree + 1)))
      (classicalBinaryPrimitive form (degree + 1) (binaryComplexReflection point))) = _
  rw [cuspClassicalFiniteAverageFamily_endpoint_primitive degree cusp central_positive halfWeight negative
      convergent vector functional point point.im_pos,
    cuspClassicalFiniteAverageFamily_endpoint_primitive degree cusp central_positive halfWeight negative
      convergent vector (functional.comp (binaryParityReflection (degree + 1))) (binaryComplexReflection point)
      (by rw [binaryComplexReflection_im]; exact point.im_pos)]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
