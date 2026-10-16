module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointHolomorphic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryEndpointHolomorphicForm (cusp : CuspidalRepresentation) (degree : ℕ)
    (halfWeight : ℤ) (vector : cusp.H) (point : ℂ) : Fin (degree + 2) → cusp.H :=
  fun position => (binaryWeightBasis (degree + 1)).coord position (binaryPointPower (degree + 1) point) •
    cuspWeightedAffineOrbit cusp halfWeight vector point

theorem binaryEndpointHolomorphicForm_eq (cusp : CuspidalRepresentation) (degree : ℕ)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) :
    point.im⁻¹ • binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point =
      binaryEndpointHolomorphicForm cusp degree halfWeight vector point := by
  funext position
  exact binaryAffineOrbitVector_single_weighted cusp degree halfWeight weight vector point positive position

theorem binaryAffineOrbitVector_reflection {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (vector : index → cusp.H) (point : ℂ) (positive : 0 < point.im) :
    binaryAffineOrbitVector cusp basis (binaryHilbertOperator cusp basis UpperHalfPlane.J vector) point =
      binaryHilbertOperator cusp basis UpperHalfPlane.J
        (binaryAffineOrbitVector cusp basis vector (binaryComplexReflection point)) := by
  let upper : UpperHalfPlane := ⟨point, positive⟩
  let reflected : UpperHalfPlane :=
    ⟨binaryComplexReflection point, by rw [binaryComplexReflection_im]; exact positive⟩
  rw [binaryAffineOrbitVector, binaryUpperSectionMatrix_coe upper, invertibleMatrix_coe,
    binaryAffineOrbitVector, binaryUpperSectionMatrix_coe reflected, invertibleMatrix_coe]
  change ((binaryHilbertOperator cusp basis (binarySymmetricSection upper)).comp
      (binaryHilbertOperator cusp basis UpperHalfPlane.J)) vector =
    ((binaryHilbertOperator cusp basis UpperHalfPlane.J).comp
      (binaryHilbertOperator cusp basis (binarySymmetricSection reflected))) vector
  rw [← binaryHilbertOperator_mul cusp spherical, ← binaryHilbertOperator_mul cusp spherical,
    binarySymmetricSection_mul_reflection]

/-- Both complex types of the full plane differential, with all height powers canceled. -/
theorem binaryEndpointDifferential_holomorphicForm (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (degree : ℕ) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) (direction : ℂ) :
    binaryEndpointDifferential cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point direction =
      (2 : ℂ)⁻¹ • (direction • binaryEndpointHolomorphicForm cusp degree halfWeight vector point -
        (starRingEnd ℂ direction) • binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (binaryEndpointHolomorphicForm cusp degree halfWeight vector (binaryComplexReflection point))) := by
  have reflected_positive : 0 < (binaryComplexReflection point).im := by
    rw [binaryComplexReflection_im]
    exact positive
  have reflected_weighted : point.im⁻¹ •
      binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1))
        (binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J (Pi.single 0 vector)) point =
      binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
        (binaryEndpointHolomorphicForm cusp degree halfWeight vector (binaryComplexReflection point)) := by
    rw [binaryAffineOrbitVector_reflection cusp spherical _ _ point positive,
      ← ContinuousLinearMap.map_smul_of_tower]
    congr 1
    rw [← binaryComplexReflection_im point]
    exact binaryEndpointHolomorphicForm_eq cusp degree halfWeight weight vector _ reflected_positive
  change point.im⁻¹ • binaryHilbertOperator cusp (binaryWeightBasis (degree + 1))
    (invertibleMatrix (binaryUpperSectionMatrix point))
    ((2 : ℂ)⁻¹ • (direction • (Pi.single 0 vector : Fin (degree + 2) → cusp.H) -
      (starRingEnd ℂ direction) •
        binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J (Pi.single 0 vector))) = _
  rw [map_smul, map_sub, map_smul, map_smul, smul_comm point.im⁻¹, smul_sub,
    smul_comm point.im⁻¹ direction, smul_comm point.im⁻¹ (starRingEnd ℂ direction)]
  change (2 : ℂ)⁻¹ • (direction •
    (point.im⁻¹ • binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point) -
      (starRingEnd ℂ direction) • (point.im⁻¹ • binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1))
        (binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J (Pi.single 0 vector)) point)) = _
  rw [binaryEndpointHolomorphicForm_eq cusp degree halfWeight weight vector point positive, reflected_weighted]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
