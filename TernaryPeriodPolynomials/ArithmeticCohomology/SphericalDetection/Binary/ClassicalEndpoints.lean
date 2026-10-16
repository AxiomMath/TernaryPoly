module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalEndpoints

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspIntegralAntiextremal_exists_classical (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cuspAffineSmoothValues cusp)
    (member : vector ∈ cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (-(2 * halfWeight)))
    (killed : cuspLoweringOperator cusp (-(2 * halfWeight)) vector = 0) :
    ∃ classicalVector : cuspClassicalVectors cusp halfWeight,
      classicalVector.val.val = cusp.π (atInfinity UpperHalfPlane.J) vector.val := by
  let reflected : cuspAffineSmoothValues cusp := ⟨cusp.π (atInfinity UpperHalfPlane.J) vector.val,
    cuspAffineOrbitVector_reflection_contDiffOn cusp vector.val vector.property⟩
  have reflected_mem : reflected ∈ cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (2 * halfWeight) := by
    refine ⟨cuspReflection_finiteLevel cusp (finiteIntegralGLLevel 2) vector.val member.1, ?_⟩
    simpa only [neg_neg] using cuspReflection_rotation cusp (-(2 * halfWeight)) vector.val member.2
  have reflected_zero : cuspRaisingOperator cusp (2 * halfWeight) reflected = 0 := by
    apply Subtype.ext
    change cuspRaisingVector cusp (2 * halfWeight) (cusp.π (atInfinity UpperHalfPlane.J) vector.val) = 0
    have zero : cuspLoweringVector cusp (-(2 * halfWeight)) vector.val = 0 := congrArg Subtype.val killed
    have equation := cuspRaisingVector_reflection cusp (-(2 * halfWeight)) vector.val
      (cuspAffineSmoothValues_differentiable cusp vector)
    simpa only [neg_neg, zero, map_zero, neg_zero] using equation
  exact cuspIntegralExtremal_exists_classical cusp spherical central_positive halfWeight reflected reflected_mem reflected_zero

theorem binaryRelative_exists_classical_endpoints (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈
      cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (binaryUnitaryWeight degree (-2) position))
    (upper_mem : ∀ position, upper position ∈
      cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (binaryUnitaryWeight degree 2 position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper) :
    ∃ first second : cuspClassicalVectors cusp halfWeight,
      first.val.val = (lower 0).val ∧
      second.val.val = cusp.π (atInfinity UpperHalfPlane.J) (upper (Fin.last (degree + 1))).val := by
  have central_positive := cohomological_centralCharacter_positive cusp cohomological
  obtain ⟨lower_killed, upper_killed⟩ := binaryRelative_endpoint_kernels cusp spherical odd cohomological
    (finiteIntegralGLLevel 2) lower upper lower_mem upper_mem closed
  have lower_weight : binaryUnitaryWeight degree (-2) 0 = 2 * halfWeight := by
    simp only [binaryUnitaryWeight, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero]
    omega
  have upper_weight : binaryUnitaryWeight degree 2 (Fin.last (degree + 1)) = -(2 * halfWeight) := by
    simp only [binaryUnitaryWeight, Fin.val_last]
    omega
  have lower_member := lower_mem 0
  have upper_member := upper_mem (Fin.last (degree + 1))
  rw [lower_weight] at lower_member
  rw [upper_weight] at upper_member
  rw [← weight] at lower_killed
  have opposite : (degree : ℤ) + 3 = -(2 * halfWeight) := by omega
  rw [opposite] at upper_killed
  obtain ⟨first, first_eq⟩ := cuspIntegralExtremal_exists_classical cusp spherical central_positive halfWeight
    (lower 0) lower_member lower_killed
  obtain ⟨second, second_eq⟩ := cuspIntegralAntiextremal_exists_classical cusp spherical central_positive halfWeight
    (upper (Fin.last (degree + 1))) upper_member upper_killed
  exact ⟨first, second, first_eq, second_eq⟩

theorem binaryClassicalEndpoints_finite_detects (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (large : 3 < degree) (cohomological : Cohomological cusp degree)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (lower upper : cuspAffineSmoothValues cusp) (first second : cuspClassicalVectors cusp halfWeight)
    (first_eq : first.val.val = lower.val)
    (second_eq : second.val.val = cusp.π (atInfinity UpperHalfPlane.J) upper.val)
    (vanishes : (∀ real : BinaryRealGL, goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
      (cuspSmoothAction cusp (atInfinity real) first.val) = 0) ∧
      (∀ real : BinaryRealGL, goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
        (cuspSmoothAction cusp (atInfinity real) second.val) = 0)) : lower = 0 ∧ upper = 0 := by
  have central_positive := cohomological_centralCharacter_positive cusp cohomological
  have first_zero := goodLineFiniteVectorIntegral_classical_detects cusp central_positive spherical large cohomological
    halfWeight weight first.val first.property vanishes.1
  have second_zero := goodLineFiniteVectorIntegral_classical_detects cusp central_positive spherical large cohomological
    halfWeight weight second.val second.property vanishes.2
  constructor
  · apply Subtype.ext
    exact first_eq.symm.trans (congrArg Subtype.val first_zero)
  · apply Subtype.ext
    apply (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J)).injective
    exact (second_eq.symm.trans (congrArg Subtype.val second_zero)).trans (map_zero _).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
