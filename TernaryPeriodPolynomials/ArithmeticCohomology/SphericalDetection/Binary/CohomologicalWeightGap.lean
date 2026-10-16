module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.OrbitWeightOrthogonality
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalHolomorphic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspWeightedAffineOrbit_finite_translate (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H) (finite : BinaryFiniteGL) (point : ℂ) :
    cuspWeightedAffineOrbit cusp halfWeight (cusp.π (atFinite finite) vector) point =
      cuspUnitaryOperator cusp (atFinite finite) (cuspWeightedAffineOrbit cusp halfWeight vector point) := by
  rw [cuspWeightedAffineOrbit, cuspWeightedAffineOrbit, ContinuousLinearMap.map_smul_of_tower]
  exact congrArg (fun value : cusp.H => point.im ^ halfWeight • value)
    (congrFun (cuspAffineOrbitVector_intertwiner cusp (cuspUnitaryOperator cusp (atFinite finite))
      (cuspFiniteOperator_real cusp finite) vector) point)

theorem cuspWeightedAffineOrbit_finite_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H) (finite : BinaryFiniteGL)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight (cusp.π (atFinite finite) vector))
      UpperHalfPlane.upperHalfPlaneSet := by
  have equality : cuspWeightedAffineOrbit cusp halfWeight (cusp.π (atFinite finite) vector) =
      (cuspUnitaryOperator cusp (atFinite finite)) ∘ cuspWeightedAffineOrbit cusp halfWeight vector := by
    funext point
    exact cuspWeightedAffineOrbit_finite_translate cusp halfWeight vector finite point
  rw [equality]
  exact (cuspUnitaryOperator cusp (atFinite finite)).differentiable.comp_differentiableOn holomorphic

theorem cuspHolomorphic_weight_gap (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.H) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (test : cusp.H) (testWeight : ℤ) (above : 2 * halfWeight < testWeight) (below : testWeight < -(2 * halfWeight))
    (test_rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) test =
      (angle : ℂ) ^ testWeight • test) : test = 0 := by
  by_contra test_nonzero
  have functional_nonzero : innerSL ℂ test ≠ 0 := by
    intro zero
    have self_zero := congrArg (fun functional : cusp.H →L[ℂ] ℂ => functional test) zero
    exact test_nonzero (inner_self_eq_zero.mp self_zero)
  obtain ⟨matrix, detected⟩ := cusp_exists_translate_detected cusp (innerSL ℂ test) functional_nonzero vector nonzero
  obtain ⟨real, finite, split⟩ := binaryAdelic_exists_real_finite matrix
  apply detected
  rw [split, map_mul, Module.End.mul_apply]
  apply cuspRealOrbit_inner_weight_gap cusp spherical central_positive halfWeight (cusp.π (atFinite finite) vector)
    ?_ (cuspWeightedAffineOrbit_finite_holomorphic cusp halfWeight vector finite holomorphic)
    test testWeight above below test_rotation real
  intro angle
  have commute := cuspFiniteOperator_real cusp finite (binaryRotations angle) vector
  change cusp.π (atFinite finite) (cusp.π (atInfinity (binaryRotations angle)) vector) =
    cusp.π (atInfinity (binaryRotations angle)) (cusp.π (atFinite finite) vector) at commute
  rw [← commute, rotation, map_smul]

theorem cohomological_cusp_weight_gap (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (vector : cusp.H) (weight : ℤ) (above : -((degree : ℤ) + 3) < weight) (below : weight < (degree : ℤ) + 3)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ weight • vector) : vector = 0 := by
  obtain ⟨halfWeight, generator, generator_weight, generator_nonzero, _, generator_rotation, _, holomorphic⟩ :=
    cohomological_exists_spherical_holomorphic cusp spherical odd cohomological
  exact cuspHolomorphic_weight_gap cusp spherical
    (cohomological_centralCharacter_positive cusp cohomological) halfWeight generator.val
      (fun zero => generator_nonzero (Subtype.ext zero)) generator_rotation holomorphic vector weight
      (by omega) (by omega) rotation

theorem cohomological_boundary_weight_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL) (vector : cuspFiniteWeightValues cusp level (degree + 1 : ℕ)) : vector = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact cohomological_cusp_weight_gap cusp spherical odd cohomological vector.val.val (degree + 1 : ℕ)
    (by omega) (by omega) vector.property.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
