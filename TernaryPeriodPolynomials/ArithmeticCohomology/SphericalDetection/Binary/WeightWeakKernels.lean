module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FullLadderProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeakKernels
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderDecomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspWeight_raising_tests (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (weight + 2) • vector)
    (annihilates : ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
      inner ℂ vector (cuspRaisingOperator cusp weight smooth).val = 0)
    (test : cusp.smooth) (fixed : test.val ∈ cuspFiniteLevelValues cusp level) :
    inner ℂ (cuspRaisingVector cusp (weight + 2) test.val) vector = 0 := by
  let projected : cuspAffineSmoothValues cusp :=
    ⟨cuspRotationProjection cusp weight test.val, cuspRotationProjection_affineSmooth cusp weight test⟩
  have member : projected ∈ cuspFiniteWeightValues cusp level weight :=
    ⟨cuspRotationProjection_finiteLevel cusp level weight test.val fixed,
      cuspRotationProjection_rotation cusp weight test.val⟩
  have equation := annihilates projected member
  change inner ℂ vector (cuspRaisingVector cusp weight (cuspRotationProjection cusp weight test.val)) = 0 at equation
  rw [cuspRaisingVector_projection, cuspRotationProjection_inner_weight cusp (weight + 2) vector _ rotation] at equation
  have flipped := inner_eq_zero_symm.mp equation
  rwa [cuspFullRaisingVector_inner_weight cusp (weight + 2) test.val vector
    (cuspMatrixOrbit_smooth_differentiable cusp test) rotation] at flipped

theorem cuspWeightFiniteLevel_raising_tests (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (level_open : IsOpen (level : Set BinaryFiniteGL)) (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (weight : ℤ) (vector : cusp.H) (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2))
    (annihilates : ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
      inner ℂ vector (cuspRaisingOperator cusp weight smooth).val = 0)
    (test : cusp.smooth) : inner ℂ (cuspRaisingVector cusp (weight + 2) test.val) vector = 0 :=
  cuspFiniteLevel_raising_tests cusp level level_open level_compact (weight + 2) vector member.1
    (cuspWeight_raising_tests cusp level weight vector member.2 annihilates) test

theorem cuspWeightWeakLoweringKernel_exists_spherical (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL)) (weight halfWeight : ℤ)
    (weight_eq : weight + 2 = 2 * halfWeight) (vector : cusp.H) (nonzero : vector ≠ 0)
    (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2))
    (annihilates : ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level weight →
      inner ℂ vector (cuspRaisingOperator cusp weight smooth).val = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ cuspSphericalValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * (-halfWeight)) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp (-halfWeight) spherical_vector.val) UpperHalfPlane.upperHalfPlaneSet := by
  apply cuspWeakLoweringKernel_exists_spherical cusp spherical central_positive halfWeight vector nonzero
  · simpa only [weight_eq] using member.2
  · simpa only [weight_eq] using
      cuspWeightFiniteLevel_raising_tests cusp level level_open level_compact weight vector member annihilates

end TernaryPeriodPolynomials.SphericalDetection.Helpers
