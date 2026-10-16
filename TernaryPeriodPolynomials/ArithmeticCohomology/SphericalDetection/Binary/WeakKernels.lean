module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeakOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ReflectionLadders
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspReflection_involution (cusp : CuspidalRepresentation) (vector : cusp.H) :
    cusp.π (atInfinity UpperHalfPlane.J) (cusp.π (atInfinity UpperHalfPlane.J) vector) = vector := by
  change (cusp.π (atInfinity UpperHalfPlane.J) * cusp.π (atInfinity UpperHalfPlane.J)) vector = vector
  rw [← map_mul, ← atInfinity_mul, ← pow_two, UpperHalfPlane.J_sq, atInfinity_one, map_one]
  rfl

theorem cuspReflection_inner (cusp : CuspidalRepresentation) (first second : cusp.H) :
    inner ℂ (cusp.π (atInfinity UpperHalfPlane.J) first) second =
      inner ℂ first (cusp.π (atInfinity UpperHalfPlane.J) second) := by
  have identity := (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J)).inner_map_map
    first (cusp.π (atInfinity UpperHalfPlane.J) second)
  change inner ℂ (cusp.π (atInfinity UpperHalfPlane.J) first)
    (cusp.π (atInfinity UpperHalfPlane.J) (cusp.π (atInfinity UpperHalfPlane.J) second)) = _ at identity
  rwa [cuspReflection_involution] at identity

theorem cuspWeakLoweringKernel_reflection (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val) vector = 0)
    (test : cusp.smooth) :
    inner ℂ (cuspLoweringVector cusp (2 * (-halfWeight)) test.val)
      (cusp.π (atInfinity UpperHalfPlane.J) vector) = 0 := by
  let reflected : cusp.smooth := ⟨cusp.π (atInfinity UpperHalfPlane.J) test.val,
    cusp.smooth_stable _ _ test.property⟩
  have equation := annihilates reflected
  have regular := cuspAffineSmoothValues_differentiable cusp ⟨test.val, cuspSmooth_le_affineSmooth cusp test.property⟩
  have reflection := cuspRaisingVector_reflection cusp (2 * (-halfWeight)) test.val regular
  have opposite : -(2 * (-halfWeight)) = 2 * halfWeight := by ring
  rw [opposite] at reflection
  change inner ℂ (cuspRaisingVector cusp (2 * halfWeight)
    (cusp.π (atInfinity UpperHalfPlane.J) test.val)) vector = 0 at equation
  rw [reflection, inner_neg_left, cuspReflection_inner, neg_eq_zero] at equation
  exact equation

theorem cuspWeakLoweringKernel_analytic (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val) vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  have reflected := cuspWeakRaisingKernel_analytic cusp spherical (-halfWeight)
    (cusp.π (atInfinity UpperHalfPlane.J) vector) (cuspWeakLoweringKernel_reflection cusp halfWeight vector annihilates)
  have reflected_regular : ContDiffOn ℝ ⊤
      (cuspAffineOrbitVector cusp (cusp.π (atInfinity UpperHalfPlane.J) vector)) UpperHalfPlane.upperHalfPlaneSet :=
    reflected.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  have regular := cuspAffineOrbitVector_reflection_contDiffOn cusp _ reflected_regular
  rw [cuspReflection_involution] at regular
  intro point positive
  exact (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive)).analyticAt

theorem cuspWeakLoweringKernel_lowering_zero_of_smooth_tests (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val) vector = 0) :
    cuspLoweringVector cusp (2 * halfWeight) vector = 0 := by
  have analytic := cuspWeakLoweringKernel_analytic cusp spherical halfWeight vector annihilates
  have regular : vector ∈ cuspAffineSmoothValues cusp :=
    analytic.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  apply (sphericalCusp_smooth_dense cusp spherical).eq_zero_of_inner_right ℂ
  intro test member
  have skew := cuspRaisingOperator_skew cusp (2 * halfWeight)
    ⟨test, cuspSmooth_le_affineSmooth cusp member⟩ ⟨vector, regular⟩
  change inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test) vector +
    inner ℂ test (cuspLoweringVector cusp (2 * halfWeight) vector) = 0 at skew
  rw [annihilates ⟨test, member⟩, zero_add] at skew
  exact skew

theorem cuspWeakLoweringKernel_exists_spherical (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.H) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ (2 * halfWeight) • vector)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val) vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ cuspSphericalValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * (-halfWeight)) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * (-halfWeight)) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp (-halfWeight) spherical_vector.val) UpperHalfPlane.upperHalfPlaneSet := by
  exact cusp_exists_spherical_smooth_of_lowering_zero cusp spherical central_positive vector halfWeight nonzero rotation
    ((cuspWeakLoweringKernel_analytic cusp spherical halfWeight vector annihilates).contDiffOn
      UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn)
    (cuspWeakLoweringKernel_lowering_zero_of_smooth_tests cusp spherical halfWeight vector annihilates)

theorem cuspFiniteLevel_raising_tests (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (level_open : IsOpen (level : Set BinaryFiniteGL)) (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (weight : ℤ) (vector : cusp.H) (fixed : vector ∈ cuspFiniteLevelValues cusp level)
    (annihilates : ∀ test : cusp.smooth, test.val ∈ cuspFiniteLevelValues cusp level →
      inner ℂ (cuspRaisingVector cusp weight test.val) vector = 0)
    (test : cusp.smooth) : inner ℂ (cuspRaisingVector cusp weight test.val) vector = 0 := by
  have projected := annihilates
    ⟨cuspFiniteProjection cusp level test.val, cuspFiniteProjection_smooth cusp level level_open level_compact test.val test.property⟩
    (cuspFiniteProjection_mem cusp level test.val)
  change inner ℂ (cuspRaisingVector cusp weight (cuspFiniteProjection cusp level test.val)) vector = 0 at projected
  rw [cuspFiniteProjection_raising cusp level weight test.val
    (cuspAffineSmoothValues_differentiable cusp ⟨test.val, cuspSmooth_le_affineSmooth cusp test.property⟩),
    cuspFiniteProjection_inner, cuspFiniteProjection_eq_self cusp level vector fixed] at projected
  exact projected

theorem cuspWeakLoweringKernel_analytic_of_finiteLevel_tests (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL)) (halfWeight : ℤ) (vector : cusp.H)
    (fixed : vector ∈ cuspFiniteLevelValues cusp level)
    (annihilates : ∀ test : cusp.smooth, test.val ∈ cuspFiniteLevelValues cusp level →
      inner ℂ (cuspRaisingVector cusp (2 * halfWeight) test.val) vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet :=
  cuspWeakLoweringKernel_analytic cusp spherical halfWeight vector
    (cuspFiniteLevel_raising_tests cusp level level_open level_compact (2 * halfWeight) vector fixed annihilates)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
