module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtWeakOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart4

@[expose] public section


/-!
# Weight-generic level-three smooth vectors

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins, for an arbitrary integer rotation weight `wt`, of the `halfWeight` declarations of the
level-three clone `MultiplicityOne.BridgePart3` / `BridgePart4`: a rotation-weight vector
of the cuspidal representation that is killed by the raising (resp. lowering) operator yields a
nonzero smooth level-three vector of the (resp. negated) weight whose weighted orbit is
holomorphic.  `2 * halfWeight` is replaced by `wt` and `cuspWeightedAffineOrbit` by
`cuspWeightedAffineOrbitWt`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.MultiplicityOne

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

theorem levelThreeWeight_smooth_of_raising_zeroWt (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (wt : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ wt • vector)
    (fixed : vector ∈ levelThreeValues cusp)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp wt vector = 0) :
    vector ∈ cusp.smooth := by
  apply levelThreeWeight_smooth_of_affine_analytic cusp spherical central_positive vector wt
    rotation fixed
  exact cuspAffineOrbitVector_analytic_of_raising_zeroWt cusp wt vector regular raising_zero
    Complex.I (by simp)

theorem cusp_exists_levelThree_smooth_raising_zeroWt (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (wt : ℤ) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ wt • vector)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp wt vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ wt • spherical_vector.val) ∧
      cuspRaisingVector cusp wt spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  obtain ⟨finite, detected⟩ := levelThreeProjection_finite_nonzero cusp spherical vector nonzero
  let operator := (levelThreeProjection cusp).comp (cuspUnitaryOperator cusp (atFinite finite))
  have commutes : ∀ matrix value, operator (cusp.π (atInfinity matrix) value) =
      cusp.π (atInfinity matrix) (operator value) := levelThreeProjection_finite_real cusp finite
  have projected_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) (operator vector) =
        (angle : ℂ) ^ wt • operator vector := by
    intro angle
    rw [← commutes, rotation, map_smul]
  have projected_fixed : operator vector ∈ levelThreeValues cusp := levelThreeProjection_mem cusp _
  have projected_regular := cuspAffineOrbitVector_intertwiner_contDiffOn cusp operator commutes
    vector regular
  have differentiable := (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I.im > 0 by simp))).differentiableAt (by simp)
  have projected_zero : cuspRaisingVector cusp wt (operator vector) = 0 := by
    rw [cuspRaisingVector_intertwiner cusp operator commutes _ vector differentiable, raising_zero,
      map_zero]
  have projected_differentiable := projected_regular.differentiableOn (by simp)
  have smooth := levelThreeWeight_smooth_of_raising_zeroWt cusp spherical central_positive
    (operator vector) wt projected_rotation projected_fixed projected_differentiable
      projected_zero
  refine ⟨⟨operator vector, smooth⟩, ?_, projected_fixed, projected_rotation, projected_zero, ?_⟩
  · intro zero
    exact detected (congrArg Subtype.val zero)
  · exact cuspWeightedAffineOrbit_holomorphicWt cusp wt (operator vector)
      projected_differentiable projected_zero

theorem cusp_exists_levelThree_smooth_of_lowering_zeroWt (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (wt : ℤ) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ wt • vector)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (lowering_zero : cuspLoweringVector cusp wt vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (-wt) • spherical_vector.val) ∧
      cuspRaisingVector cusp (-wt) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp (-wt) spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  have reflected_nonzero : cusp.π (atInfinity UpperHalfPlane.J) vector ≠ 0 := by
    exact (map_ne_zero_iff (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J))
      (cuspUnitaryIsometryEquiv cusp (atInfinity UpperHalfPlane.J)).injective).mpr nonzero
  have reflected_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) (cusp.π (atInfinity UpperHalfPlane.J) vector) =
        (angle : ℂ) ^ (-wt) • cusp.π (atInfinity UpperHalfPlane.J) vector :=
    cuspReflection_rotation cusp wt vector rotation
  have reflected_regular := cuspAffineOrbitVector_reflection_contDiffOn cusp vector regular
  have reflected_zero : cuspRaisingVector cusp (-wt) (cusp.π (atInfinity
    UpperHalfPlane.J) vector) = 0 := by
    rw [cuspRaisingVector_reflection cusp wt vector
      ((regular.differentiableOn (by simp)).differentiableAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp))),
          lowering_zero, map_zero, neg_zero]
  exact cusp_exists_levelThree_smooth_raising_zeroWt cusp spherical central_positive
    (cusp.π (atInfinity UpperHalfPlane.J) vector) (-wt) reflected_nonzero
    reflected_rotation reflected_regular reflected_zero

theorem cuspWeakLoweringKernel_reflectionWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp wt test.val) vector = 0)
    (test : cusp.smooth) :
    inner ℂ (cuspLoweringVector cusp (-wt) test.val)
      (cusp.π (atInfinity UpperHalfPlane.J) vector) = 0 := by
  let reflected : cusp.smooth := ⟨cusp.π (atInfinity UpperHalfPlane.J) test.val,
    cusp.smooth_stable _ _ test.property⟩
  have equation := annihilates reflected
  have regular := cuspAffineSmoothValues_differentiable cusp
    ⟨test.val, cuspSmooth_le_affineSmooth cusp test.property⟩
  have reflection := cuspRaisingVector_reflection cusp (-wt) test.val regular
  rw [neg_neg] at reflection
  change inner ℂ (cuspRaisingVector cusp wt
    (cusp.π (atInfinity UpperHalfPlane.J) test.val)) vector = 0 at equation
  rw [reflection, inner_neg_left, cuspReflection_inner, neg_eq_zero] at equation
  exact equation

theorem cuspWeakLoweringKernel_analyticWt (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (wt : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp wt test.val)
      vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  have reflected := cuspWeakRaisingKernel_analyticWt cusp spherical (-wt)
    (cusp.π (atInfinity UpperHalfPlane.J) vector) (cuspWeakLoweringKernel_reflectionWt cusp
      wt vector annihilates)
  have reflected_regular : ContDiffOn ℝ ⊤
      (cuspAffineOrbitVector cusp (cusp.π (atInfinity UpperHalfPlane.J) vector))
        UpperHalfPlane.upperHalfPlaneSet :=
    reflected.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  have regular := cuspAffineOrbitVector_reflection_contDiffOn cusp _ reflected_regular
  rw [cuspReflection_involution] at regular
  intro point positive
  exact (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive)).analyticAt

theorem cuspWeakLoweringKernel_lowering_zero_of_smooth_testsWt (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (wt : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp wt test.val)
      vector = 0) :
    cuspLoweringVector cusp wt vector = 0 := by
  have analytic := cuspWeakLoweringKernel_analyticWt cusp spherical wt vector annihilates
  have regular : vector ∈ cuspAffineSmoothValues cusp :=
    analytic.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  apply (levelThreeCusp_smooth_dense cusp spherical).eq_zero_of_inner_right ℂ
  intro test member
  have skew := cuspRaisingOperator_skew cusp wt
    ⟨test, cuspSmooth_le_affineSmooth cusp member⟩ ⟨vector, regular⟩
  change inner ℂ (cuspRaisingVector cusp wt test) vector +
    inner ℂ test (cuspLoweringVector cusp wt vector) = 0 at skew
  rw [annihilates ⟨test, member⟩, zero_add] at skew
  exact skew

theorem cuspWeakLoweringKernel_exists_levelThreeWt (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (wt : ℤ) (vector : cusp.H) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ wt • vector)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspRaisingVector cusp wt test.val)
      vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (-wt) • spherical_vector.val) ∧
      cuspRaisingVector cusp (-wt) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp (-wt) spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet :=
  cusp_exists_levelThree_smooth_of_lowering_zeroWt cusp spherical central_positive vector
    wt nonzero rotation
    ((cuspWeakLoweringKernel_analyticWt cusp spherical wt vector annihilates).contDiffOn
      UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn)
    (cuspWeakLoweringKernel_lowering_zero_of_smooth_testsWt cusp spherical wt vector
      annihilates)

theorem cuspWeightWeakLoweringKernel_exists_levelThreeWt (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL)) (weight wt : ℤ)
    (weight_eq : weight + 2 = wt) (vector : cusp.H) (nonzero : vector ≠ 0)
    (member : vector ∈ cuspHilbertWeightValues cusp level (weight + 2))
    (annihilates : ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp
      level weight →
      inner ℂ vector (cuspRaisingOperator cusp weight smooth).val = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (-wt) • spherical_vector.val) ∧
      cuspRaisingVector cusp (-wt) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp (-wt) spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  apply cuspWeakLoweringKernel_exists_levelThreeWt cusp spherical central_positive wt vector
    nonzero
  · simpa only [weight_eq] using member.2
  · simpa only [weight_eq] using
      cuspWeightFiniteLevel_raising_tests cusp level level_open level_compact weight vector member
        annihilates

end TernaryPeriodPolynomials.EvenLevelThree
