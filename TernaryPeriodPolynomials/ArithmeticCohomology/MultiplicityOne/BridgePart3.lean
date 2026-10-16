module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.UnitaryCentral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DetNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ExtremalSpherical
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TangentCoboundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderClosures

@[expose] public section


/-!
# Level-three port of the spherical holomorphic-detection chain, Part3

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinaryRelativeCocycle`, `SphericalDetection.BinaryUnitaryCentral`,
`SphericalDetection.BinaryDetNormalization`, `SphericalDetection.BinaryWeightAnalytic`,
`SphericalDetection.BinaryExtremalSpherical`, `SphericalDetection.BinaryTangentCoboundary`,
`SphericalDetection.BinaryLadderClosures`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section CloneBinaryRelativeCocycle

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryAffineOrbitVector_tangent (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (point : UpperHalfPlane) (direction : ℂ) :
    binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction) point =
        point.im • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ)
          direction := by
  have equivariant := binaryUpperPotential_fderiv_equivariant cusp spherical basis level cycle
    regular
    stabilizer_zero (binarySymmetricSection point) UpperHalfPlane.I
  rw [binarySymmetricSection_smul] at equivariant
  have evaluated := congrArg (fun derivative : ℂ →L[ℝ] (index → cusp.H) => derivative direction)
    equivariant
  change fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ)
      (UpperHalfPlane.smulFDeriv (binarySymmetricSection point) Complex.I direction) =
    binaryHilbertOperator cusp basis (binarySymmetricSection point)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
        direction) at evaluated
  rw [binarySymmetricSection_smulFDeriv, map_smul] at evaluated
  rw [binaryAffineOrbitVector, binaryUpperSectionMatrix_coe, invertibleMatrix_coe]
  exact evaluated.symm

theorem binaryAffineOrbitVector_tangent_contDiffOn (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (direction : ℂ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction))
      UpperHalfPlane.upperHalfPlaneSet := by
  have derivative_regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle))
        UpperHalfPlane.upperHalfPlaneSet :=
    regular.fderiv_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet
      (WithTop.coe_le_coe.mpr (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))
  have weighted := Complex.imCLM.contDiff.contDiffOn.smul
    (derivative_regular.clm_apply (contDiffOn_const (c := direction)))
  apply weighted.congr
  intro point member
  exact binaryAffineOrbitVector_tangent cusp spherical basis level cycle
    (regular.differentiableOn (by simp)) stabilizer_zero ⟨point, member⟩ direction

theorem binaryTangent_relativeCocycle (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    fderiv ℝ (binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1)) Complex.I
        Complex.I -
    fderiv ℝ (binaryAffineOrbitVector cusp basis
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I))
        Complex.I 1 =
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 := by
  have equality (direction : ℂ) :
      binaryAffineOrbitVector cusp basis
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction)
          =ᶠ[nhds Complex.I]
      (fun point : ℂ => point.im •
        fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) point direction) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp)] with point member
    exact binaryAffineOrbitVector_tangent cusp spherical basis level cycle
      (regular.differentiableOn (by simp)) stabilizer_zero ⟨point, member⟩ direction
  rw [(equality 1).fderiv_eq, (equality Complex.I).fderiv_eq]
  apply weightedGradient_relation
  exact (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet by simp))).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

end CloneBinaryRelativeCocycle

section CloneBinaryUnitaryCentral

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

theorem cuspUnitary_central (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp cusp)
    (unit : Adelesˣ) (vector : cusp.H) :
    cusp.π (GeneralLinearGroup.scalar (Fin 2) unit) vector = cusp.centralCharacter unit • vector :=
      by
  have dense : DenseRange (fun value : cusp.smooth => value.val) :=
    denseRange_subtype_val.mpr (levelThreeCusp_smooth_dense cusp spherical)
  have equality := dense.equalizer
    (cuspUnitaryOperator cusp (GeneralLinearGroup.scalar (Fin 2) unit)).continuous
    (continuous_const.smul continuous_id) (by
      funext smooth_vector
      have smooth_equality :
          (⟨cusp.π (GeneralLinearGroup.scalar (Fin 2) unit) smooth_vector.val,
            cusp.smooth_stable _ _ smooth_vector.property⟩ : cusp.smooth) =
          cusp.centralCharacter unit • smooth_vector := by
        apply cusp.injective
        funext argument
        rw [cusp.equivariant, map_smul]
        change cusp.realize smooth_vector (argument * GeneralLinearGroup.scalar (Fin 2) unit) =
          cusp.centralCharacter unit * cusp.realize smooth_vector argument
        rw [← GeneralLinearGroup.scalar_commute, cusp.central]
      exact congrArg Subtype.val smooth_equality)
  exact congrFun equality vector

theorem cuspUnitary_positive_scalar (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (unit : ℝˣ) (positive : 0 < unit.val) (vector : cusp.H) :
    cusp.π (atInfinity (GeneralLinearGroup.scalar (Fin 2) unit)) vector = vector := by
  rw [atInfinity_scalar, cuspUnitary_central cusp spherical, central_positive unit positive,
    one_smul]

end CloneBinaryUnitaryCentral

section CloneBinaryDetNormalization

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

open scoped Matrix.Norms.Elementwise

theorem cuspRotationWeight_positive_formula (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ weight • vector)
    (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) :
    cusp.π (atInfinity matrix) vector =
      binaryPhaseValue (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)) Complex.I ^ weight
        •
        cuspAffineOrbitVector cusp vector
          ((invertibleMatrix (binaryDetNormalizedMatrix matrix.val) • UpperHalfPlane.I :
            UpperHalfPlane) : ℂ) := by
  have normalized_det :
      (GeneralLinearGroup.det (invertibleMatrix (binaryDetNormalizedMatrix matrix.val))).val = 1 :=
        by
    change (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)).val.det = 1
    rw [invertibleMatrix_val _ (by rw [binaryDetNormalizedMatrix_det _ positive]; norm_num),
      binaryDetNormalizedMatrix_det _ positive]
  have equality := cuspRotationWeight_affine_transform cusp vector weight rotation
    (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)) normalized_det UpperHalfPlane.I
  simp only [UpperHalfPlane.coe_I, cuspAffineOrbitVector_I] at equality
  conv_lhs => rw [← binaryDetNormalizedMatrix_recover matrix positive]
  rw [atInfinity_mul, map_mul, Module.End.mul_apply,
    cuspUnitary_positive_scalar cusp spherical central_positive _ (Real.sqrt_pos.mpr positive)]
  exact equality

end CloneBinaryDetNormalization

section CloneBinaryWeightAnalytic

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

open scoped Matrix.Norms.Elementwise

theorem cuspRotationWeight_positive_matrix_formula (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ weight • vector)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) (positive : 0 < matrix.det) :
    cusp.π (atInfinity (invertibleMatrix matrix)) vector =
      binaryMatrixPhaseI (binaryDetNormalizedMatrix matrix) ^ weight •
        cuspAffineOrbitVector cusp vector (binaryMatrixPointI (binaryDetNormalizedMatrix matrix))
          := by
  have normalized_invertible : (binaryDetNormalizedMatrix matrix).det ≠ 0 := by
    rw [binaryDetNormalizedMatrix_det matrix positive]
    exact one_ne_zero
  have normalized_positive :
      (0 : ℝ) < (invertibleMatrix (binaryDetNormalizedMatrix matrix)).val.det := by
    rw [invertibleMatrix_val _ normalized_invertible, binaryDetNormalizedMatrix_det _ positive]
    norm_num
  have equality := cuspRotationWeight_positive_formula cusp spherical central_positive vector
    weight rotation
    (invertibleMatrix matrix) (by rw [invertibleMatrix_val _ (ne_of_gt positive)]; exact positive)
  simp only [invertibleMatrix_val matrix (ne_of_gt positive)] at equality
  rw [← binaryMatrixPhaseI_coe, ← binaryMatrixPointI_coe _ normalized_positive,
    invertibleMatrix_val _ normalized_invertible] at equality
  exact equality

theorem cuspRotationWeight_analyticAt_one (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ weight • vector)
    (affine_analytic : AnalyticAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    AnalyticAt ℝ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector) 1 := by
  have point_analytic : AnalyticAt ℝ
      (fun matrix => binaryMatrixPointI (binaryDetNormalizedMatrix matrix)) 1 := by
    apply AnalyticAt.fun_comp
    · simpa only [binaryDetNormalizedMatrix_one] using binaryMatrixPointI_contDiffAt_one.analyticAt
    · exact binaryDetNormalizedMatrix_contDiffAt_one.analyticAt
  have phase_analytic : AnalyticAt ℝ
      (fun matrix => binaryMatrixPhaseI (binaryDetNormalizedMatrix matrix)) 1 := by
    apply AnalyticAt.fun_comp
    · simpa only [binaryDetNormalizedMatrix_one] using binaryMatrixPhaseI_contDiffAt_one.analyticAt
    · exact binaryDetNormalizedMatrix_contDiffAt_one.analyticAt
  have vector_analytic : AnalyticAt ℝ
      (fun matrix => cuspAffineOrbitVector cusp vector (binaryMatrixPointI
        (binaryDetNormalizedMatrix matrix))) 1 := by
    apply AnalyticAt.fun_comp
    · simpa only [binaryDetNormalizedMatrix_one, binaryMatrixPointI_one] using affine_analytic
    · exact point_analytic
  have analytic := (phase_analytic.zpow (n := weight)
    (by simp only [binaryDetNormalizedMatrix_one, binaryMatrixPhaseI_one, ne_eq, one_ne_zero,
      not_false_eq_true])).smul vector_analytic
  apply analytic.congr
  have domain_open : IsOpen {matrix : Matrix (Fin 2) (Fin 2) ℝ | 0 < matrix.det} :=
    isOpen_lt continuous_const continuous_id.matrix_det
  filter_upwards [domain_open.mem_nhds (show (0 : ℝ) < (1 : Matrix (Fin 2) (Fin 2) ℝ).det by simp)]
    with matrix positive
  exact (cuspRotationWeight_positive_matrix_formula cusp spherical central_positive vector weight
    rotation matrix positive).symm

theorem levelThreeWeight_smooth_of_affine_analytic (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ weight • vector)
    (fixed : vector ∈ levelThreeValues cusp)
    (affine_analytic : AnalyticAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    vector ∈ cusp.smooth := by
  apply (cusp.smooth_exact vector).mpr
  refine ⟨cuspUnitary_orbit_smooth_of_one cusp vector
    (cuspRotationWeight_analyticAt_one cusp spherical central_positive vector weight rotation
      affine_analytic),
    levelThreeSmoothLevel, levelThreeSmoothLevel_isOpen, levelThreeSmoothLevel_isCompact, ?_⟩
  intro element
  exact levelThreeValues_fixed_smoothLevel cusp vector fixed
    element.val element.property

theorem levelThreeWeight_smooth_of_raising_zero (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (halfWeight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ (2 * halfWeight) • vector)
    (fixed : vector ∈ levelThreeValues cusp)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector = 0) :
    vector ∈ cusp.smooth := by
  apply levelThreeWeight_smooth_of_affine_analytic cusp spherical central_positive vector (2 *
    halfWeight) rotation fixed
  exact cuspAffineOrbitVector_analytic_of_raising_zero cusp halfWeight vector regular raising_zero
    Complex.I (by simp)

end CloneBinaryWeightAnalytic

section CloneBinaryExtremalSpherical

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cusp_exists_levelThree_smooth_raising_zero (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (halfWeight : ℤ) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ)
      ^ (2 * halfWeight) • vector)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector = 0) :
    ∃ spherical_vector : cusp.smooth, spherical_vector ≠ 0 ∧
      spherical_vector.val ∈ levelThreeValues cusp ∧
      (∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector.val =
        (angle : ℂ) ^ (2 * halfWeight) • spherical_vector.val) ∧
      cuspRaisingVector cusp (2 * halfWeight) spherical_vector.val = 0 ∧
      DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight spherical_vector.val)
        UpperHalfPlane.upperHalfPlaneSet := by
  obtain ⟨finite, detected⟩ := levelThreeProjection_finite_nonzero cusp spherical vector nonzero
  let operator := (levelThreeProjection cusp).comp (cuspUnitaryOperator cusp (atFinite finite))
  have commutes : ∀ matrix value, operator (cusp.π (atInfinity matrix) value) =
      cusp.π (atInfinity matrix) (operator value) := levelThreeProjection_finite_real cusp finite
  have projected_rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) (operator vector) =
        (angle : ℂ) ^ (2 * halfWeight) • operator vector := by
    intro angle
    rw [← commutes, rotation, map_smul]
  have projected_fixed : operator vector ∈ levelThreeValues cusp := levelThreeProjection_mem cusp _
  have projected_regular := cuspAffineOrbitVector_intertwiner_contDiffOn cusp operator commutes
    vector regular
  have differentiable := (regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I.im > 0 by simp))).differentiableAt (by simp)
  have projected_zero : cuspRaisingVector cusp (2 * halfWeight) (operator vector) = 0 := by
    rw [cuspRaisingVector_intertwiner cusp operator commutes _ vector differentiable, raising_zero,
      map_zero]
  have projected_differentiable := projected_regular.differentiableOn (by simp)
  have smooth := levelThreeWeight_smooth_of_raising_zero cusp spherical central_positive
    (operator vector) halfWeight projected_rotation projected_fixed projected_differentiable
      projected_zero
  refine ⟨⟨operator vector, smooth⟩, ?_, projected_fixed, projected_rotation, projected_zero, ?_⟩
  · intro zero
    exact detected (congrArg Subtype.val zero)
  · exact cuspWeightedAffineOrbit_holomorphic cusp halfWeight (operator vector)
      projected_differentiable projected_zero

end CloneBinaryExtremalSpherical

section CloneBinaryTangentCoboundary

open GeneralEisenstein GeneralEisenstein.Adelic

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryUpperPotential_shift (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (primitive : binaryHilbertFiniteValues (index := index) cusp level) :
    binaryUpperPotential cusp spherical basis level (shiftCocycle _ cycle primitive) =
      fun point => binaryUpperPotential cusp spherical basis level cycle point -
        (binaryAffineOrbitVector cusp basis primitive.val point - primitive.val) := rfl

theorem binaryUpperPotential_shift_fderiv (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (primitive : binaryHilbertFiniteValues (index := index) cusp level)
    (cycle_regular : DifferentiableAt ℝ (binaryUpperPotential cusp spherical basis level cycle)
      Complex.I)
    (primitive_regular : DifferentiableAt ℝ (binaryAffineOrbitVector cusp basis primitive.val)
      Complex.I) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level (shiftCocycle _ cycle primitive))
      Complex.I =
      fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I -
        fderiv ℝ (binaryAffineOrbitVector cusp basis primitive.val) Complex.I := by
  rw [binaryUpperPotential_shift]
  exact (cycle_regular.hasFDerivAt.sub (primitive_regular.hasFDerivAt.sub_const
    primitive.val)).fderiv

end CloneBinaryTangentCoboundary

section CloneBinaryLadderClosures

open GeneralEisenstein GeneralEisenstein.Adelic

open scoped Matrix.Norms.Elementwise

theorem cuspAffineSmoothValues_dense (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp) :
    Dense (cuspAffineSmoothValues cusp : Set cusp.H) :=
  (levelThreeCusp_smooth_dense cusp spherical).mono (cuspSmooth_le_affineSmooth cusp)

theorem cuspRaisingPMap_isClosable (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp) (weight : ℤ) :
    (cuspRaisingPMap cusp weight).IsClosable := by
  have dense : Dense ((-cuspLoweringPMap cusp weight).domain : Set cusp.H) :=
    cuspAffineSmoothValues_dense cusp spherical
  apply LinearPMap.isClosable_iff_exists_closed_extension.mpr
  exact ⟨(-cuspLoweringPMap cusp weight).adjoint, LinearPMap.adjoint_isClosed dense,
    (cuspRaisingPMap_formalAdjoint cusp weight).symm.le_adjoint dense⟩

end CloneBinaryLadderClosures

end TernaryPeriodPolynomials.MultiplicityOne
