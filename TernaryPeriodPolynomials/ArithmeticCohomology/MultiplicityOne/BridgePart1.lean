module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgeBasic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.NormalizedCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteLevelCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ReflectionCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DifferentiableCohomology

@[expose] public section


/-!
# Level-three port of the spherical holomorphic-detection chain, Part1

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinaryHilbertModel`, `SphericalDetection.BinaryNormalizedCocycle`,
`SphericalDetection.BinaryFiniteLevelCohomology`, `SphericalDetection.BinaryCentralCohomology`,
`SphericalDetection.BinaryReflectionCohomology`,
`SphericalDetection.BinaryDifferentiableCohomology`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section CloneBinaryHilbertModel

open GeneralEisenstein GeneralEisenstein.Adelic

theorem levelThreeCusp_smooth_dense (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) : Dense (cusp.smooth : Set cusp.H) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have stable : ∀ matrix vector, vector ∈ cusp.smooth.topologicalClosure →
      cusp.π matrix vector ∈ cusp.smooth.topologicalClosure := by
    intro matrix vector member
    have original : cusp.smooth.map (cusp.π matrix) ≤ cusp.smooth := by
      rintro _ ⟨original, original_mem, rfl⟩
      exact cusp.smooth_stable matrix original original_mem
    have closure_map := (Submodule.topologicalClosure_map
      (cuspUnitaryOperator cusp matrix) cusp.smooth).trans
      (Submodule.topologicalClosure_mono original)
    exact closure_map ⟨vector, member, rfl⟩
  rcases cusp.irreducible cusp.smooth.topologicalClosure isClosed_closure stable with zero | full
  · rcases spherical with ⟨vector, nonzero, _⟩
    have member : vector.val ∈ cusp.smooth.topologicalClosure :=
      subset_closure vector.property
    rw [zero, Submodule.mem_bot] at member
    exact False.elim (nonzero (Subtype.ext member))
  · exact full

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryHilbertEmbedding_dense (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    DenseRange (binaryHilbertEmbedding cusp basis) := by
  have dense : DenseRange (fun vectors : index → cusp.smooth =>
      fun position => (vectors position).val) :=
    DenseRange.piMap (fun _ =>
      denseRange_subtype_val.mpr (levelThreeCusp_smooth_dense cusp spherical))
  have ranges : Set.range (binaryHilbertEmbedding cusp basis) =
      Set.range (fun vectors : index → cusp.smooth => fun position => (vectors position).val) := by
    ext vectors
    constructor
    · rintro ⟨values, rfl⟩
      exact ⟨binarySmoothCoordinates cusp basis values, rfl⟩
    · rintro ⟨smooth_vectors, rfl⟩
      obtain ⟨values, coordinates⟩ := binarySmoothCoordinates_surjective cusp basis smooth_vectors
      refine ⟨values, ?_⟩
      change (fun position => (binarySmoothCoordinates cusp basis values position).val) = _
      rw [coordinates]
  change Dense (Set.range (binaryHilbertEmbedding cusp basis))
  rw [ranges]
  exact dense

theorem binaryHilbertOperator_one (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    binaryHilbertOperator cusp basis 1 = ContinuousLinearMap.id ℂ (index → cusp.H) := by
  apply DFunLike.coe_injective
  apply (binaryHilbertEmbedding_dense cusp spherical basis).equalizer
    (binaryHilbertOperator cusp basis 1).continuous continuous_id
  funext values
  change binaryHilbertOperator cusp basis 1 (binaryHilbertEmbedding cusp basis values) = _
  rw [binaryHilbertOperator_intertwines, map_one]
  rfl

theorem binaryHilbertOperator_mul (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (first second : BinaryRealGL) :
    binaryHilbertOperator cusp basis (first * second) =
      (binaryHilbertOperator cusp basis first).comp (binaryHilbertOperator cusp basis second) := by
  apply DFunLike.coe_injective
  apply (binaryHilbertEmbedding_dense cusp spherical basis).equalizer
    (binaryHilbertOperator cusp basis (first * second)).continuous
    ((binaryHilbertOperator cusp basis first).continuous.comp
      (binaryHilbertOperator cusp basis second).continuous)
  funext values
  change binaryHilbertOperator cusp basis (first * second) (binaryHilbertEmbedding cusp basis
    values) =
    binaryHilbertOperator cusp basis first
      (binaryHilbertOperator cusp basis second (binaryHilbertEmbedding cusp basis values))
  rw [binaryHilbertOperator_intertwines, binaryHilbertOperator_intertwines,
    binaryHilbertOperator_intertwines, map_mul]
  rfl

def binaryHilbertRepresentation (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    Representation ℂ BinaryRealGL (index → cusp.H) where
  toFun matrix := (binaryHilbertOperator cusp basis matrix).toLinearMap
  map_one' := congrArg ContinuousLinearMap.toLinearMap (binaryHilbertOperator_one cusp spherical
    basis)
  map_mul' first second := congrArg ContinuousLinearMap.toLinearMap
    (binaryHilbertOperator_mul cusp spherical basis first second)

end CloneBinaryHilbertModel

section CloneBinaryNormalizedCocycle

open GeneralEisenstein GeneralEisenstein.Adelic

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryRotationNormalizedCycle_cocycle (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (first second : BinaryRealGL) :
    binaryRotationNormalizedCycle cusp basis cycle (first * second) =
      binaryRotationNormalizedCycle cusp basis cycle first +
        binaryHilbertOperator cusp basis first (binaryRotationNormalizedCycle cusp basis cycle
          second) := by
  simp only [binaryRotationNormalizedCycle, binaryHilbertCocycle_identity,
    binaryHilbertOperator_mul cusp spherical basis, ContinuousLinearMap.comp_apply, map_sub]
  abel

end CloneBinaryNormalizedCocycle

section CloneBinaryFiniteLevelCohomology

open GeneralEisenstein GeneralEisenstein.Adelic

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryHilbertFiniteRepresentation (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) :
    Representation ℂ BinaryRealGL (binaryHilbertFiniteValues (index := index) cusp level) :=
  (binaryHilbertRepresentation cusp spherical basis).subrepresentation
    (binaryHilbertFiniteValues cusp level) (by
      intro matrix vectors fixed element position
      exact binaryHilbertOperator_preserves_finiteLevel cusp basis matrix element.val vectors
        (fixed element) position)

def binaryHilbertFiniteRep (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) : Rep ℂ BinaryRealGL :=
  Rep.of (X := binaryHilbertFiniteValues (index := index) cusp level)
    (binaryHilbertFiniteRepresentation cusp spherical basis level)

end CloneBinaryFiniteLevelCohomology

section CloneBinaryCentralCohomology

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

open scoped Matrix.Norms.Elementwise

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryHilbertOperator_positive_scalar (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (unit : ℝˣ) (positive : 0 < unit.val) :
    binaryHilbertOperator cusp basis (GeneralLinearGroup.scalar (Fin 2) unit) =
      ContinuousLinearMap.id ℂ (index → cusp.H) := by
  apply DFunLike.coe_injective
  apply (binaryHilbertEmbedding_dense cusp spherical basis).equalizer
    (binaryHilbertOperator cusp basis _).continuous continuous_id
  funext values
  change binaryHilbertOperator cusp basis (GeneralLinearGroup.scalar (Fin 2) unit)
    (binaryHilbertEmbedding cusp basis values) = binaryHilbertEmbedding cusp basis values
  rw [binaryHilbertOperator_intertwines]
  congr 1
  apply Subtype.ext
  funext argument
  change binaryCohomologicalAction degree (GeneralLinearGroup.scalar (Fin 2) unit) values.val
    argument =
    values.val argument
  rw [binaryCohomologicalAction_positive_scalar cusp values.val values.property unit positive,
    cohomological_centralCharacter_positive cusp cohomological unit positive, one_smul]

theorem binaryHilbertFiniteCocycle_identity (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (first second : BinaryRealGL) :
    (cycle (first * second) : binaryHilbertFiniteValues cusp level).val =
      (cycle first : binaryHilbertFiniteValues cusp level).val +
        binaryHilbertOperator cusp basis first (cycle second : binaryHilbertFiniteValues cusp
          level).val := by
  have equality := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first second
  exact (congrArg Subtype.val equality).trans (add_comm _ _)

theorem binaryHilbertFiniteCocycle_positive_scalar_zero (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (unit : ℝˣ) (positive : 0 < unit.val) : cycle (GeneralLinearGroup.scalar (Fin 2) unit) = 0 := by
  apply binaryHilbertFiniteValues_invariant_eq_zero cusp basis level level_open level_compact
  intro matrix
  let central := GeneralLinearGroup.scalar (Fin 2) unit
  have first := binaryHilbertFiniteCocycle_identity cusp spherical basis level cycle central matrix
  have second := binaryHilbertFiniteCocycle_identity cusp spherical basis level cycle matrix central
  rw [binaryHilbertOperator_positive_scalar cusp spherical cohomological basis unit positive,
    ContinuousLinearMap.id_apply] at first
  rw [GeneralLinearGroup.scalar_commute unit matrix] at first
  have equality := first.symm.trans second
  exact (add_left_cancel (by simpa only [add_comm] using equality)).symm

end CloneBinaryCentralCohomology

section CloneBinaryReflectionCohomology

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryReflectionNormalizedCycle (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) :
    groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level) :=
  shiftCocycle _ cycle (-(2 : ℂ)⁻¹ • cycle UpperHalfPlane.J)

theorem binaryReflectionNormalizedCycle_H1 (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) :
    groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
      (binaryReflectionNormalizedCycle cusp spherical basis level cycle) =
        groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle :=
  shiftCocycle_H1 _ _ _

theorem binaryReflectionNormalizedCycle_reflection (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) :
    binaryReflectionNormalizedCycle cusp spherical basis level cycle UpperHalfPlane.J = 0 :=
  shiftCocycle_involution _ _ _ (by simpa only [pow_two] using UpperHalfPlane.J_sq)

theorem binaryReflectionNormalizedCycle_rotation (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (angle : Circle) : binaryReflectionNormalizedCycle cusp spherical basis level cycle
      (binaryRotations angle) = 0 := by
  apply shiftCocycle_zero_of_fixed _ _ _ _ (rotations_zero angle)
  rw [map_smul, cocycle_normalizer_fixed _ cycle (binaryRotations angle) UpperHalfPlane.J
    (binaryRotations angle⁻¹) (binaryRotation_mul_reflection angle) (rotations_zero angle)
      (rotations_zero angle⁻¹)]

end CloneBinaryReflectionCohomology

section CloneBinaryDifferentiableCohomology

open GeneralEisenstein GeneralEisenstein.Adelic

open scoped Matrix.Norms.Elementwise

variable {degree : ℕ} {index : Type} [Fintype index]

theorem cohomological_exists_smooth_symmetricSpace_H1 (cusp : CuspidalRepresentation)
    (spherical : LevelThreeCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (fun matrix : BinaryRealMatrix => (cycle (invertibleMatrix matrix) :
          binaryHilbertFiniteValues cusp level).val) {matrix | matrix.det ≠ 0} ∧
      ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0 := by
  obtain ⟨original, original_nonzero, continuous, smooth, level, level_open, level_compact, fixed⟩
    :=
    cohomological_exists_continuous_nonzero_H1 cusp cohomological basis
  let normalized := binaryRotationNormalizedCycle cusp basis original
  have normalized_fixed := binaryRotationNormalizedCycle_finiteLevel cusp basis original continuous
    level fixed
  let cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level) :=
    ⟨fun matrix => ⟨normalized matrix, fun element position => normalized_fixed element matrix
      position⟩, by
      apply (groupCohomology.mem_cocycles₁_iff _).mpr
      intro first second
      apply Subtype.ext
      exact (binaryRotationNormalizedCycle_cocycle cusp spherical basis original first
        second).trans (add_comm _ _)⟩
  have cycle_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
    cycle ≠ 0 := by
    intro zero
    obtain ⟨primitive, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp zero
    apply binaryRotationNormalizedCycle_no_finiteLevel_primitive cusp basis original
      original_nonzero
      continuous (binaryHilbertCocycle_smooth cusp basis original smooth) level level_open
        level_compact fixed
    refine ⟨primitive.val, ?_, primitive.property⟩
    intro matrix
    exact (congrArg Subtype.val (congrFun boundary matrix)).symm
  have rotations_zero (angle : Circle) : cycle (binaryRotations angle) = 0 := by
    apply Subtype.ext
    exact binaryRotationNormalizedCycle_rotation cusp basis original continuous angle
  have regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun matrix : BinaryRealMatrix => (cycle (invertibleMatrix matrix) :
        binaryHilbertFiniteValues cusp level).val) {matrix | matrix.det ≠ 0} :=
    binaryRotationNormalizedCycle_contDiffOn cusp basis original
      (binaryHilbertCocycle_smooth cusp basis original smooth)
  let symmetric := binaryReflectionNormalizedCycle cusp spherical basis level cycle
  refine ⟨level, symmetric, level_open, level_compact, ?_, ?_, ?_⟩
  · exact fun zero => cycle_nonzero ((binaryReflectionNormalizedCycle_H1 cusp spherical basis level
      cycle).symm.trans zero)
  · exact binaryCocycleShift_contDiffOn _ cycle (binaryHilbertFiniteValues cusp level).subtype
      regular
      UpperHalfPlane.J (-(2 : ℂ)⁻¹)
  · exact binary_cocycle_stabilizer_zero _ symmetric
      (binaryReflectionNormalizedCycle_rotation cusp spherical basis level cycle rotations_zero)
      (binaryReflectionNormalizedCycle_reflection cusp spherical basis level cycle)
      (binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical cohomological basis level
        level_open level_compact symmetric)

end CloneBinaryDifferentiableCohomology

end TernaryPeriodPolynomials.MultiplicityOne
