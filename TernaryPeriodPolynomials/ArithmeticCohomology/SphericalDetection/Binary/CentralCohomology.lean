module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteLevelCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.InvariantValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryHilbertFiniteValues_invariant_eq_zero (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (vector : binaryHilbertFiniteValues (index := index) cusp level)
    (fixed : ∀ matrix, binaryHilbertOperator cusp basis matrix vector.val = vector.val) : vector = 0 := by
  have boundary : ∀ matrix, (0 : index → cusp.H) = binaryHilbertOperator cusp basis matrix vector.val - vector.val := by
    intro matrix
    rw [fixed, sub_self]
  obtain ⟨values, equality⟩ := binaryHilbertPrimitive_mem_range cusp basis (fun _ => 0)
    contDiffOn_const vector.val boundary level level_open level_compact vector.property
  have original_fixed (matrix) : binaryCuspidalRepresentation cusp degree matrix values = values := by
    apply binaryHilbertEmbedding_injective cusp basis
    rw [← binaryHilbertOperator_intertwines, equality, fixed]
  have values_zero : values = 0 := by
    apply Subtype.ext
    apply binaryValues_invariant_eq_zero cusp values.val values.property
    intro matrix argument
    exact congrArg (fun function : binaryCuspidalValues cusp degree => function.val argument)
      (original_fixed matrix)
  apply Subtype.ext
  rw [← equality, values_zero, map_zero]
  rfl

theorem binaryHilbertOperator_positive_scalar (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
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
  change binaryCohomologicalAction degree (GeneralLinearGroup.scalar (Fin 2) unit) values.val argument =
    values.val argument
  rw [binaryCohomologicalAction_positive_scalar cusp values.val values.property unit positive,
    cohomological_centralCharacter_positive cusp cohomological unit positive, one_smul]

theorem binaryHilbertFiniteCocycle_identity (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (first second : BinaryRealGL) :
    (cycle (first * second) : binaryHilbertFiniteValues cusp level).val =
      (cycle first : binaryHilbertFiniteValues cusp level).val +
        binaryHilbertOperator cusp basis first (cycle second : binaryHilbertFiniteValues cusp level).val := by
  have equality := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first second
  exact (congrArg Subtype.val equality).trans (add_comm _ _)

theorem binaryHilbertFiniteCocycle_positive_scalar_zero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
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

theorem binaryHilbertFiniteCocycle_right_rotation (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (matrix : BinaryRealGL) (angle : Circle) : cycle (matrix * binaryRotations angle) = cycle matrix := by
  apply Subtype.ext
  have zero : (cycle (binaryRotations angle) : binaryHilbertFiniteValues cusp level).val = (0 : index → cusp.H) :=
    congrArg Subtype.val (rotations_zero angle)
  have equality := binaryHilbertFiniteCocycle_identity cusp spherical basis level cycle matrix (binaryRotations angle)
  exact equality.trans ((congrArg (fun vector : index → cusp.H =>
    (cycle matrix : binaryHilbertFiniteValues cusp level).val + binaryHilbertOperator cusp basis matrix vector)
    zero).trans (by simp))

theorem binaryHilbertFiniteCocycle_left_rotation (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (matrix : BinaryRealGL) (angle : Circle) :
    (cycle (binaryRotations angle * matrix) : binaryHilbertFiniteValues cusp level).val =
      binaryHilbertOperator cusp basis (binaryRotations angle) (cycle matrix : binaryHilbertFiniteValues cusp level).val := by
  have zero : (cycle (binaryRotations angle) : binaryHilbertFiniteValues cusp level).val = (0 : index → cusp.H) :=
    congrArg Subtype.val (rotations_zero angle)
  have equality := binaryHilbertFiniteCocycle_identity cusp spherical basis level cycle (binaryRotations angle) matrix
  exact equality.trans ((congrArg (fun vector : index → cusp.H =>
    vector + binaryHilbertOperator cusp basis (binaryRotations angle)
      (cycle matrix : binaryHilbertFiniteValues cusp level).val) zero).trans (zero_add _))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
