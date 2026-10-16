module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Rotations
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HilbertCohomology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryRotationNormalizedCycle (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (matrix : BinaryRealGL) : index → cusp.H :=
  binaryHilbertEmbedding cusp basis (cycle matrix) -
    (binaryHilbertOperator cusp basis matrix (binaryRotationPrimitive cusp basis cycle) -
      binaryRotationPrimitive cusp basis cycle)

theorem binaryRotationNormalizedCycle_continuous (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix))) :
    Continuous (binaryRotationNormalizedCycle cusp basis cycle) :=
  continuous.sub ((binaryHilbertOperator_continuous cusp basis _).sub continuous_const)

theorem binaryRotationNormalizedCycle_cocycle (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (first second : BinaryRealGL) :
    binaryRotationNormalizedCycle cusp basis cycle (first * second) =
      binaryRotationNormalizedCycle cusp basis cycle first +
        binaryHilbertOperator cusp basis first (binaryRotationNormalizedCycle cusp basis cycle second) := by
  simp only [binaryRotationNormalizedCycle, binaryHilbertCocycle_identity,
    binaryHilbertOperator_mul cusp spherical basis, ContinuousLinearMap.comp_apply, map_sub]
  abel

theorem binaryRotationNormalizedCycle_rotation (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    (angle : Circle) : binaryRotationNormalizedCycle cusp basis cycle (binaryRotations angle) = 0 := by
  rw [binaryRotationNormalizedCycle, binaryRotationPrimitive_spec cusp basis cycle continuous,
    sub_self]

theorem binaryRotationNormalizedCycle_finiteLevel (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    (level : Subgroup BinaryFiniteGL)
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (cycle matrix) = cycle matrix)
    (element : level) (matrix : BinaryRealGL) (position : index) :
    cusp.π (atFinite element.val) (binaryRotationNormalizedCycle cusp basis cycle matrix position) =
      binaryRotationNormalizedCycle cusp basis cycle matrix position := by
  have cycle_fixed : cusp.π (atFinite element.val) (binaryHilbertEmbedding cusp basis (cycle matrix) position) =
      binaryHilbertEmbedding cusp basis (cycle matrix) position :=
    congrFun ((binaryHilbertTranslation_intertwines cusp basis (atFinite element.val) (cycle matrix)).trans
      (congrArg (binaryHilbertEmbedding cusp basis) (fixed element matrix))) position
  have primitive_fixed := binaryRotationPrimitive_finiteLevel cusp basis cycle continuous level fixed element
  simp only [binaryRotationNormalizedCycle, Pi.sub_apply, map_sub, cycle_fixed,
    binaryHilbertOperator_preserves_finiteLevel cusp basis matrix element.val _ primitive_fixed,
    primitive_fixed]

theorem binaryRotationNormalizedCycle_no_finiteLevel_primitive (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (nonzero : groupCohomology.H1π (binaryCuspidalRep cusp degree) cycle ≠ 0)
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    (regular : Smooth (fun point : Fin 1 → BinaryRealGL =>
      binaryHilbertEmbedding cusp basis (cycle (point 0))))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ element : level, ∀ matrix,
      binaryRightTranslation cusp degree (atFinite element.val) (cycle matrix) = cycle matrix) :
    ¬ ∃ vector : index → cusp.H,
      (∀ matrix, binaryRotationNormalizedCycle cusp basis cycle matrix =
        binaryHilbertOperator cusp basis matrix vector - vector) ∧
      ∀ element : level, ∀ position, cusp.π (atFinite element.val) (vector position) = vector position := by
  rintro ⟨vector, boundary, vector_fixed⟩
  apply binaryHilbertCocycle_no_finiteLevel_primitive cusp basis cycle nonzero regular
    level level_open level_compact
  refine ⟨vector + binaryRotationPrimitive cusp basis cycle, ?_, ?_⟩
  · intro matrix
    have equality := sub_eq_iff_eq_add.mp (boundary matrix)
    exact equality.trans (by rw [map_add]; abel)
  · intro element position
    simp only [Pi.add_apply, map_add, vector_fixed,
      binaryRotationPrimitive_finiteLevel cusp basis cycle continuous level fixed]

theorem cohomological_exists_rotation_normalized (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (cycle : BinaryRealGL → (index → cusp.H)) (level : Subgroup BinaryFiniteGL),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      Continuous cycle ∧
      (∀ first second, cycle (first * second) = cycle first + binaryHilbertOperator cusp basis first (cycle second)) ∧
      (∀ angle : Circle, cycle (binaryRotations angle) = 0) ∧
      (∀ element : level, ∀ matrix position,
        cusp.π (atFinite element.val) (cycle matrix position) = cycle matrix position) ∧
      ¬ ∃ vector : index → cusp.H,
        (∀ matrix, cycle matrix = binaryHilbertOperator cusp basis matrix vector - vector) ∧
        ∀ element : level, ∀ position, cusp.π (atFinite element.val) (vector position) = vector position := by
  obtain ⟨cycle, nonzero, continuous, smooth, level, level_open, level_compact, fixed⟩ :=
    cohomological_exists_continuous_nonzero_H1 cusp cohomological basis
  refine ⟨binaryRotationNormalizedCycle cusp basis cycle, level, level_open, level_compact,
    binaryRotationNormalizedCycle_continuous cusp basis cycle continuous,
    binaryRotationNormalizedCycle_cocycle cusp spherical basis cycle,
    binaryRotationNormalizedCycle_rotation cusp basis cycle continuous,
    binaryRotationNormalizedCycle_finiteLevel cusp basis cycle continuous level fixed, ?_⟩
  exact binaryRotationNormalizedCycle_no_finiteLevel_primitive cusp basis cycle nonzero continuous
    (binaryHilbertCocycle_smooth cusp basis _ smooth) level level_open level_compact fixed

end TernaryPeriodPolynomials.SphericalDetection.Helpers
