module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.NormalizedCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryHilbertFiniteValues (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    Submodule ℂ (index → cusp.H) where
  carrier := {vectors | ∀ element : level, ∀ position,
    cusp.π (atFinite element.val) (vectors position) = vectors position}
  zero_mem' := by simp
  add_mem' {first second} first_fixed second_fixed := by
    intro element position
    change cusp.π (atFinite element.val) (first position + second position) = first position + second position
    rw [map_add, first_fixed element position, second_fixed element position]
  smul_mem' scalar vectors := by
    intro fixed element position
    change cusp.π (atFinite element.val) (scalar • vectors position) = scalar • vectors position
    rw [map_smul, fixed element position]

omit [Fintype index] in
theorem binaryHilbertFiniteValues_closed (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) :
    IsClosed (binaryHilbertFiniteValues (index := index) cusp level : Set (index → cusp.H)) := by
  change IsClosed {vectors : index → cusp.H | ∀ element : level, ∀ position,
    cusp.π (atFinite element.val) (vectors position) = vectors position}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro element
  apply isClosed_iInter
  intro position
  exact isClosed_eq ((cuspUnitaryOperator cusp (atFinite element.val)).continuous.comp
    (continuous_apply position)) (continuous_apply position)

instance binaryHilbertFiniteValues_completeSpace (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) :
    CompleteSpace (binaryHilbertFiniteValues (index := index) cusp level) := by
  let : IsClosed (binaryHilbertFiniteValues (index := index) cusp level : Set (index → cusp.H)) :=
    binaryHilbertFiniteValues_closed cusp level
  infer_instance

def binaryHilbertFiniteRepresentation (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) :
    Representation ℂ BinaryRealGL (binaryHilbertFiniteValues (index := index) cusp level) :=
  (binaryHilbertRepresentation cusp spherical basis).subrepresentation
    (binaryHilbertFiniteValues cusp level) (by
      intro matrix vectors fixed element position
      exact binaryHilbertOperator_preserves_finiteLevel cusp basis matrix element.val vectors
        (fixed element) position)

def binaryHilbertFiniteRep (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL) : Rep ℂ BinaryRealGL :=
  Rep.of (X := binaryHilbertFiniteValues (index := index) cusp level)
    (binaryHilbertFiniteRepresentation cusp spherical basis level)

theorem cohomological_exists_finiteLevel_H1 (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      Continuous (fun matrix => (cycle matrix : binaryHilbertFiniteValues cusp level).val) ∧
      ∀ angle : Circle, cycle (binaryRotations angle) = 0 := by
  obtain ⟨cycle, level, level_open, level_compact, continuous, cocycle, rotations, fixed, nonboundary⟩ :=
    cohomological_exists_rotation_normalized cusp spherical cohomological basis
  let group_cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level) :=
    ⟨fun matrix => ⟨cycle matrix, fun element position => fixed element matrix position⟩, by
      apply (groupCohomology.mem_cocycles₁_iff _).mpr
      intro first second
      apply Subtype.ext
      exact (cocycle first second).trans (add_comm _ _)⟩
  refine ⟨level, group_cycle, level_open, level_compact, ?_, continuous, ?_⟩
  · intro zero
    obtain ⟨primitive, boundary⟩ := (groupCohomology.H1π_eq_zero_iff group_cycle).mp zero
    apply nonboundary
    refine ⟨primitive.val, ?_, primitive.property⟩
    intro matrix
    exact (congrArg Subtype.val (congrFun boundary matrix)).symm
  · intro angle
    apply Subtype.ext
    exact rotations angle

end TernaryPeriodPolynomials.SphericalDetection.Helpers
