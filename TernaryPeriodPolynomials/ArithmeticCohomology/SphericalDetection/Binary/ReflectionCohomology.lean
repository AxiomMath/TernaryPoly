module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CocycleShift
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRotation_mul_reflection (angle : Circle) :
    binaryRotations angle * UpperHalfPlane.J = UpperHalfPlane.J * binaryRotations angle⁻¹ := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryRotations, binaryRotation, UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two]

variable {degree : ℕ} {index : Type} [Fintype index]

def binaryReflectionNormalizedCycle (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) :
    groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level) :=
  shiftCocycle _ cycle (-(2 : ℂ)⁻¹ • cycle UpperHalfPlane.J)

theorem binaryReflectionNormalizedCycle_H1 (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) :
    groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level)
      (binaryReflectionNormalizedCycle cusp spherical basis level cycle) =
        groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle :=
  shiftCocycle_H1 _ _ _

theorem binaryReflectionNormalizedCycle_reflection (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)) :
    binaryReflectionNormalizedCycle cusp spherical basis level cycle UpperHalfPlane.J = 0 :=
  shiftCocycle_involution _ _ _ (by simpa only [pow_two] using UpperHalfPlane.J_sq)

theorem binaryReflectionNormalizedCycle_rotation (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (angle : Circle) : binaryReflectionNormalizedCycle cusp spherical basis level cycle (binaryRotations angle) = 0 := by
  apply shiftCocycle_zero_of_fixed _ _ _ _ (rotations_zero angle)
  rw [map_smul, cocycle_normalizer_fixed _ cycle (binaryRotations angle) UpperHalfPlane.J
    (binaryRotations angle⁻¹) (binaryRotation_mul_reflection angle) (rotations_zero angle) (rotations_zero angle⁻¹)]

theorem binaryReflectionNormalizedCycle_continuous (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (continuous : Continuous (fun matrix => (cycle matrix : binaryHilbertFiniteValues cusp level).val)) :
    Continuous (fun matrix =>
      (binaryReflectionNormalizedCycle cusp spherical basis level cycle matrix :
        binaryHilbertFiniteValues cusp level).val) := by
  let primitive : binaryHilbertFiniteRep cusp spherical basis level := -(2 : ℂ)⁻¹ • cycle UpperHalfPlane.J
  change Continuous (fun matrix => (cycle matrix : binaryHilbertFiniteValues cusp level).val -
    (binaryHilbertOperator cusp basis matrix primitive.val - primitive.val))
  exact continuous.sub ((binaryHilbertOperator_continuous cusp basis primitive.val).sub continuous_const)

theorem cohomological_exists_symmetricSpace_H1 (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      Continuous (fun matrix => (cycle matrix : binaryHilbertFiniteValues cusp level).val) ∧
      (∀ angle : Circle, cycle (binaryRotations angle) = 0) ∧ cycle UpperHalfPlane.J = 0 ∧
      ∀ unit : ℝˣ, 0 < unit.val → cycle (GeneralLinearGroup.scalar (Fin 2) unit) = 0 := by
  obtain ⟨level, cycle, level_open, level_compact, nonzero, continuous, rotations_zero⟩ :=
    cohomological_exists_finiteLevel_H1 cusp spherical cohomological basis
  refine ⟨level, binaryReflectionNormalizedCycle cusp spherical basis level cycle,
    level_open, level_compact, ?_, binaryReflectionNormalizedCycle_continuous cusp spherical basis level cycle continuous,
    binaryReflectionNormalizedCycle_rotation cusp spherical basis level cycle rotations_zero,
    binaryReflectionNormalizedCycle_reflection cusp spherical basis level cycle, ?_⟩
  · rw [binaryReflectionNormalizedCycle_H1]
    exact nonzero
  · exact binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical cohomological basis level
      level_open level_compact _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
