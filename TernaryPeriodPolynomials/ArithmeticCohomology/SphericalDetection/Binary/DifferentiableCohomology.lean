module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SymmetricSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Shifting by a value of a differentiable cocycle preserves its regularity. -/
theorem binaryCocycleShift_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {order : WithTop ℕ∞} (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation) (embedding : representation →ₗ[ℂ] E)
    (regular : ContDiffOn ℝ order
      (fun matrix : BinaryRealMatrix => embedding (cycle (invertibleMatrix matrix)))
      {matrix | matrix.det ≠ 0}) (fixed : BinaryRealGL) (scalar : ℂ) :
    ContDiffOn ℝ order (fun matrix : BinaryRealMatrix =>
      embedding (shiftCocycle representation cycle (scalar • cycle fixed) (invertibleMatrix matrix)))
      {matrix | matrix.det ≠ 0} := by
  have shifted := realGL_contDiffOn_mul_const (fun matrix => embedding (cycle matrix)) regular fixed
  have action_regular := shifted.sub regular
  apply (regular.sub ((action_regular.sub
    (contDiffOn_const (c := embedding (cycle fixed)))).const_smul scalar)).congr
  intro matrix _
  have identity := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property (invertibleMatrix matrix) fixed
  change cycle (invertibleMatrix matrix * fixed) =
    representation.ρ (invertibleMatrix matrix) (cycle fixed) + cycle (invertibleMatrix matrix) at identity
  have embedded := congrArg embedding identity
  rw [map_add] at embedded
  simp only [shiftCocycle_apply, map_sub, map_smul]
  rw [embedded, add_sub_cancel_right, smul_sub]

variable {degree : ℕ} {index : Type} [Fintype index]

theorem cohomological_exists_smooth_symmetricSpace_H1 (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (fun matrix : BinaryRealMatrix => (cycle (invertibleMatrix matrix) :
          binaryHilbertFiniteValues cusp level).val) {matrix | matrix.det ≠ 0} ∧
      ∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0 := by
  obtain ⟨original, original_nonzero, continuous, smooth, level, level_open, level_compact, fixed⟩ :=
    cohomological_exists_continuous_nonzero_H1 cusp cohomological basis
  let normalized := binaryRotationNormalizedCycle cusp basis original
  have normalized_fixed := binaryRotationNormalizedCycle_finiteLevel cusp basis original continuous level fixed
  let cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level) :=
    ⟨fun matrix => ⟨normalized matrix, fun element position => normalized_fixed element matrix position⟩, by
      apply (groupCohomology.mem_cocycles₁_iff _).mpr
      intro first second
      apply Subtype.ext
      exact (binaryRotationNormalizedCycle_cocycle cusp spherical basis original first second).trans (add_comm _ _)⟩
  have cycle_nonzero : groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 := by
    intro zero
    obtain ⟨primitive, boundary⟩ := (groupCohomology.H1π_eq_zero_iff cycle).mp zero
    apply binaryRotationNormalizedCycle_no_finiteLevel_primitive cusp basis original original_nonzero
      continuous (binaryHilbertCocycle_smooth cusp basis original smooth) level level_open level_compact fixed
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
  · exact fun zero => cycle_nonzero ((binaryReflectionNormalizedCycle_H1 cusp spherical basis level cycle).symm.trans zero)
  · exact binaryCocycleShift_contDiffOn _ cycle (binaryHilbertFiniteValues cusp level).subtype regular
      UpperHalfPlane.J (-(2 : ℂ)⁻¹)
  · exact binary_cocycle_stabilizer_zero _ symmetric
      (binaryReflectionNormalizedCycle_rotation cusp spherical basis level cycle rotations_zero)
      (binaryReflectionNormalizedCycle_reflection cusp spherical basis level cycle)
      (binaryHilbertFiniteCocycle_positive_scalar_zero cusp spherical cohomological basis level level_open level_compact symmetric)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
