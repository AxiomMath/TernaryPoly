module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.BoundaryLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeComparison

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- In relative normal form, the two endpoints give an exact test for a coboundary. -/
theorem binaryNormalForm_coboundary_iff_endpoints (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_value : binarySmoothValues_val cusp lower = binaryHolomorphicTangent cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
    (upper_value : binarySmoothValues_val cusp upper =
      fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) Complex.I Complex.I)
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0) :
    groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level) cycle = 0 ↔
      ∃ boundary : cuspFiniteWeightValues cusp level (degree + 1 : ℕ),
        binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0
          (binaryRelativeBoundaryLift cusp degree level boundary) 0 = lower 0 ∧
        cuspRaisingOperator cusp (degree + 1 : ℕ) boundary.val = upper (Fin.last (degree + 1)) := by
  let basis := binaryWeightBasis (degree + 1)
  rw [binaryRelativePair_coboundary_iff cusp spherical cohomological basis level level_open level_compact
    cycle regular rotations_zero lower upper lower_value upper_value]
  constructor
  · rintro ⟨primitive, primitive_finite, primitive_rotation, primitive_lower, primitive_upper⟩
    have primitive_mem (position : Fin (degree + 2)) :
        primitive position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 0 position) := by
      refine ⟨fun element => primitive_finite element position, ?_⟩
      apply binaryWeightBasis_eigenvector_coordinate cusp degree 0 (binarySmoothValues_val cusp primitive)
      intro angle
      simpa only [zpow_zero, one_smul] using primitive_rotation angle
    have last_weight : binaryUnitaryWeight degree 0 (Fin.last (degree + 1)) = (degree + 1 : ℕ) := by
      simp only [binaryUnitaryWeight, Fin.val_last]
      omega
    let boundary : cuspFiniteWeightValues cusp level (degree + 1 : ℕ) :=
      ⟨primitive (Fin.last (degree + 1)), by rw [← last_weight]; exact primitive_mem _⟩
    have lift_eq : binaryRelativeBoundaryLift cusp degree level boundary = primitive := by
      apply binaryRelativeBoundaryLift_eq cusp degree level boundary primitive rfl
      intro position
      rw [primitive_lower, support]
    refine ⟨boundary, ?_, ?_⟩
    · rw [lift_eq, primitive_lower]
    · have endpoint := congrFun primitive_upper (Fin.last (degree + 1))
      rw [binaryRelativeRaising_last, zero_add] at endpoint
      exact endpoint
  · rintro ⟨boundary, lower_endpoint, upper_endpoint⟩
    let primitive := binaryRelativeBoundaryLift cusp degree level boundary
    obtain ⟨last, primitive_mem, primitive_support⟩ := binaryRelativeBoundaryLift_spec cusp degree level boundary
    change primitive (Fin.last (degree + 1)) = boundary.val at last
    have primitive_lower : binaryRelativeLowering cusp basis 0 primitive = lower := by
      funext position
      exact Fin.cases lower_endpoint
        (fun position => (primitive_support position).trans (support position).symm) position
    have primitive_upper : binaryRelativeRaising cusp basis 0 primitive = upper := by
      let new_lower := lower - binaryRelativeLowering cusp basis 0 primitive
      let new_upper := upper - binaryRelativeRaising cusp basis 0 primitive
      have new_closed := binaryRelativeLadder_shift cusp basis lower upper primitive closed
      have new_support (position : Fin (degree + 1)) : new_lower position.succ = 0 := by
        change lower position.succ - binaryRelativeLowering cusp basis 0 primitive position.succ = 0
        rw [support, primitive_support, sub_self]
      have endpoint_zero : new_upper (Fin.last (degree + 1)) = 0 := by
        change upper (Fin.last (degree + 1)) -
          binaryRelativeRaising cusp basis 0 primitive (Fin.last (degree + 1)) = 0
        rw [binaryRelativeRaising_last, zero_add, last, upper_endpoint, sub_self]
      have upper_zero := binaryRelative_normal_form_upper_zero cusp degree new_lower new_upper
        new_closed new_support endpoint_zero
      exact (sub_eq_zero.mp upper_zero).symm
    refine ⟨primitive, fun element position => (primitive_mem position).1 element, ?_, primitive_lower, primitive_upper⟩
    intro angle
    simpa only [zpow_zero, one_smul] using
      binaryFiniteWeightValues_rotation cusp degree level 0 primitive primitive_mem angle

end TernaryPeriodPolynomials.SphericalDetection.Helpers
