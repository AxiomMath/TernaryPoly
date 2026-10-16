module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeEndpoints

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The last coordinate and the positive-index lowering coordinates determine the vector. -/
theorem binaryRelativeLowering_ext_of_last (cusp : CuspidalRepresentation) (degree : ℕ)
    (first second : binarySmoothValues cusp (Fin (degree + 2)))
    (last : first (Fin.last (degree + 1)) = second (Fin.last (degree + 1)))
    (lower : ∀ position : Fin (degree + 1),
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 first position.succ =
        binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 second position.succ) :
    first = second := by
  funext position
  refine Fin.reverseInduction last (fun position successor_equal => ?_) position
  have equality := lower position
  rw [binaryRelativeLowering_succ, binaryRelativeLowering_succ, successor_equal] at equality
  have scaled := add_right_cancel equality
  have difference_zero : (Complex.I * ((degree + 1 - position.val : ℕ) : ℂ)) •
      (first position.castSucc - second position.castSucc) = 0 := by
    rw [smul_sub, scaled, sub_self]
  apply sub_eq_zero.mp
  apply (smul_eq_zero.mp difference_zero).resolve_left
  apply mul_ne_zero Complex.I_ne_zero
  have positive : 0 < degree + 1 - position.val := by omega
  exact_mod_cast (ne_of_gt positive)

/-- The unique finite-level lift whose lowering coordinates vanish away from zero. -/
def binaryRelativeBoundaryLift (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL)
    (boundary : cuspFiniteWeightValues cusp level (degree + 1 : ℕ)) :
    binarySmoothValues cusp (Fin (degree + 2)) :=
  (binaryRelativeLowering_lift_boundary cusp degree level boundary.val boundary.property).choose

theorem binaryRelativeBoundaryLift_spec (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL)
    (boundary : cuspFiniteWeightValues cusp level (degree + 1 : ℕ)) :
    binaryRelativeBoundaryLift cusp degree level boundary (Fin.last (degree + 1)) = boundary.val ∧
    (∀ position, binaryRelativeBoundaryLift cusp degree level boundary position ∈
      cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 0 position)) ∧
    (∀ position : Fin (degree + 1), binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0
      (binaryRelativeBoundaryLift cusp degree level boundary) position.succ = 0) :=
  (binaryRelativeLowering_lift_boundary cusp degree level boundary.val boundary.property).choose_spec

theorem binaryRelativeBoundaryLift_eq (cusp : CuspidalRepresentation) (degree : ℕ)
    (level : Subgroup BinaryFiniteGL)
    (boundary : cuspFiniteWeightValues cusp level (degree + 1 : ℕ))
    (primitive : binarySmoothValues cusp (Fin (degree + 2)))
    (last : primitive (Fin.last (degree + 1)) = boundary.val)
    (support : ∀ position : Fin (degree + 1),
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 primitive position.succ = 0) :
    binaryRelativeBoundaryLift cusp degree level boundary = primitive := by
  apply binaryRelativeLowering_ext_of_last cusp degree
  · exact (binaryRelativeBoundaryLift_spec cusp degree level boundary).1.trans last.symm
  · intro position
    exact ((binaryRelativeBoundaryLift_spec cusp degree level boundary).2.2 position).trans (support position).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
