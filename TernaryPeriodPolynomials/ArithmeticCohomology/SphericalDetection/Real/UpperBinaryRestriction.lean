module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBinarySection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRestrict_upperAction_last_derivative (first second : ℂ) (polynomial : Binary.Poly) :
    binaryPolynomialRestrict (pderiv 2
        (action (-1) (planeUnipotent first second) (binaryPolynomialLift polynomial))) =
      -first • pderiv 0 polynomial + -second • pderiv 1 polynomial := by
  have determinant : determinantCharacter (-1) (planeUnipotent first second) = 1 := by
    change ((planeUnipotent first second).val.det) ^ (-1 : ℤ) = 1
    simp [planeUnipotent, Matrix.det_fin_three]
  have invariant (input : Poly) :
      binaryPolynomialRestrict (substitute (planeUnipotent first second)⁻¹.val input) =
        binaryPolynomialRestrict input := by
    simpa only [action_apply, determinant, one_smul] using
      binaryPolynomialRestrict_planeUnipotent first second input
  have first_derivative : binaryPolynomialRestrict (pderiv 0 (binaryPolynomialLift polynomial)) =
      pderiv 0 polynomial := by
    exact (congrArg binaryPolynomialRestrict (binaryPolynomialLift_pderiv (0 : Fin 2) polynomial)).trans
      (binaryPolynomialRestrict_lift _)
  have second_derivative : binaryPolynomialRestrict (pderiv 1 (binaryPolynomialLift polynomial)) =
      pderiv 1 polynomial := by
    exact (congrArg binaryPolynomialRestrict (binaryPolynomialLift_pderiv (1 : Fin 2) polynomial)).trans
      (binaryPolynomialRestrict_lift _)
  rw [action_apply, determinant, one_smul, pderiv_substitute, Fin.sum_univ_three]
  simp only [map_add, map_mul, invariant,
    first_derivative, second_derivative, binaryPolynomialLift_pderiv_third, map_zero, mul_zero, add_zero]
  simp [planeUnipotent, Algebra.smul_def]

theorem realUpperBinarySection_restrict (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1))
    (element : RealPlaneRadical) :
    binaryPolynomialRestrict (realUpperBinarySection degree polynomial element).val =
      (element.toAdd 0 : ℂ) • pderiv 0 polynomial.val +
        (element.toAdd 1 : ℂ) • pderiv 1 polynomial.val := by
  let difference : HomogeneousPoly (degree + 1) := binaryHomogeneousLift (degree + 1) polynomial -
    (realUpperRadicalRep (degree + 1)).ρ element (binaryHomogeneousLift (degree + 1) polynomial)
  have zero : binaryHomogeneousRestrict (degree + 1) difference = 0 := by
    change binaryHomogeneousRestrict (degree + 1)
      (binaryHomogeneousLift (degree + 1) polynomial -
        (realUpperRadicalRep (degree + 1)).ρ element (binaryHomogeneousLift (degree + 1) polynomial)) = 0
    rw [map_sub, binaryHomogeneousRestrict_realUpper, sub_self]
  change binaryPolynomialRestrict (homogeneousLastDivide degree difference).val = _
  rw [binaryRestrict_lastDivide degree difference zero]
  have difference_value : difference.val = binaryPolynomialLift polynomial.val -
      action (-1) (planeUnipotent (element.toAdd 0 : ℂ) (element.toAdd 1 : ℂ))
        (binaryPolynomialLift polynomial.val) := by
    change binaryPolynomialLift polynomial.val -
      (realCoefficientComponent (degree + 1) trivialCharacter
        (planeUnipotent (element.toAdd 0) (element.toAdd 1)) (binaryHomogeneousLift (degree + 1) polynomial)).val = _
    rw [realCoefficientComponent_trivial, map_planeUnipotent]
    rfl
  rw [difference_value, map_sub, binaryPolynomialLift_pderiv_third, map_sub, map_zero,
    binaryRestrict_upperAction_last_derivative]
  simp only [neg_smul]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
