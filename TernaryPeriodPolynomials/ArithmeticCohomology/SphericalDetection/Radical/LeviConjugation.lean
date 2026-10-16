module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CoefficientDerivatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LeviCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem planeLevi_planeUnipotent_commute {R : Type*} [CommRing R]
    (matrix : GeneralLinearGroup (Fin 2) R) (first second : R) :
    planeLevi matrix 1 * planeUnipotent first second =
      planeUnipotent (matrix.val 0 0 * first + matrix.val 0 1 * second)
        (matrix.val 1 0 * first + matrix.val 1 1 * second) * planeLevi matrix 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, planeUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem lowerPlaneUnipotent_planeLevi_commute {R : Type*} [CommRing R]
    (matrix : GeneralLinearGroup (Fin 2) R) (first second : R) :
    lowerPlaneUnipotent first second * planeLevi matrix 1 =
      planeLevi matrix 1 * lowerPlaneUnipotent
        (first * matrix.val 0 0 + second * matrix.val 1 0)
        (first * matrix.val 0 1 + second * matrix.val 1 1) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, lowerPlaneUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem planeLevi_inverse_conjugate_planeUnipotent (matrix : Binary.GL2) (first second : ℂ) :
    (planeLevi matrix 1)⁻¹ * planeUnipotent first second * planeLevi matrix 1 =
      planeUnipotent (matrix⁻¹.val 0 0 * first + matrix⁻¹.val 0 1 * second)
        (matrix⁻¹.val 1 0 * first + matrix⁻¹.val 1 1 * second) := by
  have equation := planeLevi_planeUnipotent_commute matrix⁻¹ first second
  have inverse : planeLevi matrix⁻¹ 1 = (planeLevi matrix 1)⁻¹ := by
    rw [planeLevi_inverse, inv_one]
  rw [inverse] at equation
  rw [equation, mul_assoc, inv_mul_cancel, mul_one]

theorem planeLevi_inverse_conjugate_lowerPlaneUnipotent (matrix : Binary.GL2) (first second : ℂ) :
    (planeLevi matrix 1)⁻¹ * lowerPlaneUnipotent first second * planeLevi matrix 1 =
      lowerPlaneUnipotent (first * matrix.val 0 0 + second * matrix.val 1 0)
        (first * matrix.val 0 1 + second * matrix.val 1 1) := by
  rw [mul_assoc, lowerPlaneUnipotent_planeLevi_commute, inv_mul_cancel_left]

theorem planeRadicalLeviPair_homogeneous {degree : ℕ} (matrix : Binary.GL2) (pair : Fin 2 → Poly)
    (homogeneous : ∀ index, (pair index).IsHomogeneous degree) (coordinate : Fin 2) :
    (planeRadicalLeviPair matrix pair coordinate).IsHomogeneous degree := by
  apply IsHomogeneous.sum
  intro index _
  exact (action_homogeneous (-1) (planeLevi matrix 1) (homogeneous index)).C_mul _

theorem lowerRadicalLeviPair_homogeneous {degree : ℕ} (matrix : Binary.GL2) (pair : Fin 2 → Poly)
    (homogeneous : ∀ index, (pair index).IsHomogeneous degree) (coordinate : Fin 2) :
    (lowerRadicalLeviPair matrix pair coordinate).IsHomogeneous degree := by
  apply IsHomogeneous.sum
  intro index _
  exact (action_homogeneous (-1) (planeLevi matrix 1) (homogeneous index)).C_mul _

theorem planeRadicalLeviPair_closed (matrix : Binary.GL2) (pair : Fin 2 → Poly)
    (closed : X 2 * pderiv 0 (pair 1) = X 2 * pderiv 1 (pair 0)) :
    X 2 * pderiv 0 (planeRadicalLeviPair matrix pair 1) =
      X 2 * pderiv 1 (planeRadicalLeviPair matrix pair 0) := by
  have derivatives := mul_left_cancel₀ (X_ne_zero (2 : Fin 3)) closed
  have first := pderiv_action_planeLevi_binary (-1) matrix (0 : Fin 2)
  have second := pderiv_action_planeLevi_binary (-1) matrix (1 : Fin 2)
  dsimp only [Fin.castSucc_zero, Fin.castSucc_one] at first second
  simp only [planeRadicalLeviPair, Fin.sum_univ_two, map_add, pderiv_C_mul, first, second]
  simp only [Fin.castSucc_zero, Fin.castSucc_one, derivatives]
  ring

theorem lowerRadicalLeviPair_closed (matrix : Binary.GL2) (pair : Fin 2 → Poly)
    (closed : X 0 * pderiv 2 (pair 1) = X 1 * pderiv 2 (pair 0)) :
    X 0 * pderiv 2 (lowerRadicalLeviPair matrix pair 1) =
      X 1 * pderiv 2 (lowerRadicalLeviPair matrix pair 0) := by
  have derivative_zero := lowerRadicalContraction_pderiv_third (pair 0) (pair 1) closed
  have equation := congrArg (pderiv (2 : Fin 3)) (lowerRadicalLeviPair_contraction matrix pair)
  rw [pderiv_substitute_planeBlock_third, derivative_zero, map_zero, mul_zero] at equation
  simp only [lowerRadicalContraction, map_sub, pderiv_mul,
    pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2), zero_mul, zero_add] at equation
  exact (sub_eq_zero.mp equation).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
