module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.LeviLattice

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem action_mul_linearForm (exponent : ℤ) (matrix : GeneralEisenstein.GL3)
    (coordinate : Fin 3) (polynomial : Poly) :
    action exponent matrix (linearForm matrix.val coordinate * polynomial) =
      X coordinate * action exponent matrix polynomial := by
  have inverse : matrix.val * matrix⁻¹.val = 1 := matrix.val_inv
  simp only [action_apply, map_mul, substitute_linearForm, inverse]
  have form : linearForm (1 : Matrix (Fin 3) (Fin 3) ℂ) coordinate = X coordinate := by
    simp [linearForm, Matrix.one_apply]
  rw [form, mul_smul_comm]

theorem lowerRadicalLevi_boundary (matrix : Binary.GL2) (coordinate : Fin 2) (polynomial : Poly) :
    action (-1) (planeLevi matrix 1)
        (C (matrix.val coordinate 0) * X 0 * pderiv 2 polynomial +
          C (matrix.val coordinate 1) * X 1 * pderiv 2 polynomial) =
      X coordinate.castSucc * pderiv 2 (action (-1) (planeLevi matrix 1) polynomial) := by
  have form : linearForm (planeLevi matrix 1).val coordinate.castSucc =
      C (matrix.val coordinate 0) * X 0 + C (matrix.val coordinate 1) * X 1 := by
    fin_cases coordinate <;> simp [linearForm, planeLevi, planeBlock, Fin.sum_univ_three]
  rw [← add_mul, ← form, action_mul_linearForm, pderiv_action_planeLevi_third]

theorem upperRadicalGenerator_levi (degree : ℕ) (matrix : Binary.GL2) (coordinate : Fin 2) :
    (upperRadicalGenerator degree coordinate).comp (homogeneousAction degree (-1) (planeLevi matrix 1)) =
      (homogeneousAction degree (-1) (planeLevi matrix 1)).comp
        (matrix⁻¹.val 0 coordinate • upperRadicalGenerator degree 0 +
          matrix⁻¹.val 1 coordinate • upperRadicalGenerator degree 1) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change (-1 : ℂ) • (X 2 * pderiv coordinate.castSucc (action (-1) (planeLevi matrix 1) polynomial.val)) =
    action (-1) (planeLevi matrix 1)
      (matrix⁻¹.val 0 coordinate • ((-1 : ℂ) • (X 2 * pderiv 0 polynomial.val)) +
        matrix⁻¹.val 1 coordinate • ((-1 : ℂ) • (X 2 * pderiv 1 polynomial.val)))
  rw [pderiv_action_planeLevi_binary, Fin.sum_univ_two, map_add, map_smul, map_smul,
    map_smul, map_smul, action_planeLevi_mul_third, action_planeLevi_mul_third]
  simp only [Fin.castSucc_zero, Fin.castSucc_one, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring

theorem lowerRadicalGenerator_levi (degree : ℕ) (matrix : Binary.GL2) (coordinate : Fin 2) :
    (lowerRadicalGenerator degree coordinate).comp (homogeneousAction degree (-1) (planeLevi matrix 1)) =
      (homogeneousAction degree (-1) (planeLevi matrix 1)).comp
        (matrix.val coordinate 0 • lowerRadicalGenerator degree 0 +
          matrix.val coordinate 1 • lowerRadicalGenerator degree 1) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  change (-3 : ℂ) • (X coordinate.castSucc * pderiv 2 (action (-1) (planeLevi matrix 1) polynomial.val)) =
    action (-1) (planeLevi matrix 1)
      (matrix.val coordinate 0 • ((-3 : ℂ) • (X 0 * pderiv 2 polynomial.val)) +
        matrix.val coordinate 1 • ((-3 : ℂ) • (X 1 * pderiv 2 polynomial.val)))
  rw [← lowerRadicalLevi_boundary]
  have scalar : matrix.val coordinate 0 • ((-3 : ℂ) • (X 0 * pderiv 2 polynomial.val)) +
      matrix.val coordinate 1 • ((-3 : ℂ) • (X 1 * pderiv 2 polynomial.val)) =
      (-3 : ℂ) • (C (matrix.val coordinate 0) * X 0 * pderiv 2 polynomial.val +
        C (matrix.val coordinate 1) * X 1 * pderiv 2 polynomial.val) := by
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    ring
  rw [scalar, map_smul]

theorem upperLeviLatticeInput_generator (matrix : GeneralLinearGroup (Fin 2) ℤ) (coordinate : Fin 2) :
    upperLeviLatticeInput matrix (radicalLatticeGenerator coordinate) =
      Multiplicative.ofAdd (matrix⁻¹.val 0 coordinate, matrix⁻¹.val 1 coordinate) := by
  fin_cases coordinate <;>
    simp [upperLeviLatticeInput, radicalLatticeGenerator, radicalLatticeFirst, radicalLatticeSecond]

theorem lowerLeviLatticeInput_generator (matrix : GeneralLinearGroup (Fin 2) ℤ) (coordinate : Fin 2) :
    lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate) =
      Multiplicative.ofAdd (matrix.val coordinate 0, matrix.val coordinate 1) := by
  fin_cases coordinate <;>
    simp [lowerLeviLatticeInput, radicalLatticeGenerator, radicalLatticeFirst, radicalLatticeSecond]

theorem upperRadicalGenerator_arithmeticLevi (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (coordinate : Fin 2) :
    (upperRadicalGenerator degree coordinate).comp (arithmeticLeviCoefficient degree matrix) =
      (arithmeticLeviCoefficient degree matrix).comp
        (latticeInfinitesimal (upperRadicalGenerator degree 0) (upperRadicalGenerator degree 1)
          (upperLeviLatticeInput matrix (radicalLatticeGenerator coordinate))) := by
  rw [arithmeticLeviCoefficient_homogeneous, upperLeviLatticeInput_generator]
  have equality := upperRadicalGenerator_levi degree (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) coordinate
  rw [← map_inv] at equality
  exact equality

theorem lowerRadicalGenerator_arithmeticLevi (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (coordinate : Fin 2) :
    (lowerRadicalGenerator degree coordinate).comp (arithmeticLeviCoefficient degree matrix) =
      (arithmeticLeviCoefficient degree matrix).comp
        (latticeInfinitesimal (lowerRadicalGenerator degree 0) (lowerRadicalGenerator degree 1)
          (lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate))) := by
  rw [arithmeticLeviCoefficient_homogeneous, lowerLeviLatticeInput_generator]
  exact lowerRadicalGenerator_levi degree (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) coordinate

end TernaryPeriodPolynomials.SphericalDetection.Helpers
