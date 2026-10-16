module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.DerivativeNilpotence

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem polynomialShearDerivation_commute (first second first_multiplier second_multiplier : Fin 3)
    (first_distinct : second_multiplier ≠ first) (second_distinct : first_multiplier ≠ second) :
    Commute (polynomialShearDerivation first first_multiplier)
      (polynomialShearDerivation second second_multiplier) := by
  apply LinearMap.ext
  intro polynomial
  change X first_multiplier * pderiv first (X second_multiplier * pderiv second polynomial) =
    X second_multiplier * pderiv second (X first_multiplier * pderiv first polynomial)
  rw [pderiv_mul, pderiv_mul, pderiv_X_of_ne first_distinct, pderiv_X_of_ne second_distinct,
    zero_mul, zero_mul, zero_add, zero_add, pderiv_commute first second]
  ring

theorem homogeneousShearDerivation_commute (degree : ℕ)
    (first second first_multiplier second_multiplier : Fin 3)
    (first_distinct : second_multiplier ≠ first) (second_distinct : first_multiplier ≠ second) :
    Commute (homogeneousShearDerivation degree first first_multiplier)
      (homogeneousShearDerivation degree second second_multiplier) := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  exact congrArg (fun operator : Module.End ℂ Poly => operator polynomial.val)
    (polynomialShearDerivation_commute first second first_multiplier second_multiplier
      first_distinct second_distinct).eq

def upperRadicalGenerator (degree : ℕ) (coordinate : Fin 2) : Module.End ℂ (HomogeneousPoly degree) :=
  (-1 : ℂ) • homogeneousShearDerivation degree coordinate.castSucc 2

/-- The lower generator uses the actual arithmetic lattice step three. -/
def lowerRadicalGenerator (degree : ℕ) (coordinate : Fin 2) : Module.End ℂ (HomogeneousPoly degree) :=
  (-3 : ℂ) • homogeneousShearDerivation degree 2 coordinate.castSucc

theorem upperRadicalGenerator_power_zero (degree : ℕ) (coordinate : Fin 2) :
    upperRadicalGenerator degree coordinate ^ (degree + 1) = 0 := by
  rw [upperRadicalGenerator, smul_pow,
    homogeneousShearDerivation_power_zero degree coordinate.castSucc 2
      (Ne.symm (Fin.castSucc_ne_last coordinate)), smul_zero]

theorem lowerRadicalGenerator_power_zero (degree : ℕ) (coordinate : Fin 2) :
    lowerRadicalGenerator degree coordinate ^ (degree + 1) = 0 := by
  rw [lowerRadicalGenerator, smul_pow,
    homogeneousShearDerivation_power_zero degree 2 coordinate.castSucc
      (Fin.castSucc_ne_last coordinate), smul_zero]

theorem upperRadicalGenerators_commute (degree : ℕ) :
    Commute (upperRadicalGenerator degree 0) (upperRadicalGenerator degree 1) := by
  exact ((homogeneousShearDerivation_commute degree 0 1 2 2 (by decide) (by decide)).smul_left
    (-1 : ℂ)).smul_right (-1 : ℂ)

theorem lowerRadicalGenerators_commute (degree : ℕ) :
    Commute (lowerRadicalGenerator degree 0) (lowerRadicalGenerator degree 1) := by
  exact ((homogeneousShearDerivation_commute degree 2 2 0 1 (by decide) (by decide)).smul_left
    (-3 : ℂ)).smul_right (-3 : ℂ)

theorem upperRadicalGenerator_first_derivative {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (realCoefficientComponent degree trivialCharacter (planeUnipotent parameter 0) polynomial).val.coeff monomial)
      ((upperRadicalGenerator degree 0 polynomial).val.coeff monomial) 0 := by
  have derivative := real_planeUnipotent_coefficient_derivative 1 0 polynomial monomial
  simpa [upperRadicalGenerator, homogeneousShearDerivation, polynomialShearDerivation] using derivative

theorem upperRadicalGenerator_second_derivative {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (realCoefficientComponent degree trivialCharacter (planeUnipotent 0 parameter) polynomial).val.coeff monomial)
      ((upperRadicalGenerator degree 1 polynomial).val.coeff monomial) 0 := by
  have derivative := real_planeUnipotent_coefficient_derivative 0 1 polynomial monomial
  simpa [upperRadicalGenerator, homogeneousShearDerivation, polynomialShearDerivation] using derivative

theorem lowerRadicalGenerator_first_derivative {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (realCoefficientComponent degree trivialCharacter (lowerPlaneUnipotent (parameter * 3) 0) polynomial).val.coeff monomial)
      ((lowerRadicalGenerator degree 0 polynomial).val.coeff monomial) 0 := by
  have derivative := real_lowerPlaneUnipotent_coefficient_derivative 3 0 polynomial monomial
  simpa [lowerRadicalGenerator, homogeneousShearDerivation, polynomialShearDerivation,
    Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_assoc] using derivative

theorem lowerRadicalGenerator_second_derivative {degree : ℕ}
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter : ℝ => (realCoefficientComponent degree trivialCharacter (lowerPlaneUnipotent 0 (parameter * 3)) polynomial).val.coeff monomial)
      ((lowerRadicalGenerator degree 1 polynomial).val.coeff monomial) 0 := by
  have derivative := real_lowerPlaneUnipotent_coefficient_derivative 0 3 polynomial monomial
  simpa [lowerRadicalGenerator, homogeneousShearDerivation, polynomialShearDerivation,
    Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_assoc] using derivative

end TernaryPeriodPolynomials.SphericalDetection.Helpers
