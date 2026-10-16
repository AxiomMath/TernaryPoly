module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.Taylor
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.Generators

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def shearPolynomialCurve (coordinate multiplier : Fin 3) (scalar : ℂ) :
    Poly →ₐ[ℂ] Polynomial Poly :=
  MvPolynomial.aeval (fun index => Polynomial.C (X index) +
    if index = coordinate then Polynomial.C (C scalar * X multiplier) * Polynomial.X else 0)

theorem shearPolynomialCurve_X (coordinate multiplier index : Fin 3) (scalar : ℂ) :
    shearPolynomialCurve coordinate multiplier scalar (X index) =
      Polynomial.C (X index) +
        if index = coordinate then Polynomial.C (C scalar * X multiplier) * Polynomial.X else 0 := by
  simp [shearPolynomialCurve]

theorem shearPolynomialCurve_C (coordinate multiplier : Fin 3) (scalar constant : ℂ) :
    shearPolynomialCurve coordinate multiplier scalar (C constant) = Polynomial.C (C constant) := by
  simp [shearPolynomialCurve, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem shearPolynomialCurve_derivative_X (coordinate multiplier index : Fin 3) (scalar : ℂ) :
    Polynomial.derivative (shearPolynomialCurve coordinate multiplier scalar (X index)) =
      if index = coordinate then Polynomial.C (C scalar * X multiplier) else 0 := by
  rw [shearPolynomialCurve_X]
  by_cases equality : index = coordinate <;> simp [equality]

theorem shearPolynomialCurve_derivative (coordinate multiplier : Fin 3) (scalar : ℂ)
    (distinct : multiplier ≠ coordinate) (polynomial : Poly) :
    Polynomial.derivative (shearPolynomialCurve coordinate multiplier scalar polynomial) =
      shearPolynomialCurve coordinate multiplier scalar
        (scalar • polynomialShearDerivation coordinate multiplier polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C constant => simp [polynomialShearDerivation]
  | add first second first_eq second_eq =>
    simp only [map_add, first_eq, second_eq, smul_add]
  | mul_X polynomial generator equality =>
    have shear_product : polynomialShearDerivation coordinate multiplier (polynomial * X generator) =
        polynomialShearDerivation coordinate multiplier polynomial * X generator +
          polynomial * (X multiplier * pderiv coordinate (X generator)) := by
      change X multiplier * pderiv coordinate (polynomial * X generator) =
        (X multiplier * pderiv coordinate polynomial) * X generator +
          polynomial * (X multiplier * pderiv coordinate (X generator))
      rw [pderiv_mul]
      ring
    rw [map_mul, Polynomial.derivative_mul, equality, shearPolynomialCurve_derivative_X,
      shear_product, smul_add, map_add]
    congr 1
    · rw [← smul_mul_assoc]
      exact (map_mul (shearPolynomialCurve coordinate multiplier scalar) _ _).symm
    · rw [← mul_smul_comm, map_mul]
      by_cases same : generator = coordinate
      · subst generator
        simp [Algebra.smul_def, MvPolynomial.algebraMap_eq,
          shearPolynomialCurve_X, distinct]
      · simp [pderiv_X_of_ne same, same]

theorem shearPolynomialCurve_eval_zero (coordinate multiplier : Fin 3) (scalar : ℂ) (polynomial : Poly) :
    Polynomial.eval 0 (shearPolynomialCurve coordinate multiplier scalar polynomial) = polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C constant => simp
  | add first second first_eq second_eq => simp [first_eq, second_eq]
  | mul_X polynomial generator equality =>
    rw [map_mul, Polynomial.eval_mul, equality, shearPolynomialCurve_X]
    by_cases same : generator = coordinate <;> simp [same]

theorem shearPolynomialCurve_iterated_derivative (coordinate multiplier : Fin 3) (scalar : ℂ)
    (distinct : multiplier ≠ coordinate) (power : ℕ) (polynomial : Poly) :
    (Polynomial.derivative : Polynomial Poly → Polynomial Poly)^[power]
        (shearPolynomialCurve coordinate multiplier scalar polynomial) =
      shearPolynomialCurve coordinate multiplier scalar
        (((scalar • polynomialShearDerivation coordinate multiplier) ^ power) polynomial) := by
  induction power with
  | zero => rfl
  | succ power equality =>
    rw [Function.iterate_succ_apply', equality, shearPolynomialCurve_derivative _ _ _ distinct,
      pow_succ', Module.End.mul_apply]
    rfl

theorem shearPolynomialCurve_finite_taylor {degree : ℕ} (coordinate multiplier : Fin 3) (scalar : ℂ)
    (distinct : multiplier ≠ coordinate) (polynomial : HomogeneousPoly degree) :
    Polynomial.eval 1 (shearPolynomialCurve coordinate multiplier scalar polynomial.val) =
      ∑ power ∈ Finset.range (degree + 1), (power.factorial : ℚ)⁻¹ •
        (((scalar • polynomialShearDerivation coordinate multiplier) ^ power) polynomial.val) := by
  have vanishes : (Polynomial.derivative : Polynomial Poly → Polynomial Poly)^[degree + 1]
      (shearPolynomialCurve coordinate multiplier scalar polynomial.val) = 0 := by
    rw [shearPolynomialCurve_iterated_derivative _ _ _ distinct, smul_pow, LinearMap.smul_apply,
      polynomialShearDerivation_power _ _ distinct,
      homogeneous_pderiv_power_zero coordinate polynomial.val polynomial.property, mul_zero, smul_zero, map_zero]
  rw [polynomial_finite_taylor_one _ (degree + 1) (Nat.succ_pos degree) vanishes]
  apply Finset.sum_congr rfl
  intro power _
  rw [shearPolynomialCurve_iterated_derivative _ _ _ distinct, shearPolynomialCurve_eval_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
