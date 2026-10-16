module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CoefficientDerivatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.NilpotentRadicalComparison

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem pderiv_homogeneous_zero (coordinate : Fin 3) (polynomial : Poly)
    (homogeneous : polynomial.IsHomogeneous 0) : pderiv coordinate polynomial = 0 := by
  ext exponent
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have degree_ne : (exponent + Finsupp.single coordinate 1).degree ≠ 0 := by
    rw [map_add, Finsupp.degree_single]
    omega
  rw [homogeneous.coeff_eq_zero degree_ne, zero_mul]

theorem homogeneous_pderiv_power_zero (coordinate : Fin 3) {degree : ℕ}
    (polynomial : Poly) (homogeneous : polynomial.IsHomogeneous degree) :
    ((pderiv coordinate).toLinearMap ^ (degree + 1)) polynomial = 0 := by
  induction degree generalizing polynomial with
  | zero =>
    simpa only [Nat.zero_add, pow_one, Derivation.coeFn_coe] using
      pderiv_homogeneous_zero coordinate polynomial homogeneous
  | succ degree induction =>
    have derivative_degree : (pderiv coordinate polynomial).IsHomogeneous degree := by
      simpa only [Nat.add_sub_cancel] using homogeneous.pderiv (i := coordinate)
    rw [pow_succ, Module.End.mul_apply]
    exact induction _ derivative_degree

def polynomialShearDerivation (coordinate multiplier : Fin 3) : Module.End ℂ Poly where
  toFun polynomial := X multiplier * pderiv coordinate polynomial
  map_add' first second := by rw [map_add, mul_add]
  map_smul' scalar polynomial := by
    simp only [Derivation.map_smul, mul_smul_comm, RingHom.id_apply]

theorem polynomialShearDerivation_power (coordinate multiplier : Fin 3)
    (distinct : multiplier ≠ coordinate) (power : ℕ) (polynomial : Poly) :
    (polynomialShearDerivation coordinate multiplier ^ power) polynomial =
      X multiplier ^ power * ((pderiv coordinate).toLinearMap ^ power) polynomial := by
  induction power with
  | zero => simp
  | succ power induction =>
    rw [pow_succ' (polynomialShearDerivation coordinate multiplier), Module.End.mul_apply]
    change X multiplier * pderiv coordinate
      ((polynomialShearDerivation coordinate multiplier ^ power) polynomial) = _
    rw [induction, pderiv_mul, pderiv_pow, pderiv_X_of_ne distinct, mul_zero, zero_mul, zero_add]
    rw [pow_succ' ((pderiv coordinate).toLinearMap), Module.End.mul_apply, pow_succ']
    exact (mul_assoc _ _ _).symm

theorem polynomialShearDerivation_homogeneous (coordinate multiplier : Fin 3)
    {degree : ℕ} (polynomial : Poly) (homogeneous : polynomial.IsHomogeneous degree) :
    (polynomialShearDerivation coordinate multiplier polynomial).IsHomogeneous degree := by
  by_cases zero : degree = 0
  · subst degree
    change (X multiplier * pderiv coordinate polynomial).IsHomogeneous 0
    rw [pderiv_homogeneous_zero coordinate polynomial homogeneous, mul_zero]
    exact isHomogeneous_zero _ _ _
  · have result := (isHomogeneous_X ℂ multiplier).mul (homogeneous.pderiv (i := coordinate))
    have degree_eq : 1 + (degree - 1) = degree := by omega
    change (X multiplier * pderiv coordinate polynomial).IsHomogeneous degree
    simpa only [degree_eq] using result

def homogeneousShearDerivation (degree : ℕ) (coordinate multiplier : Fin 3) :
    Module.End ℂ (HomogeneousPoly degree) where
  toFun polynomial := ⟨polynomialShearDerivation coordinate multiplier polynomial.val,
    polynomialShearDerivation_homogeneous coordinate multiplier polynomial.val polynomial.property⟩
  map_add' _ _ := Subtype.ext (map_add (polynomialShearDerivation coordinate multiplier) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (polynomialShearDerivation coordinate multiplier) _ _)

theorem homogeneousShearDerivation_power_coe (degree : ℕ) (coordinate multiplier : Fin 3)
    (power : ℕ) (polynomial : HomogeneousPoly degree) :
    ((homogeneousShearDerivation degree coordinate multiplier ^ power) polynomial).val =
      (polynomialShearDerivation coordinate multiplier ^ power) polynomial.val := by
  induction power with
  | zero => rfl
  | succ power induction =>
    rw [pow_succ', pow_succ' (polynomialShearDerivation coordinate multiplier), Module.End.mul_apply, Module.End.mul_apply]
    change polynomialShearDerivation coordinate multiplier
      ((homogeneousShearDerivation degree coordinate multiplier ^ power) polynomial).val = _
    rw [induction]

theorem homogeneousShearDerivation_power_zero (degree : ℕ) (coordinate multiplier : Fin 3)
    (distinct : multiplier ≠ coordinate) :
    homogeneousShearDerivation degree coordinate multiplier ^ (degree + 1) = 0 := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [homogeneousShearDerivation_power_coe, polynomialShearDerivation_power coordinate multiplier distinct,
    homogeneous_pderiv_power_zero coordinate polynomial.val polynomial.property, mul_zero]
  rfl

theorem homogeneousShearDerivation_nilpotent (degree : ℕ) (coordinate multiplier : Fin 3)
    (distinct : multiplier ≠ coordinate) : IsNilpotent (homogeneousShearDerivation degree coordinate multiplier) :=
  ⟨degree + 1, homogeneousShearDerivation_power_zero degree coordinate multiplier distinct⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
