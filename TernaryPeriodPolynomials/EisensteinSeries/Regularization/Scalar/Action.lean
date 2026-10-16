module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CentralCharacter

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem homogeneous_rescale
    {degree : ℕ} {polynomial : Binary.Poly}
    (homogeneous : polynomial.IsHomogeneous degree) (scalar : ℂ) :
    (bind₁ (fun coordinate : Fin 2 => C scalar * X coordinate)) polynomial =
      scalar ^ degree • polynomial := by
  classical
  conv_lhs => rw [polynomial.as_sum]
  rw [map_sum]
  conv_rhs => rw [polynomial.as_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro monomial monomial_mem
  have monomial_degree : monomial.degree = degree := by
    by_contra degree_ne
    exact (mem_support_iff.mp monomial_mem) (homogeneous.coeff_eq_zero degree_ne)
  rw [bind₁_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib]
  have scalar_product : monomial.prod (fun _ exponent => (C scalar : Binary.Poly) ^ exponent) =
      C (scalar ^ degree) := by
    rw [Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum]
    have sum_degree : (∑ coordinate, monomial coordinate) = degree := by
      change monomial.sum (fun _ exponent => exponent) = degree at monomial_degree
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at monomial_degree
      exact monomial_degree
    rw [sum_degree, map_pow]
  change C (polynomial.coeff monomial) *
      (monomial.prod (fun _ exponent => C scalar ^ exponent) *
        monomial.prod (fun coordinate exponent => X coordinate ^ exponent)) = _
  rw [scalar_product]
  rw [smul_eq_C_mul, monomial_eq]
  ring

theorem binary_substitute_scalar
    {degree : ℕ} {polynomial : Binary.Poly}
    (homogeneous : polynomial.IsHomogeneous degree) (scalar : ℂˣ) :
    Binary.substitute (GeneralLinearGroup.scalar (Fin 2) scalar) polynomial =
      (scalar : ℂ) ^ degree • polynomial := by
  have linear_form : Binary.linearForm
      (GeneralLinearGroup.scalar (Fin 2) scalar) =
      fun coordinate : Fin 2 => C (scalar : ℂ) * X coordinate := by
    funext coordinate
    fin_cases coordinate <;>
      simp [Binary.linearForm, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply]
  simpa only [Binary.substitute, linear_form] using homogeneous_rescale homogeneous scalar

theorem binary_homogeneous_action_scalar (degree : ℕ) (twist : ℤ)
    (scalar : ℂˣ) (polynomial : Binary.HomogeneousPoly degree) :
    Binary.homogeneousAction degree twist
      (GeneralLinearGroup.scalar (Fin 2) scalar) polynomial =
      ((scalar : ℂ) ^ (2 * twist) * ((scalar : ℂ)⁻¹) ^ degree) • polynomial := by
  apply Subtype.ext
  simp only [Binary.homogeneousAction_coe, Binary.action_apply,
    ← map_inv, binary_substitute_scalar polynomial.property,
    Units.val_inv_eq_inv_val, smul_smul, Submodule.coe_smul_of_tower]
  congr 2
  change (((GeneralLinearGroup.det
    (GeneralLinearGroup.scalar (Fin 2) scalar) : ℂˣ) : ℂ) ^ twist) = _
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val]
  simpa only [zpow_ofNat] using (zpow_mul (scalar : ℂ) 2 twist).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
