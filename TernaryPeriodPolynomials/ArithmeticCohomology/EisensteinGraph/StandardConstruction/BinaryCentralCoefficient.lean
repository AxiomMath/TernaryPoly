module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.NormPower

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryCentralCoefficient

theorem linearForm_scalar (scalar : ℂ) (index : Fin 2) :
    Binary.linearForm (Matrix.scalar (Fin 2) scalar) index = C scalar * X index := by
  fin_cases index <;> simp [Binary.linearForm, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem substitute_scalar_monomial (scalar : ℂ) (index : Fin 2 →₀ ℕ) (coefficient : ℂ) :
    Binary.substitute (Matrix.scalar (Fin 2) scalar) (monomial index coefficient) =
      scalar ^ Finsupp.degree index • monomial index coefficient := by
  simp only [Binary.substitute, linearForm_scalar, bind₁_monomial, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
  rw [monomial_eq, Finsupp.prod, Algebra.smul_def, map_pow]
  change _ = C scalar ^ Finsupp.degree index * (C coefficient * _)
  ring

theorem substitute_scalar {degree : ℕ} (scalar : ℂ) (polynomial : Binary.HomogeneousPoly degree) :
    Binary.substitute (Matrix.scalar (Fin 2) scalar) polynomial.val = scalar ^ degree • polynomial.val := by
  conv_lhs => rw [polynomial.val.as_sum]
  rw [map_sum]
  conv_rhs => rw [polynomial.val.as_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index membership
  rw [substitute_scalar_monomial, Finsupp.degree_apply,
    ← polynomial.property.degree_eq_sum_deg_support membership]

theorem homogeneousAction_scalar (degree : ℕ) (twist : ℤ) (unit : ℂˣ)
    (polynomial : Binary.HomogeneousPoly degree) :
    Binary.homogeneousAction degree twist (GeneralLinearGroup.scalar (Fin 2) unit) polynomial =
      ((unit.val ^ 2) ^ twist * unit.inv ^ degree) • polynomial := by
  apply Subtype.ext
  change Binary.action twist (GeneralLinearGroup.scalar (Fin 2) unit) polynomial.val = _
  rw [Binary.action_apply, ← map_inv, GeneralLinearGroup.coe_scalar, substitute_scalar,
    smul_smul]
  change (((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) unit) : ℂ) ^ twist) *
    unit.inv ^ degree) • polynomial.val = _
  simp only [GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val]
  rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryCentralCoefficient
