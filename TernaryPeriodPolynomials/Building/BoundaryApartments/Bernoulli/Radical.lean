module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Finite

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open MvPolynomial

def radicalDerivative (degree : ℕ) (index : Fin 3) :
    Module.End ℂ (HomogeneousPoly degree) where
  toFun polynomial := ⟨-X index * pderiv 0 polynomial.val, by
    by_cases degree_zero : degree = 0
    · subst degree
      rw [derivative_homogeneous_zero polynomial.property, mul_zero]
      exact isHomogeneous_zero _ _ _
    · have homogeneous := (isHomogeneous_X ℂ index).neg.mul
        (polynomial.property.pderiv (i := (0 : Fin 3)))
      have degree_eq : 1 + (degree - 1) = degree := by omega
      rw [degree_eq] at homogeneous
      exact homogeneous⟩
  map_add' first second := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add, mul_add]
  map_smul' scalar polynomial := by
    apply Subtype.ext
    change -X index * pderiv 0 (scalar • polynomial.val) =
      scalar • (-X index * pderiv 0 polynomial.val)
    simp only [MvPolynomial.smul_eq_C_mul, pderiv_C_mul]
    ring

theorem radicalDerivative_pow_val (degree : ℕ) (index : Fin 3)
    (index_nonzero : index ≠ 0) (iterations : ℕ) (polynomial : HomogeneousPoly degree) :
    ((radicalDerivative degree index ^ iterations) polynomial).val =
      (-X index) ^ iterations *
        ((fun value : Poly => pderiv 0 value)^[iterations]) polynomial.val := by
  induction iterations with
  | zero => simp
  | succ iterations induction_hypothesis =>
    rw [pow_succ', Module.End.mul_apply]
    change -X index * pderiv 0 ((radicalDerivative degree index ^ iterations) polynomial).val = _
    rw [induction_hypothesis, pderiv_mul]
    have derivative_power : pderiv 0 ((-X index : Poly) ^ iterations) = 0 := by
      simp [index_nonzero]
    rw [derivative_power, zero_mul, zero_add, pow_succ',
      Function.iterate_succ_apply']
    ring

theorem radicalDerivative_nilpotent (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0) :
    radicalDerivative degree index ^ (degree + 1) = 0 := by
  apply LinearMap.ext
  intro polynomial
  apply Subtype.ext
  rw [radicalDerivative_pow_val degree index index_nonzero,
    derivative_iterate_terminates polynomial.property, mul_zero]
  rfl

theorem aeval_trunc_apply_val (degree bound : ℕ) (index : Fin 3)
    (index_nonzero : index ≠ 0) (series : PowerSeries ℚ) (polynomial : HomogeneousPoly degree) :
    ((Polynomial.aeval (radicalDerivative degree index)
      (PowerSeries.trunc bound series)) polynomial).val =
      ∑ iterations ∈ Finset.range bound,
        C (((PowerSeries.coeff iterations series : ℚ) : ℂ)) * (-X index) ^ iterations *
          ((fun value : Poly => pderiv 0 value)^[iterations]) polynomial.val := by
  rw [PowerSeries.trunc_apply, ← Finset.range_eq_Ico, map_sum]
  simp only [LinearMap.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro iterations _
  rw [Polynomial.aeval_monomial, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one]
  simp only [LinearMap.smul_apply, Module.End.one_apply,
    ← Rat.cast_smul_eq_qsmul ℂ, Submodule.coe_smul,
    radicalDerivative_pow_val degree index index_nonzero, MvPolynomial.smul_eq_C_mul,
    mul_assoc]

theorem bernoulliRadical_aeval (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : HomogeneousPoly degree) :
    ((Polynomial.aeval (radicalDerivative degree index)
      (PowerSeries.trunc (degree + 1) (bernoulliPowerSeries ℚ))) polynomial).val =
        bernoulliOperator degree (X index) polynomial.val := by
  rw [aeval_trunc_apply_val degree (degree + 1) index index_nonzero]
  unfold bernoulliOperator
  apply Finset.sum_congr rfl
  intro iterations _
  have coefficient : PowerSeries.coeff iterations (bernoulliPowerSeries ℚ) =
      bernoulli iterations / (iterations.factorial : ℚ) := by
    simp [bernoulliPowerSeries, PowerSeries.coeff_mk]
  rw [coefficient]
  norm_cast

theorem aeval_trunc_degree_bound (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0)
    (series : PowerSeries ℚ) :
    Polynomial.aeval (radicalDerivative degree index) (PowerSeries.trunc (degree + 2) series) =
      Polynomial.aeval (radicalDerivative degree index) (PowerSeries.trunc (degree + 1) series) := by
  rw [polynomial_aeval_trunc (radicalDerivative degree index) (degree + 1)
    (radicalDerivative_nilpotent degree index index_nonzero)
    (PowerSeries.trunc (degree + 2) series)]
  rw [PowerSeries.trunc_trunc_of_le series (by omega)]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
