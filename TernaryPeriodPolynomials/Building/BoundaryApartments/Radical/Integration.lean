module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Cusps

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

def radicalBernoulli (degree : ℕ) (index : Fin 3) : Module.End ℂ (HomogeneousPoly degree) :=
  Polynomial.aeval (radicalDerivative degree index)
    (PowerSeries.trunc (degree + 1) (bernoulliPowerSeries ℚ))

def radicalIntegration (degree : ℕ) (index : Fin 3) : Module.End ℂ (HomogeneousPoly degree) :=
  Polynomial.aeval (radicalDerivative degree index)
    (PowerSeries.trunc (degree + 1) integrationPowerSeries)

theorem polynomial_aeval_commutes {AlgebraType : Type*} [Ring AlgebraType] [Algebra ℚ AlgebraType]
    (element : AlgebraType) (first second : Polynomial ℚ) :
    Commute (Polynomial.aeval element first) (Polynomial.aeval element second) := by
  change Polynomial.aeval element first * Polynomial.aeval element second =
    Polynomial.aeval element second * Polynomial.aeval element first
  rw [← map_mul, ← map_mul, mul_comm first second]

theorem radicalBernoulli_mul_integration (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0) :
    radicalBernoulli degree index * radicalIntegration degree index = 1 :=
  finiteBernoulli_mul_integration (radicalDerivative degree index) degree
    (radicalDerivative_nilpotent degree index index_nonzero)

theorem radicalIntegration_mul_bernoulli (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0) :
    radicalIntegration degree index * radicalBernoulli degree index = 1 := by
  have commute := polynomial_aeval_commutes (radicalDerivative degree index)
    (PowerSeries.trunc (degree + 1) (bernoulliPowerSeries ℚ))
    (PowerSeries.trunc (degree + 1) integrationPowerSeries)
  change radicalBernoulli degree index * radicalIntegration degree index =
    radicalIntegration degree index * radicalBernoulli degree index at commute
  rw [← commute, radicalBernoulli_mul_integration degree index index_nonzero]

theorem radicalBernoulli_injective (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0) :
    Function.Injective (radicalBernoulli degree index) := by
  apply Function.LeftInverse.injective
    (f := radicalBernoulli degree index) (g := radicalIntegration degree index)
  intro polynomial
  rw [← Module.End.mul_apply, radicalIntegration_mul_bernoulli degree index index_nonzero,
    Module.End.one_apply]

theorem radicalIntegration_injective (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0) :
    Function.Injective (radicalIntegration degree index) := by
  apply Function.LeftInverse.injective
    (f := radicalIntegration degree index) (g := radicalBernoulli degree index)
  intro polynomial
  rw [← Module.End.mul_apply, radicalBernoulli_mul_integration degree index index_nonzero,
    Module.End.one_apply]

theorem radicalBernoulli_val (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : HomogeneousPoly degree) :
    (radicalBernoulli degree index polynomial).val =
      bernoulliOperator degree (X index) polynomial.val :=
  bernoulliRadical_aeval degree index index_nonzero polynomial

theorem radicalIntegration_val (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : HomogeneousPoly degree) :
    (radicalIntegration degree index polynomial).val =
      ∑ iterations ∈ Finset.range (degree + 1),
        C (((iterations + 1 : ℕ).factorial : ℂ)⁻¹) * (-X index) ^ iterations *
          ((fun value : Poly => pderiv 0 value)^[iterations]) polynomial.val := by
  rw [radicalIntegration, aeval_trunc_apply_val degree (degree + 1) index index_nonzero]
  apply Finset.sum_congr rfl
  intro iterations _
  have coefficient : PowerSeries.coeff iterations integrationPowerSeries =
      ((iterations + 1 : ℕ).factorial : ℚ)⁻¹ := by
    simp [integrationPowerSeries, PowerSeries.coeff_mk]
  rw [coefficient]
  simp only [Rat.cast_inv, Rat.cast_natCast]

theorem radicalCocycle_lie_relation (degree : ℕ) (first second : HomogeneousPoly degree)
    (cocycle_relation : radicalTranslation degree 1 second - second =
      radicalTranslation degree 2 first - first) :
    X 1 * pderiv 0 (radicalBernoulli degree 2 second).val =
      X 2 * pderiv 0 (radicalBernoulli degree 1 first).val := by
  have binary := radicalCocycle_contraction_binary degree first second cocycle_relation
  simp only [map_sub, pderiv_mul, pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0),
    pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), zero_mul, zero_add] at binary
  rw [radicalBernoulli_val degree 1 (by decide), radicalBernoulli_val degree 2 (by decide)]
  exact (sub_eq_zero.mp binary).symm

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
