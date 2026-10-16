module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Algebra
public import Mathlib.RingTheory.PowerSeries.Trunc

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

variable {AlgebraType : Type*} [Ring AlgebraType] [Algebra ℚ AlgebraType]

def integrationPowerSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun iterations => ((iterations + 1 : ℕ).factorial : ℚ)⁻¹)

theorem integrationPowerSeries_mul_X :
    integrationPowerSeries * PowerSeries.X = PowerSeries.exp ℚ - 1 := by
  have shifted := PowerSeries.sub_const_eq_shift_mul_X (PowerSeries.exp ℚ)
  have coefficients :
      PowerSeries.mk (fun iterations => PowerSeries.coeff (iterations + 1) (PowerSeries.exp ℚ)) =
        integrationPowerSeries := by
    apply PowerSeries.ext
    intro iterations
    simp [integrationPowerSeries, PowerSeries.coeff_mk, PowerSeries.coeff_exp]
  rw [coefficients] at shifted
  simpa using shifted.symm

theorem bernoulliPowerSeries_mul_integration :
    bernoulliPowerSeries ℚ * integrationPowerSeries = 1 := by
  apply PowerSeries.X_mul_injective
  have identity := bernoulliPowerSeries_mul_exp_sub_one ℚ
  rw [← integrationPowerSeries_mul_X, ← mul_assoc] at identity
  simpa only [mul_comm, mul_one, one_mul] using identity

theorem polynomial_aeval_trunc (element : AlgebraType) (bound : ℕ)
    (nilpotent : element ^ bound = 0) (polynomial : Polynomial ℚ) :
    Polynomial.aeval element polynomial =
      Polynomial.aeval element (PowerSeries.trunc bound (polynomial : PowerSeries ℚ)) := by
  have divisible : Polynomial.X ^ bound ∣
      polynomial - PowerSeries.trunc bound (polynomial : PowerSeries ℚ) := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro index index_lt
    simp only [Polynomial.coeff_sub, PowerSeries.coeff_trunc, ite_eq_left index_lt,
      Polynomial.coeff_coe, sub_self]
  obtain ⟨quotient, equality⟩ := divisible
  have zero_evaluation : Polynomial.aeval element
      (polynomial - PowerSeries.trunc bound (polynomial : PowerSeries ℚ)) = 0 := by
    rw [equality, map_mul, map_pow, Polynomial.aeval_X, nilpotent, zero_mul]
  simpa only [map_sub, sub_eq_zero] using zero_evaluation

theorem finiteBernoulli_mul_exp_sub_one (element : AlgebraType) (degree : ℕ)
    (nilpotent : element ^ (degree + 2) = 0) :
    Polynomial.aeval element
        (PowerSeries.trunc (degree + 2) (bernoulliPowerSeries ℚ)) *
      (Polynomial.aeval element
        (PowerSeries.trunc (degree + 2) (PowerSeries.exp ℚ)) - 1) = element := by
  let bernoulli_polynomial := PowerSeries.trunc (degree + 2) (bernoulliPowerSeries ℚ)
  let exponential_polynomial := PowerSeries.trunc (degree + 2) (PowerSeries.exp ℚ)
  have truncate : PowerSeries.trunc (degree + 2)
      ((bernoulli_polynomial * (exponential_polynomial - 1) : Polynomial ℚ) : PowerSeries ℚ) =
        PowerSeries.trunc (degree + 2)
          (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) := by
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one]
    dsimp only [bernoulli_polynomial, exponential_polynomial]
    have subtract_one :
        (PowerSeries.trunc (degree + 2) (PowerSeries.exp ℚ - 1) : PowerSeries ℚ) =
          (PowerSeries.trunc (degree + 2) (PowerSeries.exp ℚ) : PowerSeries ℚ) - 1 := by
      simp only [PowerSeries.trunc_sub, PowerSeries.trunc_one, Polynomial.coe_sub,
        Polynomial.coe_one]
    rw [← subtract_one, PowerSeries.trunc_trunc_mul_trunc]
  change Polynomial.aeval element bernoulli_polynomial *
    (Polynomial.aeval element exponential_polynomial - 1) = element
  rw [← map_one (Polynomial.aeval (R := ℚ) element), ← map_sub, ← map_mul,
    polynomial_aeval_trunc element (degree + 2) nilpotent, truncate,
    bernoulliPowerSeries_mul_exp_sub_one, PowerSeries.trunc_X, Polynomial.aeval_X]

theorem finiteBernoulli_mul_integration (element : AlgebraType) (bound : ℕ)
    (nilpotent : element ^ (bound + 1) = 0) :
    Polynomial.aeval element (PowerSeries.trunc (bound + 1) (bernoulliPowerSeries ℚ)) *
      Polynomial.aeval element (PowerSeries.trunc (bound + 1) integrationPowerSeries) = 1 := by
  rw [← map_mul, polynomial_aeval_trunc element (bound + 1) nilpotent]
  simp only [Polynomial.coe_mul]
  rw [PowerSeries.trunc_trunc_mul_trunc, bernoulliPowerSeries_mul_integration,
    PowerSeries.trunc_one, map_one]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
