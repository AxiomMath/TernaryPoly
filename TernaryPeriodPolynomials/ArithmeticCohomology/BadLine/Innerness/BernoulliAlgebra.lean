module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

section NilpotentEvaluation

variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem nilpotent_aeval_eq_of_coeff {N : ℕ} (D : R) (nilpotent : D^N = 0)
    (p q : Polynomial ℂ) (coefficients : ∀ k < N, p.coeff k = q.coeff k) :
    Polynomial.aeval D p = Polynomial.aeval D q := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  have divisibility : (Polynomial.X : Polynomial ℂ)^N ∣ p-q := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k bounded
    rw [Polynomial.coeff_sub, coefficients k bounded, sub_self]
  obtain ⟨factor, factorization⟩ := divisibility
  rw [factorization, map_mul, map_pow, Polynomial.aeval_X, nilpotent, zero_mul]

theorem nilpotent_aeval_trunc {N : ℕ} (D : R) (nilpotent : D^N = 0)
    (p : Polynomial ℂ) :
    Polynomial.aeval D (PowerSeries.trunc N (p : PowerSeries ℂ)) =
      Polynomial.aeval D p := by
  apply nilpotent_aeval_eq_of_coeff D nilpotent
  intro k bounded
  simp only [PowerSeries.coeff_trunc, ite_eq_left bounded, Polynomial.coeff_coe]

theorem nilpotent_aeval_trunc_mul {N : ℕ} (D : R) (nilpotent : D^N = 0)
    (p q : PowerSeries ℂ) :
    Polynomial.aeval D (PowerSeries.trunc N (p*q)) =
      Polynomial.aeval D (PowerSeries.trunc N p) *
        Polynomial.aeval D (PowerSeries.trunc N q) := by
  rw [← PowerSeries.trunc_trunc_mul_trunc p q]
  rw [← Polynomial.coe_mul, nilpotent_aeval_trunc D nilpotent, map_mul]

theorem nilpotent_bernoulli_identity {N : ℕ} (bound : 2 ≤ N)
    (D : R) (nilpotent : D^N = 0) :
    Polynomial.aeval D (PowerSeries.trunc N (bernoulliPowerSeries ℂ)) *
      (Polynomial.aeval D (PowerSeries.trunc N (PowerSeries.exp ℂ)) - 1) = D := by
  have identity := congrArg (fun series : PowerSeries ℂ =>
    Polynomial.aeval D (PowerSeries.trunc N series))
      (bernoulliPowerSeries_mul_exp_sub_one ℂ)
  rw [nilpotent_aeval_trunc_mul D nilpotent, PowerSeries.trunc_sub,
    map_sub, PowerSeries.trunc_X_of bound, Polynomial.aeval_X] at identity
  have trunc_one : PowerSeries.trunc N (1 : PowerSeries ℂ) = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    exact PowerSeries.trunc_one k
  simpa only [trunc_one, map_one] using identity

theorem aeval_trunc_bernoulli (N : ℕ) (D : R) :
    Polynomial.aeval D (PowerSeries.trunc N (bernoulliPowerSeries ℂ)) =
      ∑ k ∈ Finset.range N, ((bernoulli k : ℂ) / (k.factorial : ℂ)) • D^k := by
  rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp [bernoulliPowerSeries, Algebra.smul_def]

theorem aeval_trunc_exp (N : ℕ) (D : R) :
    Polynomial.aeval D (PowerSeries.trunc N (PowerSeries.exp ℂ)) =
      ∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D^k := by
  rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp [PowerSeries.exp, Algebra.smul_def]

theorem nilpotent_bernoulli_sum_identity {N : ℕ} (bound : 2 ≤ N)
    (D : R) (nilpotent : D^N = 0) :
    (∑ k ∈ Finset.range N, ((bernoulli k : ℂ) / (k.factorial : ℂ)) • D^k) *
      ((∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D^k) - 1) = D := by
  simpa only [aeval_trunc_bernoulli, aeval_trunc_exp] using
    nilpotent_bernoulli_identity bound D nilpotent

theorem isUnit_nilpotent_aeval {N : ℕ} (D : R) (nilpotent : D^N = 0)
    (p : Polynomial ℂ) (constant : p.coeff 0 = 1) : IsUnit (Polynomial.aeval D p) := by
  have divisibility : Polynomial.X ∣ p-1 := by
    apply Polynomial.X_dvd_iff.mpr
    rw [Polynomial.coeff_sub, constant, Polynomial.coeff_one_zero, sub_self]
  obtain ⟨q, factorization⟩ := divisibility
  have nilpotent_sub : IsNilpotent (Polynomial.aeval D p - 1) := by
    refine ⟨N, ?_⟩
    rw [← map_one (Polynomial.aeval D : Polynomial ℂ →ₐ[ℂ] R), ← map_sub, ← map_pow,
      factorization, mul_pow, map_mul, map_pow, Polynomial.aeval_X,
      nilpotent, zero_mul]
  simpa only [sub_add_cancel] using nilpotent_sub.isUnit_add_one

theorem nilpotent_bernoulli_isUnit {N : ℕ} (positive : 0 < N)
    (D : R) (nilpotent : D^N = 0) :
    IsUnit (∑ k ∈ Finset.range N, ((bernoulli k : ℂ) / (k.factorial : ℂ)) • D^k) := by
  rw [← aeval_trunc_bernoulli]
  apply isUnit_nilpotent_aeval D nilpotent
  simp [PowerSeries.coeff_trunc, positive, bernoulliPowerSeries, bernoulli_zero]

end NilpotentEvaluation

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
