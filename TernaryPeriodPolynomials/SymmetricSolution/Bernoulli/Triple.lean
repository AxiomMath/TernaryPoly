module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BernoulliAlgebra
public import Mathlib.RingTheory.PowerSeries.Exp

@[expose] public section


/-!
# The operator identity `B(3t) (1 + eᵗ + e²ᵗ) = 3 B(t)` on nilpotent operators

Formalized by Claude Sonnet 5.5.  First of the three cancellations ("`B(3t)(1+e^t+e^{2t}) = 3B(t)`").
-/

open PowerSeries

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

/-- **`B(3t)(1 + eᵗ + e²ᵗ) = 3 B(t)` in `ℂ⟦t⟧`.** -/
theorem rescale_bernoulli_mul_exp :
    rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (1 + exp ℂ + exp ℂ * exp ℂ) = (3 : ℂ) • bernoulliPowerSeries ℂ := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℂ
  have h1 := congrArg (rescale (3 : ℂ)) hB
  rw [map_mul, map_sub, map_one, rescale_X] at h1
  have hexp : rescale (3 : ℂ) (exp ℂ) = exp ℂ ^ 3 := by
    have := (exp_pow_eq_rescale_exp (A := ℂ) 3).symm
    simpa using this
  rw [hexp] at h1
  have hne : exp ℂ - 1 ≠ 0 := by
    intro h
    have := congrArg (coeff 1) h
    simp [coeff_exp] at this
  apply mul_right_cancel₀ hne
  have e3 : exp ℂ ^ 3 - 1 = (exp ℂ - 1) * (1 + exp ℂ + exp ℂ * exp ℂ) := by ring
  rw [e3] at h1
  calc rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * (1 + exp ℂ + exp ℂ * exp ℂ) * (exp ℂ - 1)
      = rescale (3 : ℂ) (bernoulliPowerSeries ℂ) * ((exp ℂ - 1) * (1 + exp ℂ + exp ℂ * exp ℂ)) := by ring
    _ = C 3 * X := h1
    _ = (3 : ℂ) • bernoulliPowerSeries ℂ * (exp ℂ - 1) := by
      rw [smul_mul_assoc, hB, smul_eq_C_mul]


section Nilpotent

variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem trunc_smul' (N : ℕ) (a : ℂ) (f : PowerSeries ℂ) : PowerSeries.trunc N (a • f) = a • PowerSeries.trunc N f := by
  ext k
  simp only [PowerSeries.coeff_trunc, Polynomial.coeff_smul, map_smul]

/-- **`B(3D)(1 + e^D + e^{2D}) = 3 B(D)` for a nilpotent operator `D`** (truncated exponential and Bernoulli sums). -/
theorem bernoulli_triple (D : R) {N : ℕ} (hN : 0 < N) (nil : D ^ N = 0) :
    (∑ k ∈ Finset.range N, ((bernoulli k : ℂ) / (k.factorial : ℂ)) • ((3 : ℂ) • D) ^ k) *
        (1 + (∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D ^ k) +
          (∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D ^ k) * (∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D ^ k)) =
      (3 : ℂ) • ∑ k ∈ Finset.range N, ((bernoulli k : ℂ) / (k.factorial : ℂ)) • D ^ k := by
  have first : Polynomial.aeval D (PowerSeries.trunc N (rescale (3 : ℂ) (bernoulliPowerSeries ℂ))) =
      ∑ k ∈ Finset.range N, ((bernoulli k : ℂ) / (k.factorial : ℂ)) • ((3 : ℂ) • D) ^ k := by
    rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    have hc : coeff k (rescale (3 : ℂ) (bernoulliPowerSeries ℂ)) = 3 ^ k * ((bernoulli k : ℂ) / (k.factorial : ℂ)) := by
      simp [coeff_rescale, bernoulliPowerSeries]
    rw [hc, ← Algebra.smul_def, smul_pow, smul_smul, mul_comm]
  have hone : Polynomial.aeval D (PowerSeries.trunc N (1 : PowerSeries ℂ)) = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    simp [PowerSeries.trunc_one]
  have second : Polynomial.aeval D (PowerSeries.trunc N (1 + exp ℂ + exp ℂ * exp ℂ)) =
      1 + (∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D ^ k) +
        (∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D ^ k) * (∑ k ∈ Finset.range N, (k.factorial : ℂ)⁻¹ • D ^ k) := by
    rw [map_add (PowerSeries.trunc N), map_add (PowerSeries.trunc N), map_add, map_add, nilpotent_aeval_trunc_mul D nil, hone,
      aeval_trunc_exp]
  rw [← first, ← second, ← nilpotent_aeval_trunc_mul D nil, rescale_bernoulli_mul_exp, trunc_smul', map_smul,
    aeval_trunc_bernoulli]

end Nilpotent

end TernaryPeriodPolynomials.Argument.Identities
