module

public import TernaryPeriodPolynomials.ModularForm.Hecke.Fourier
public import TernaryPeriodPolynomials.ModularForm.HeckeLSeries.CoefficientsUnique
public import TernaryPeriodPolynomials.ModularForm.Period.Hecke

@[expose] public section


noncomputable section
open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace TernaryPoly.BinaryCuspHecke
open BinaryCuspPeriod

/-- Primality supplies the positivity required by the literal upper-half-plane points. -/
theorem prime_pos (p : Nat.Primes) : 0 < p.val :=
  ((Nat.irreducible_iff_nat_prime _).mp p.property).pos

/-- Actual simultaneous pointwise eigenidentities for the standard prime Hecke expressions. -/
def IsPrimeEigenform {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ) : Prop :=
  ∀ p : Nat.Primes, ∀ z : ℍ, primeOperator p.val (prime_pos p) f z = ev p * f z

/-- Scalar multiplication of actual cusp forms scales their actual Fourier coefficients. -/
theorem coefficients_smul {d : ℕ} (f : Forms d) (c : ℂ) (n : ℕ) :
    coefficients (c • f) n = c * coefficients f n := by
  have hp : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      Subgroup.strictWidthInfty_mem_strictPeriods 𝒮ℒ
  change (qExpansion 1 (c • (f : ℍ → ℂ))).coeff n = c * (qExpansion 1 f).coeff n
  rw [ModularForm.qExpansion_smul (by norm_num) hp c f]
  simp

/-- The actual pointwise eigenidentity forces the literal Fourier coefficient identity. -/
theorem eigen_coefficient_relation {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ)
    (hf : IsPrimeEigenform f ev) (p : Nat.Primes) (n : ℕ) :
    coefficients f (p.val*n) + (p.val : ℂ) ^ (d+1) *
      (if p.val ∣ n then coefficients f (n/p.val) else 0) = ev p * coefficients f n := by
  have hp : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      Subgroup.strictWidthInfty_mem_strictPeriods 𝒮ℒ
  have hs (z : ℍ) : HasSum (fun m => transformedCoefficients f p.val m •
      Function.Periodic.qParam 1 z ^ m) ((ev p • f) z) := by
    simpa only [smul_eq_mul, smul_apply, q, hf p z] using
      hasSum_primeOperator f p.val (prime_pos p) z
  have hu := ModularFormClass.qExpansion_coeff_unique (f := ev p • f)
    (by norm_num : (0 : ℝ) < 1) hp hs n
  change transformedCoefficients f p.val n = coefficients (ev p • f) n at hu
  simpa only [transformedCoefficients, coefficients_smul] using hu

/-- For a normalized actual simultaneous eigenform, the prime eigenvalue is a(p). -/
theorem eigenvalue_eq_coefficient {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ)
    (hf : IsPrimeEigenform f ev) (h1 : coefficients f 1 = 1) (p : Nat.Primes) :
    ev p = coefficients f p.val := by
  have he := eigen_coefficient_relation f ev hf p 1
  have hp := (Nat.irreducible_iff_nat_prime _).mp p.property
  simpa [hp.not_dvd_one, h1] using he.symm

/-- Normalized simultaneous eigenidentities imply coprime multiplicativity of actual coefficients. -/
theorem eigen_coefficients_multiplicative {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ)
    (hf : IsPrimeEigenform f ev) (h1 : coefficients f 1 = 1) (m n : ℕ) (hmn : m.Coprime n) :
    coefficients f (m*n) = coefficients f m * coefficients f n := by
  apply BinaryHeckeCoefficients.coprime_multiplicative (coefficients f)
    (fun p => (p.val : ℂ) ^ (d+1)) (coefficients_zero f) h1
  · intro p j
    simpa only [eigenvalue_eq_coefficient f ev hf h1] using
      eigen_coefficient_relation f ev hf p j
  · exact hmn

/-- The exact second-order prime-power recurrence, with weight factor p^(d+1). -/
theorem eigen_coefficients_prime_recurrence {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ)
    (hf : IsPrimeEigenform f ev) (h1 : coefficients f 1 = 1) (p : Nat.Primes) (r : ℕ) :
    coefficients f (p.val^(r+2)) = coefficients f p.val * coefficients f (p.val^(r+1)) -
      (p.val : ℂ) ^ (d+1) * coefficients f (p.val^r) := by
  apply BinaryHeckeCoefficients.prime_power_recurrence (coefficients f)
    (fun p => (p.val : ℂ) ^ (d+1))
  intro q j
  simpa only [eigenvalue_eq_coefficient f ev hf h1] using
    eigen_coefficient_relation f ev hf q j

/-- Actual cusp forms are determined by their width-one Fourier coefficients. -/
theorem eq_zero_of_coefficients_zero {d : ℕ} (f : Forms d) (hf : ∀ n, coefficients f n = 0) :
    f = 0 := by
  apply CuspForm.ext
  intro z
  have he := (hasSum_coefficients f z).tsum_eq
  simpa [hf] using he.symm

/-- A nonzero simultaneous pointwise prime eigenform has nonzero first Fourier coefficient. -/
theorem first_coefficient_ne_zero {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ)
    (hf : IsPrimeEigenform f ev) (hne : f ≠ 0) : coefficients f 1 ≠ 0 := by
  intro h1
  apply hne
  apply eq_zero_of_coefficients_zero
  exact BinaryHeckeCoefficients.all_zero_of_first_zero (coefficients f)
    (fun p => (p.val : ℂ) ^ (d+1)) ev (coefficients_zero f) h1
    (eigen_coefficient_relation f ev hf)

end TernaryPoly.BinaryCuspHecke
