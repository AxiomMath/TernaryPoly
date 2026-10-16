module

public import TernaryPeriodPolynomials.ModularForm.Hecke.Eigen

@[expose] public section


noncomputable section
open MvPolynomial
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspHecke
open BinaryCuspPeriod

/-- The L-series of an actual normalized simultaneous pointwise prime eigenform is nonzero
at the outer critical point, using the derived Fourier coefficient equations. -/
theorem normalized_eigen_LSeries_ne_zero {d : ℕ} (hd : 4 < d) (f : Forms d)
    (ev : Nat.Primes → ℂ) (hf : IsPrimeEigenform f ev) (h1 : coefficients f 1 = 1) :
    LSeries (coefficients f) (d : ℂ) ≠ 0 :=
  actual_LSeries_ne_zero_of_coefficient_equations hd f (fun p => (p.val : ℂ) ^ (d+1)) h1
    (eigen_coefficients_multiplicative f ev hf h1) (eigen_coefficients_prime_recurrence f ev hf h1)

/-- The literal extreme odd-period coefficient detects every actual normalized simultaneous
pointwise eigenform. No coefficient recurrence is assumed here: it is derived from the values. -/
theorem normalized_eigen_extreme_ne_zero {d : ℕ} (hd : 4 < d) (f : Forms d)
    (ev : Nat.Primes → ℂ) (hf : IsPrimeEigenform f ev) (h1 : coefficients f 1 = 1) :
    (oddPeriod f).coeff (exponent d 1) ≠ 0 :=
  actual_extreme_ne_zero_of_coefficient_equations hd f (fun p => (p.val : ℂ) ^ (d+1)) h1
    (eigen_coefficients_multiplicative f ev hf h1) (eigen_coefficients_prime_recurrence f ev hf h1)

/-- The actual standard Hecke expression is compatible with scalar multiplication. -/
theorem primeOperator_smul {d : ℕ} (p : ℕ) (hp : 0 < p) (f : Forms d) (c : ℂ) (z : ℍ) :
    primeOperator p hp (c • f) z = c * primeOperator p hp f z := by
  simp only [primeOperator, smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- Scalar multiplication preserves the literal simultaneous pointwise eigenidentities. -/
theorem IsPrimeEigenform.smul {d : ℕ} {f : Forms d} {ev : Nat.Primes → ℂ}
    (hf : IsPrimeEigenform f ev) (c : ℂ) : IsPrimeEigenform (c • f) ev := by
  intro p z
  rw [primeOperator_smul, hf p z]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Normalization is justified for each nonzero actual simultaneous eigenform. -/
theorem normalized_first_coefficient {d : ℕ} (f : Forms d) (ev : Nat.Primes → ℂ)
    (hf : IsPrimeEigenform f ev) (hne : f ≠ 0) :
    coefficients ((coefficients f 1)⁻¹ • f) 1 = 1 := by
  rw [coefficients_smul, inv_mul_cancel₀ (first_coefficient_ne_zero f ev hf hne)]

/-- An actual nonzero eigenform has a normalized representative with nonzero extreme coefficient. -/
theorem actual_normalization_and_extreme {d : ℕ} (hd : 4 < d) (f : Forms d)
    (ev : Nat.Primes → ℂ) (hf : IsPrimeEigenform f ev) (hne : f ≠ 0) :
    let g : Forms d := (coefficients f 1)⁻¹ • f
    IsPrimeEigenform g ev ∧ coefficients g 1 = 1 ∧
      (oddPeriod g).coeff (exponent d 1) ≠ 0 := by
  dsimp only
  have hg := hf.smul (coefficients f 1)⁻¹
  have h1 := normalized_first_coefficient f ev hf hne
  exact ⟨hg, h1, normalized_eigen_extreme_ne_zero hd _ ev hg h1⟩

end TernaryPoly.BinaryCuspHecke
