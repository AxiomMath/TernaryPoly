module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.RecursionEigen

@[expose] public section


/-!
# Hecke recursion: coefficients

Formalized by Claude Sonnet 5.5.

`coeff_prime_pow`: `a_h(p^r) = c_r`; `latticeOp_prime_pow_eq_coeff`: `T_{p^r} h = a_h(p^r) h` for a normalized level-one cusp form with the prime Hecke relations.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion

open Finset Matrix TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator

/-! ### Coefficients -/

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **The coefficients at prime powers are the eigenvalue sequence**: `a_h(p^r) = c_r` for a normalized level-one cusp form with the prime
Hecke relation at `p`. -/
theorem coeff_prime_pow {k : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range k)
    (period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods)
    (prime : Nat.Primes) (lam : ℂ)
    (eigenrelation : ∀ point : UpperHalfPlane,
      lam * form point =
        (prime.val : ℂ) ^ (k - 1) *
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate prime.val prime.property.pos) • point) +
          (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
            form (GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (binaryHeckeTranslate prime.val prime.property.pos index) • point))
    (normalized : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1) :
    ∀ r, (UpperHalfPlane.qExpansion 1 form).coeff (prime.val ^ r) = heckeC k prime.val lam r := by
  have key : ∀ r, (UpperHalfPlane.qExpansion 1 form).coeff (prime.val ^ r) = heckeC k prime.val lam r ∧
      (UpperHalfPlane.qExpansion 1 form).coeff (prime.val ^ (r + 1)) = heckeC k prime.val lam (r + 1) := by
    intro r
    induction r with
    | zero =>
      refine ⟨by simpa [heckeC] using normalized, ?_⟩
      simpa [heckeC] using cuspForm_hecke_prime_coefficient form period prime lam eigenrelation normalized
    | succ r ih =>
      refine ⟨ih.2, ?_⟩
      rw [cuspForm_hecke_prime_power_recurrence form period prime lam eigenrelation r, ih.1, ih.2]
      rfl
  exact fun r => (key r).1

open TernaryPeriodPolynomials.SphericalDetection.Helpers in
/-- **Steps 1-3 of the prime-power Hecke recursion for a normalized level-one eigenform**: for every prime `p` and `r`,
`T_{p^r} h = a_h(p^r) h` (the lattice operator of index `p^r` acts by the `p^r`-th Fourier coefficient). -/
theorem latticeOp_prime_pow_eq_coeff {k : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range k) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations k form eigenvalues)
    (normalized : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1) (prime : Nat.Primes) (r : ℕ) (z : UpperHalfPlane) :
    latticeOp k (prime.val ^ r) form z = (UpperHalfPlane.qExpansion 1 form).coeff (prime.val ^ r) * form z := by
  have period : (1 : ℝ) ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty_mem_strictPeriods
  have hper : PerInv form := perInv_of_period form period
  have hrel := (hasPrimeHeckeRelations_iff_latticeOp k form eigenvalues).1 relations prime
  rw [latticeOp_eigen prime.property k hper (eigenvalues prime) (hrel · ) r z,
    coeff_prime_pow form period prime (eigenvalues prime) (relations prime) normalized r]

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion
