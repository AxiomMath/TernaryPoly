module

public import TernaryPeriodPolynomials.ModularForm.Periods.OuterLValues

@[expose] public section


/-!
# Euler product of a normalized level-one eigenform

For a normalized eigenform `h` of weight `k > 0` (`IsNormalizedEigenform h`: `a_h(1) = 1` and the prime
eigen-relations), the Dirichlet series `L(h,s) = ∑ a_h(m) m^{-s}` equals the Euler product
`∏_p L_p(h,s)` with `L_p(h,s) = (1 - a_h(p) p^{-s} + p^{k-1-2s})⁻¹`, in the half-plane `Re s > k/2 + 1`
where the series converges absolutely.

Route: the coefficients are multiplicative (`cuspForm_hecke_multiplicative`) and satisfy the prime-power
recurrence (`cuspForm_hecke_prime_power_recurrence`); the Euler roots of each local quadratic come from
`cuspForm_eulerRoots`, and the general Euler product for multiplicative coefficients with summable terms is
`quadraticEulerSeries_eq_product`. The local factor identity is `outerLValue_eulerFactor_eq`.

Formalized by Claude Haiku 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument

/-- The local Euler factor `L_p(h,s) = (1 - a_h(p) p^{-s} + p^{k-1-2s})⁻¹` of a level-one form. -/
def localEulerFactor {k : ℤ} (h : CuspForm levelOne k) (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s) +
    ((p : ℕ) : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹

/-- Euler product for a normalized level-one eigenform: `L(h,s) = ∏_p L_p(h,s)` for
`Re s > k/2 + 1`. -/
theorem heckeLSeries_eulerProduct {k : ℤ} (hk : 0 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (s : ℂ) (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeries (fun m => fourierCoeff h m) s = ∏' p : Nat.Primes, localEulerFactor h p s := by
  obtain ⟨initial, eigenvalue, relations⟩ := hh
  have period : (1 : ℝ) ∈ levelOne.strictPeriods := by
    simpa only [Subgroup.strictWidthInfty_SL2Z] using levelOne.strictWidthInfty_mem_strictPeriods
  have initial' : (UpperHalfPlane.qExpansion 1 h).coeff 1 = 1 := by
    have widened : (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff 1 = 1 := initial
    rwa [Subgroup.strictWidthInfty_SL2Z] at widened
  have hmul : ∀ a b : ℕ, a.Coprime b →
      (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (a * b) =
        (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff a *
          (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff b := by
    intro a b hab
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_multiplicative h period eigenvalue relations initial' a b hab
  have hfirst : ∀ p : Nat.Primes,
      (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff p.val = eigenvalue p := by
    intro p
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_coefficient h period p (eigenvalue p) (relations p) initial'
  have hrec : ∀ (p : Nat.Primes) (e : ℕ),
      (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ (e + 2)) =
        eigenvalue p * (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff
            (p.val ^ (e + 1)) -
          (p.val : ℂ) ^ (k - 1) *
            (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff (p.val ^ e) := by
    intro p e
    simpa only [Subgroup.strictWidthInfty_SL2Z] using
      cuspForm_hecke_prime_power_recurrence h period p (eigenvalue p) (relations p) e
  obtain ⟨first_root, second_root, root_sum, root_product, -, -⟩ :=
    cuspForm_eulerRoots h eigenvalue (fun p => (p.val : ℂ) ^ (k - 1)) initial hfirst hrec
  have summable : Summable (fun index => ‖LSeries.term (fun m => fourierCoeff h m) s index‖) :=
    cuspForm_LSeries_norm_summable hk h s hs
  rw [quadraticEulerSeries_eq_product (fun m => fourierCoeff h m) s eigenvalue
    (fun p => (p.val : ℂ) ^ (k - 1)) first_root second_root initial hmul hfirst hrec
    root_sum root_product summable]
  refine tprod_congr fun p => ?_
  have sum_eq : first_root p + second_root p = fourierCoeff h (p : ℕ) := by
    rw [root_sum p]
    exact (hfirst p).symm
  have identity := outerLValue_eulerFactor_eq p s (fourierCoeff h (p : ℕ))
    (first_root p) (second_root p) sum_eq (root_product p)
  unfold localEulerFactor
  rw [identity]

end TernaryPeriodPolynomials.Argument.Identities
