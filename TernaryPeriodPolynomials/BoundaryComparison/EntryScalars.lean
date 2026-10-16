module

public import TernaryPeriodPolynomials.ArithmeticGroup.UnramifiedFactor
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.ClassicalEulerScaling

@[expose] public section


/-!
# The unramified entry: the scalar and the library's local Euler quotient

Appendix C.6 of the paper computes the local
factor at `p ≠ 3` of the line constant term as `c_p = L_p(h, k-2)/L_p(h, k-1)`. The target
`unramified_local_factor` states the shell-sum form of `c_p` and its value
`(1 - a_p p^{1-k} + p^{1-k}) / (1 - a_p p^{2-k} + p^{3-k})`. The library's adelic computation of the
local intertwining integral at the cohomological point (`cuspLocalPadicEulerFactor_cohomological`)
produces `classicalPrimeEulerPolynomial p k a (k-1) / classicalPrimeEulerPolynomial p k a (k-2)`.
This module proves that the two expressions coincide for `k = n + 3`, so the scalar is the
value of the library's local factor.

Written by Claude Opus 5.5.
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Argument.Statements.EntryScalars

private theorem sq_zpow (x : ℂ) (e : ℤ) : (x ^ e) ^ 2 = x ^ (2 * e) := by
  rw [← zpow_natCast, ← zpow_mul]
  ring_nf

private theorem eulerPolynomial_eq (p : ℕ) (hp : 0 < p) (n : ℕ) (a : ℂ) (s : ℤ) :
    classicalPrimeEulerPolynomial p ((n : ℤ) + 3) a (-(s : ℂ)) =
      1 - a * (p : ℂ) ^ s + (p : ℂ) ^ ((n : ℤ) + 2 + 2 * s) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold classicalPrimeEulerPolynomial
  rw [neg_neg, Complex.cpow_intCast, sq_zpow, ← zpow_add₀ hp0]
  congr 2
  ring

/-- **The library's local Euler quotient at `k = n + 3` is the unramified entry.** -/
theorem classicalEulerQuotient_eq_unramified (p : ℕ) (hp : 0 < p) (n : ℕ) (a : ℂ) :
    classicalPrimeEulerPolynomial p ((n : ℤ) + 3) a ((n : ℂ) + 2) /
        classicalPrimeEulerPolynomial p ((n : ℤ) + 3) a ((n : ℂ) + 1) =
      (1 - a * (p : ℂ) ^ (1 - ((n : ℤ) + 3)) + (p : ℂ) ^ (1 - ((n : ℤ) + 3))) /
        (1 - a * (p : ℂ) ^ (2 - ((n : ℤ) + 3)) + (p : ℂ) ^ (3 - ((n : ℤ) + 3))) := by
  have h2 : ((n : ℂ) + 2) = -(((-((n : ℤ) + 2) : ℤ) : ℂ)) := by push_cast; ring
  have h1 : ((n : ℂ) + 1) = -(((-((n : ℤ) + 1) : ℤ) : ℂ)) := by push_cast; ring
  rw [h2, h1, eulerPolynomial_eq p hp, eulerPolynomial_eq p hp]
  have e2 : (n : ℤ) + 2 + 2 * -((n : ℤ) + 2) = 1 - ((n : ℤ) + 3) := by ring
  have e4 : (n : ℤ) + 2 + 2 * -((n : ℤ) + 1) = 3 - ((n : ℤ) + 3) := by ring
  have e1 : -((n : ℤ) + 2) = 1 - ((n : ℤ) + 3) := by ring
  have e3 : -((n : ℤ) + 1) = 2 - ((n : ℤ) + 3) := by ring
  rw [e2, e4, e1, e3]

end TernaryPeriodPolynomials.Argument.Statements.EntryScalars
