module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.Assembly

@[expose] public section


/-! Target: Corollary 1.4 (`cor:dimensions`) of the paper. -/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Corollary 1.4.** For every even `n > 0`, the period maps `h ↦ Φ(r_h^{odd})` and
`h ↦ Φ(r_h^{ev,0})` induce complex linear isomorphisms `S_{n+2} ≅ W_n^{sym}(ℂ)` and
`S_{n+2} ≅ W_n^{alt}(ℂ)`. For every characteristic-zero field `F` and every `n ≥ 0`,
`dim_F W_n^{sym}(F) = dim_F W_n^{alt}(F) = dim_ℂ S_{n+2}`; all these spaces vanish when `n = 0`
or `n` is odd; and `∑_n dim_F W_n(F) tⁿ = 2t¹⁰ / ((1 - t⁴)(1 - t⁶))`. -/
theorem period_isomorphisms_and_finrank :
    (∀ n : ℕ, 0 < n → Even n →
      (∃ e : CuspForm levelOne ((n : ℤ) + 2) ≃ₗ[ℂ] symmetricSolutionSpace ℂ n,
        ∀ h, (e h : MvPolynomial (Fin 3) ℂ) = cyclicLift (oddPeriodPart n h)) ∧
      (∃ e : CuspForm levelOne ((n : ℤ) + 2) ≃ₗ[ℂ] alternatingSolutionSpace ℂ n,
        ∀ h, (e h : MvPolynomial (Fin 3) ℂ) = cyclicLift (normalizedEvenPeriodPart n h))) ∧
    (∀ (F : Type) [Field F] [CharZero F] (n : ℕ),
      Module.finrank F (symmetricSolutionSpace F n) =
          Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2)) ∧
        Module.finrank F (alternatingSolutionSpace F n) =
          Module.finrank ℂ (CuspForm levelOne ((n : ℤ) + 2))) ∧
    (∀ (F : Type) [Field F] [CharZero F] (n : ℕ), (n = 0 ∨ Odd n) →
      symmetricSolutionSpace F n = ⊥ ∧ alternatingSolutionSpace F n = ⊥) ∧
    (∀ (F : Type) [Field F] [CharZero F],
      PowerSeries.mk (fun n => (Module.finrank F (solutionSpace F n) : ℤ)) *
          ((1 - PowerSeries.X ^ 4) * (1 - PowerSeries.X ^ 6)) =
        2 * PowerSeries.X ^ 10) := by
  exact TernaryPeriodPolynomials.Argument.Corollary14.corollary_1_4_assembly

end TernaryPeriodPolynomials
