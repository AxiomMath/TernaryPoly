module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.PeriodIsomorphism.HilbertSeries

@[expose] public section


/-!
# Corollary 1.4: assembly of the four conjuncts

The statement below is the statement of `TernaryPeriodPolynomials.period_isomorphisms_and_finrank`; the
target file applies it.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials.Argument.Corollary14

theorem corollary_1_4_assembly :
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
  refine ⟨fun n hn hev => ⟨⟨oddBijection n hev, oddBijection_coe n hev⟩,
      ⟨evenBijection n (Nat.pos_iff_ne_zero.mp hn) hev,
        evenBijection_coe n (Nat.pos_iff_ne_zero.mp hn) hev⟩⟩,
    fun F _ _ n => ⟨symmetricSolution_finrank F n, alternatingSolution_finrank F n⟩,
    conjunct3, fun F _ _ => hilbertSeries_mul F⟩

end TernaryPeriodPolynomials.Argument.Corollary14
