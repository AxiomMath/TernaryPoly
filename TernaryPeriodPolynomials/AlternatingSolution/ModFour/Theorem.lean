module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Theorem52Proof

@[expose] public section


/-! Target: Theorem 5.2 (`mf:thm:main`), integral form, of the paper. -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Theorem 5.2.** Let `f ∈ ℤ[x,y,z]` be alternating, with every monomial of odd total
degree. If `N f ∈ 4ℤ[x,y,z]`, then `f ∈ 2ℤ[x,y,z]`. -/
theorem even_coefficients_of_four_dvd_norm (f : MvPolynomial (Fin 3) ℤ) (halt : IsAlternating f)
    (hodd : HasOddMonomials f) (hN : ∃ g : MvPolynomial (Fin 3) ℤ, threeTermNorm f = C 4 * g) :
    ∃ g : MvPolynomial (Fin 3) ℤ, f = C 2 * g := by
  exact theorem_5_2_proof f halt hodd hN

end TernaryPeriodPolynomials
