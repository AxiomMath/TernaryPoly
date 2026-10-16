module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Corollaries.Corollary15Assembly
public import TernaryPeriodPolynomials.Polynomial.Corollaries.Corollary15PartB

@[expose] public section


/-! Target: Corollary 1.5 (`cor:common-divisor`) of the paper. -/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Corollary 1.5.** Over every characteristic-zero field, `D = (x+y+z)(x+y)(y+z)(z+x)`
divides every solution of the two defining equations, and every common divisor of all
solutions divides `D`; so `D` is, up to a nonzero scalar, their greatest common divisor. -/
theorem universal_divisor_gcd {F : Type*} [Field F] [CharZero F] :
    (∀ f : MvPolynomial (Fin 3) F, Solution f → universalDivisor F ∣ f) ∧
    ∀ g : MvPolynomial (Fin 3) F, (∀ f, Solution f → g ∣ f) → g ∣ universalDivisor F := by
  exact ⟨fun _ hf => universalDivisor_dvd_of_solution hf,
    fun _ hg => universalDivisor_dvd_of_universal_property hg⟩

end TernaryPeriodPolynomials
