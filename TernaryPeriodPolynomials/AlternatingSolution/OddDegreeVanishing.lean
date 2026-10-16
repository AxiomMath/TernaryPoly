module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.GeneralFieldVanishing

@[expose] public section


/-! Target: the characteristic-zero consequence stated in Theorem 5.2 (`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Theorem 5.2, consequence.** An alternating homogeneous solution of `N f = 0` in odd
degree over any field of characteristic zero is zero. -/
theorem alternating_odd_degree_solution_eq_zero {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous n) (hn : Odd n)
    (halt : IsAlternating f) (hN : threeTermNorm f = 0) : f = 0 := by
  exact ModFourMain.vanishing_of_odd_alternating_norm_zero_field hn f hf halt hN

end TernaryPeriodPolynomials
