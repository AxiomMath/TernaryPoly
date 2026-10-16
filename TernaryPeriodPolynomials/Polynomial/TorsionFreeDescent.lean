module

public import TernaryPeriodPolynomials.Polynomial.Defs
public import TernaryPeriodPolynomials.Polynomial.Corollaries.UniversalDivisorTorsionFree

@[expose] public section


/-! Target: the torsion-free coefficient rings of Section 7.4 of the paper. -/

open MvPolynomial TernaryPoly.Paper

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Section 7.4, torsion-free rings.** Over a commutative ring with torsion-free additive
group, every solution has two-variable support, odd-degree homogeneous components vanish, the
restriction `q(X,Y) = f(X,Y,0)` satisfies the normalized binary period relations with
`f = Φ(q)`, and `D` divides `f`. -/
theorem torsion_free_descent {R : Type*} [CommRing R] [IsAddTorsionFree R]
    (f : MvPolynomial (Fin 3) R) (hf : Solution f) :
    TernaryPoly.Paper.Pairwise f ∧ (∀ n : ℕ, Odd n → homogeneousComponent n f = 0) ∧
    PeriodRelations (restriction f) ∧ f = cyclicLift (restriction f) ∧
    universalDivisor R ∣ f := by
  exact torsion_free_descent_assembled hf

end TernaryPeriodPolynomials
