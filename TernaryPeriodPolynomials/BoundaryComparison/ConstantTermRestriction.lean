module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.ConstantTermRestriction.Convergence

@[expose] public section


/-! Target: Proposition C.4 (`ar:prop:convergence`) of the paper, in the adelic
model of the project: plane cusp data are smooth flat induced sections, and the series over
`Γ_P\Γ` is the sum over `P(ℚ)\G(ℚ)` evaluated at the cohomological point `s = -3/2`. -/

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Proposition C.4.** For `n ≥ 4` (so `k = n + 3 > 6`), the plane Eisenstein series of every
flat induced section converges absolutely at the cohomological point, and its sum is invariant
under left translation by `G(ℚ)`, i.e. it defines a global automorphic function. -/
theorem plane_eisenstein_convergent_invariant (n : ℕ) (hn : 4 ≤ n) (D : InducingData n) (F : ℂ → AdelicGL → ℂ)
    (hF : IsFlatSection D F) :
    (∀ g, Summable (eisensteinSummand F cohomologicalPoint g)) ∧
    ∀ (γ : RationalGL3) (g : AdelicGL),
      ∑' q, eisensteinSummand F cohomologicalPoint (rationalGroup γ * g) q =
        ∑' q, eisensteinSummand F cohomologicalPoint g q := by
  exact TernaryPeriodPolynomials.Argument.Classification.plane_eisenstein_convergent_invariant n hn D F hF

end TernaryPeriodPolynomials
