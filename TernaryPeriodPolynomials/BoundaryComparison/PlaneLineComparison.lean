module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison.Graph

@[expose] public section


/-! Target: Proposition C.5 (`ar:prop:graph`) of the paper, in the project's
boundary model.

The proof (Claude Sonnet 5.5, Claude Opus 5.5) calls
`TernaryPeriodPolynomials.Argument.BoundaryComparison.paper_graph_route`, which transports the paper-route `Γ(6)` Proposition C.5
(`GammaNStokes.LevelChange.propC5_gammaN_printed_paperRoute`: canonical face pairings and the literal Stokes lemma)
to the `K†` strata along the dictionaries `phiPlane`/`phiLine`, using both its existence and uniqueness clauses. -/

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Proposition C.5.** Let `n ≥ 4`. There is a linear map `T`, the line constant term of the
convergent cusp-form Eisenstein classes, such that every mixed cuspidal plane class `ξ` is the
plane restriction of a global class with boundary coordinates `(ξ, Tξ)`, `Tξ` mixed cuspidal; and
every global degree-two class whose maximal-face restrictions `(ξ_P, ξ_Q)` are mixed cuspidal with
zero flag restrictions satisfies `ξ_Q = T ξ_P`. -/
theorem line_constant_term_comparison (n : ℕ) (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        InnerBoundary n trivialCharacter .line (T ξ) ∧
          ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
            globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
        InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  exact TernaryPeriodPolynomials.Argument.BoundaryComparison.paper_graph_route n hn

end TernaryPeriodPolynomials
