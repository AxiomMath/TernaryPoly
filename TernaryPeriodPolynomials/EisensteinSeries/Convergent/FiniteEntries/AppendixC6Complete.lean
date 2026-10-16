module

public import TernaryPeriodPolynomials.BoundaryComparison.BadPlaneInjectivity.TEliminate
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.AppendixC6Core

@[expose] public section


/-!
# Full assembly of `bad_plane_data_injective`, parity-independent

`appendix_C6_core_ms` (`AppendixC6Core.lean`) proves the `T₀`-fixed core fact for *all* `n ≥ 4`, with
no `Even`/`Odd` case split (unlike `EvenAssembly.lean`'s `appendix_C6_even_complete`, which only covers even `n`). Combining it with
`appendix_C6_of_core` (`TEliminate.lean`, `T`-elimination against `line_constant_term_comparison`'s canonical `T₀`)
therefore gives the *whole* `bad_plane_data_injective` statement in one shot, no case split needed.

This is exactly `Targets/AppendixC6.lean`'s own statement, verbatim.

Variant by Claude Sonnet 5.5 of `ConsumersStd/AppendixC6Complete.lean` through
`FiniteEntries.appendix_C6_core_ms`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous


namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd

open TernaryPeriodPolynomials.Argument.BadPlaneInjectivity

/-- **`bad_plane_data_injective`, fully assembled.** Matches `Targets/AppendixC6.lean`'s statement verbatim. -/
theorem appendix_C6_complete_ms (n : ℕ) (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line (T ξ)) : ξ = 0 :=
  appendix_C6_of_core n (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose
    (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose_spec.2
    (fun ξ' hξ' hgood' hline' => appendix_C6_core_ms n hn ξ' hξ' hgood' hline')
    T hT ξ hξ hgood hline

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
