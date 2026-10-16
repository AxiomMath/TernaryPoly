module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.TrivialSector

@[expose] public section


/-!
# CMP-7 (K† comparison): the reduction to the trivial sector,

The `bad_plane_data_injective` is stated for the sector `trivialCharacter` (coefficients `E_n = E_{n,1}`, data of trivial normal inducing
character).  The paper shows that nothing is lost: a datum with a nonzero bad-plane class whose class extends over `⟨K†, -I₃⟩`
has trivial normal character.  Statements (all `Proofs/KDaggerComparison/TrivialSector.lean`):

* `reflScalar_eq_one_iff_even`: for odd `n`, `-I₃` acts on the `χ`-sector coefficients by `χ_∞(-1)`, so every class of the trivial
  sector extends (`globalCoordinates_trivial_extended`); `rationalCoefficientComponent_eq_of_even`: all even normal characters give
  the same coefficient system `E_n`.
* `spherical_and_odd_of_bad_plane`: a datum with a nonzero bad-plane class is spherical (level one) with `n` odd (even weight `n + 3`).
* `chi_eq_trivial_of_extended_span`, `chi_eq_trivial_of_global_plane_coordinate`: an extended class of the span of the plane
  summands of data of normal character `χ`, or the plane coordinate of a global class with `reflScalar n χ = 1`, with a nonzero
  bad-plane coordinate, forces `χ = trivialCharacter`.
* `automorphicPlaneSpan_eq_planeDatumSpan`: the span is the span of data of normal character `trivialCharacter`.
* `appendix_C6_anySector`, `appendix_C6_anySector_of_global`, `appendix_C6_even_character`: the bad-plane injectivity of
  `bad_plane_data_injective` for data of an arbitrary (resp. even) normal character, derived from the `bad_plane_data_injective`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.KDaggerCMP7

alias automorphicPlaneSpan_eq_planeDatumSpan := TernaryPeriodPolynomials.Argument.KDaggerComparison.automorphicPlaneSpan_eq_planeDatumSpan
alias reflScalar_eq_one_iff_even := TernaryPeriodPolynomials.Argument.KDaggerComparison.reflScalar_eq_one_iff_even
alias globalCoordinates_trivial_extended := TernaryPeriodPolynomials.Argument.KDaggerComparison.globalCoordinates_trivial_extended
alias rationalCoefficientComponent_eq_of_even := TernaryPeriodPolynomials.Argument.KDaggerComparison.rationalCoefficientComponent_eq_of_even
alias spherical_and_odd_of_bad_plane := TernaryPeriodPolynomials.Argument.KDaggerComparison.spherical_and_odd_of_bad_plane
alias chi_eq_trivial_of_extended_span := TernaryPeriodPolynomials.Argument.KDaggerComparison.chi_eq_trivial_of_extended_span
alias chi_eq_trivial_of_global_plane_coordinate := TernaryPeriodPolynomials.Argument.KDaggerComparison.chi_eq_trivial_of_global_plane_coordinate
alias appendix_C6_anySector := TernaryPeriodPolynomials.Argument.KDaggerComparison.appendix_C6_anySector
alias appendix_C6_anySector_of_global := TernaryPeriodPolynomials.Argument.KDaggerComparison.appendix_C6_anySector_of_global
alias appendix_C6_even_character := TernaryPeriodPolynomials.Argument.KDaggerComparison.appendix_C6_even_character

end TernaryPeriodPolynomials.Argument.Statements.KDaggerCMP7
