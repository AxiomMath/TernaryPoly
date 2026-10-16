module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.BoundaryComparison.EntryCertificates

@[expose] public section


/-! Target: the injectivity of Appendix C.6 (`ar:sec:finite`) of the paper.

The proof (Claude Sonnet 5.5) calls `TernaryPeriodPolynomials.Argument.BoundaryComparison.appendix_C6_paper`, the assembly along the
actual essential route: the finite entry `paper_finite_entry` (literal lattice/Hecke integral) → class-level consumer
`classLevel_paper_of_entry` → R3 certificate `paper_entry_at_classical_faces` (the classical line-seed boundary
vector) → detection through the classical faces (`cuspRes_line_true_image_ne_zero_certified`) → Hecke-character
separation (`cluster_zero_classical`) → `appendix_C6_core_of_map` → `appendix_C6_of_map`, with the graph map of R1
(`paperGraphMap`, paper-route Stokes/`Γ(6)` proof of Proposition C.5, uniqueness clause `paperGraphMap_unique`).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Appendix C.6, injectivity.** Let `n ≥ 4` and let `T` be the line constant term of
Proposition C.5, i.e. any linear map such that every mixed cuspidal plane class `ξ` is the plane
restriction of a global class with boundary coordinates `(ξ, Tξ)`. A mixed cuspidal plane class
supported on the bad plane (zero at every good plane) whose image `Tξ` vanishes at every good line
is zero: bad-plane data map injectively to the good lines. -/
theorem bad_plane_data_injective (n : ℕ) (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line (T ξ)) : ξ = 0 :=
  TernaryPeriodPolynomials.Argument.BoundaryComparison.appendix_C6_paper n hn T hT ξ hξ hgood hline

end TernaryPeriodPolynomials
