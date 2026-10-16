module

public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison.Graph
public import TernaryPeriodPolynomials.BoundaryComparison.Assembly.AppendixC6Map
public import TernaryPeriodPolynomials.BoundaryComparison.ClassicalFaces.Certificate
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntry.FiniteEntry

@[expose] public section


/-!
# The argument-flow certificates R3 and the Appendix C.6 assembly along the actual essential route

* `appendix_C6_paper`: the exact statement of `bad_plane_data_injective`, assembled as
  the finite entry (`paper_finite_entry`) → class-level consumer (`classLevel_paper_of_entry`) → R3 certificate
  (`paper_entry_at_classical_faces`, `ClassicalFaces/Certificate.lean`) → detection through the classical faces
  (`cuspRes_line_true_image_ne_zero_certified`, `perDatumDetection_classical`) → Hecke-character separation
  (`cluster_zero_classical`) → `appendix_C6_core_of_map` → `appendix_C6_of_map`, with the graph map `T₀` of R1
  (`paperGraphMap`, uniqueness clause `paperGraphMap_unique`).

Formalized by Claude Sonnet 5.5, with Claude Opus 5.5.  Inputs: `paper_finite_entry`, `paperGraphMap`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1)
open TernaryPeriodPolynomials.Argument.KDaggerComparison (phiLine)
open TernaryPeriodPolynomials.Argument.LineSeed (lineSeedBoundary lineEntryTupleC)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BoundaryComparison

/-- **Appendix C.6, injectivity, along the actual essential route.**  The exact statement of
`TernaryPeriodPolynomials.bad_plane_data_injective`, with the graph map `T₀ = paperGraphMap` (R1) and the finite entry
`paper_finite_entry` (R2, consumed inside `paper_entry_at_classical_faces`). -/
theorem appendix_C6_paper (n : ℕ) (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ)
    (hgood : VanishesOnGood n trivialCharacter .plane ξ)
    (hline : VanishesOnGood n trivialCharacter .line (T ξ)) : ξ = 0 :=
  appendix_C6_of_map n hn (paperGraphMap n hn) (paperGraphMap_unique n hn) T hT ξ hξ hgood hline

end TernaryPeriodPolynomials.Argument.BoundaryComparison
