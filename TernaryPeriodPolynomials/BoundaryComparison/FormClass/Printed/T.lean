module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Intertwiner.Printed

@[expose] public section


/-!
# `r_Q = T r_P` at `K†` for the classical series, with `T` the printed intertwiner

Formalized by Claude Sonnet 5.5.  Combines `formClass_planeLocallyInner` (M3 reduction)
with the `T0_eq_printed` (`T₀ [plane] = [sourceStandard plane]`, the printed integral `eq:intertwiner`).
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) [Fintype (PlaneFaces N)]

/-- **`r_Q = T₀ r_P` at `K†` for the classical summed series**, `T₀ = (line_constant_term_comparison n hn).choose` the canonical uniqueness map. -/
theorem formClass_line_eq_T0 (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (hS : ∀ x b, SeriesRestrictionInSeedSpan N n hn (f x b) x b)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, complexify (gammaN N) n
        (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b)
          (Quotient.out x) b hn))) :
    (globalCoordinates n trivialCharacter c).2 =
      (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose (globalCoordinates n trivialCharacter c).1 := by
  have he : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel_le_level e)
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
    intro e
    rw [hc]
    exact classK_edge_vanishing N h3 hN n _ (formClass_planeLocallyInner N n h3 hN hn f hS) e
  exact lineCoordinate_eq_of_edgeVanishing n _ (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose_spec.2 c he

/-- **`r_Q = T r_P` with `T` the printed intertwiner (corollary).**  If the plane coordinate of the `K†`-corestriction of the classical
series is the class of a plane source cocycle `plane` of a paper datum `D`, then its line coordinate is the class of the printed
integral `sourceStandard plane` (`eq:intertwiner`). -/
theorem formClass_line_eq_printedT (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (hS : ∀ x b, SeriesRestrictionInSeedSpan N n hn (f x b) x b)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, complexify (gammaN N) n
        (TernaryPeriodPolynomials.Argument.Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b)
          (Quotient.out x) b hn)))
    (D : CohomologicalCuspData n) (plane : SourceSpace.sourceCocycles D.inducingData .plane)
    (hplane : (globalCoordinates n trivialCharacter c).1 = SourceSpace.sourceClass D.inducingData .plane plane) :
    (globalCoordinates n trivialCharacter c).2 =
      SourceSpace.sourceClass D.inducingData .line
        (EndpointSourceStandard.sourceStandard D.inducingData hn (planeEisensteinConvergent hn D.inducingData) plane) := by
  rw [formClass_line_eq_T0 N h3 hN n hn f hS c hc, hplane]
  exact PrintedIntertwiner.T0_eq_printed D hn plane

end TernaryPeriodPolynomials.Argument.FormClassK
