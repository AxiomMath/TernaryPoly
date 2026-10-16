module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PlaneSpan
public import TernaryPeriodPolynomials.EisensteinSeries.Class.BridgeK

@[expose] public section


/-!
# L8: the `K†`-level results for the classical series are unconditional

Formalized by Claude Sonnet 5.5.
`seriesRestrictionInSeedSpan` (`EisensteinClass/BridgeK`) discharges the cusp-by-cusp input of `formClass_planeLocallyInner`, so:
* `formClass_planeLocallyInner_uncond`: the summed classical series is locally inner at every plane (`r_B = 0`);
* `formClass_line_eq_T0_uncond`: `r_Q = T₀ r_P` at `K†`;
* `formClass_line_eq_printedT_uncond`, `formClass_line_eq_printedT_sum_uncond`: for every presentation of the plane coordinate as a finite sum of plane source classes (one always exists), the line coordinate is the sum of the printed integrals `sourceStandard` (`eq:intertwiner`).
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) [Fintype (PlaneFaces N)]

/-- **M3 (unconditional): the summed classical series of the `K†`-level group is locally inner at every plane** (`r_B = 0` over every plane), for every tuple
of cusp forms, with S6's `seriesRestrictionInSeedSpan` discharging the cusp-by-cusp input. -/
theorem formClass_planeLocallyInner_uncond (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    PlaneLocallyInner N h3 hN n (∑ x, ∑ b, EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (Quotient.out x) b hn)) :=
  formClass_planeLocallyInner N n h3 hN hn f fun x b =>
    EisensteinClass.seriesRestrictionInSeedSpan N n (f x b) hn hN x b

/-- **`r_Q = T₀ r_P` at `K†` for the classical series, unconditional** (`T₀ = (line_constant_term_comparison n hn).choose`). -/
theorem formClass_line_eq_T0_uncond (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (Quotient.out x) b hn))) :
    (globalCoordinates n trivialCharacter c).2 =
      (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose (globalCoordinates n trivialCharacter c).1 :=
  formClass_line_eq_T0 N h3 hN n hn f
    (fun x b => EisensteinClass.seriesRestrictionInSeedSpan N n (f x b) hn hN x b) c hc

/-- **`r_Q = T r_P` with the printed intertwiner for the classical series, unconditional**: whenever the plane coordinate of the `K†`-class of the series is presented as a
finite sum of plane source classes of paper data (such a presentation always exists: `formClass_line_eq_printedT_sum_uncond`), the line coordinate is the sum of the
printed integrals `sourceStandard` (`eq:intertwiner`). -/
theorem formClass_line_eq_printedT_uncond (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (Quotient.out x) b hn)))
    {ι : Type} [Fintype ι] (D : ι → CohomologicalCuspData n)
    (p : (i : ι) → SourceSpace.sourceCocycles (D i).inducingData .plane)
    (hp : (globalCoordinates n trivialCharacter c).1 =
      ∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i)) :
    (globalCoordinates n trivialCharacter c).2 =
      ∑ i, SourceSpace.sourceClass (D i).inducingData .line
        (EndpointSourceStandard.sourceStandard (D i).inducingData hn
          (planeEisensteinConvergent hn (D i).inducingData) (p i)) := by
  rw [formClass_line_eq_T0_uncond N h3 hN n hn f c hc, hp]
  exact T0_sum_printed n hn D p

/-- **Presentation and printed formula, unconditional.** -/
theorem formClass_line_eq_printedT_sum_uncond (hn : 4 ≤ n)
    (f : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (Quotient.out x) b hn))) :
    ∃ (ι : Type) (_ : Fintype ι) (D : ι → CohomologicalCuspData n)
      (p : (i : ι) → SourceSpace.sourceCocycles (D i).inducingData .plane),
      (globalCoordinates n trivialCharacter c).1 =
          ∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i) ∧
        (globalCoordinates n trivialCharacter c).2 =
          ∑ i, SourceSpace.sourceClass (D i).inducingData .line
            (EndpointSourceStandard.sourceStandard (D i).inducingData hn
              (planeEisensteinConvergent hn (D i).inducingData) (p i)) :=
  formClass_line_eq_printedT_sum n N h3 hN hn f
    (fun x b => EisensteinClass.seriesRestrictionInSeedSpan N n (f x b) hn hN x b) c hc

end TernaryPeriodPolynomials.Argument.FormClassK
