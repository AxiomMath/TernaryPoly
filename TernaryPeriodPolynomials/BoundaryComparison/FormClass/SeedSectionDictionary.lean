module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.ClassicalSeries
public import TernaryPeriodPolynomials.BoundaryComparison.LemmaC3Final

@[expose] public section


/-!
# The classical-seed / adelic-section dictionary at the level of spans (R5 G5)

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3, the constant terms, the real entry.
* `transferred_seeds_are_source_sum`: every pair of transferred `Γ(N)`-seed classes at a good and a bad reference plane is the pair of Shapiro components of a finite sum of plane source classes.
* `formClass_plane_inner`, **`formClass_plane_coordinate_named`**: the `K†` plane coordinate of the classical series has reference-plane components `planeTransfer yg`, `planeTransfer yb` with `yg, yb`
  in the seed spans, is a finite sum of source classes, and its line coordinate is the sum of the printed integrals.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

/-- **The seed/section dictionary at the level of spans (literal).**  Every pair of transferred `Γ(N)`-seed classes `(yg, yb)` at a good and a bad reference plane
(`yg ∈ faceSeedSpan N hg n`, `yb ∈ faceSeedSpan N hb n`: combinations of the classes of the holomorphic and antiholomorphic seeds of cusp forms of level `Γ(N)`) is the pair of
Shapiro components of a FINITE SUM OF PLANE SOURCE CLASSES of paper data: `Lemma C.3` (last sentence: `lemma_C3_final_sentence`) puts `(yg, yb)` into the inner classes, and
the inner classes lie in `automorphicPlaneSpan` (`innerBoundary_plane_mem_span`, from `good/bad_plane_cuspidal_span`).  The family `(D i, p i)` is existential. -/
theorem transferred_seeds_are_source_sum (hn : 0 < n) (hg hb : SL(3, ℤ))
    (hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt hg)) (hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt hb))
    (yg : groupCohomology.H2 (SeedC3S4c.faceRep N hg n)) (hyg : yg ∈ SeedC3S4c.faceSeedSpan N hg n)
    (yb : groupCohomology.H2 (SeedC3S4c.faceRep N hb n)) (hyb : yb ∈ SeedC3S4c.faceSeedSpan N hb n) :
    ∃ (ι : Type) (_ : Fintype ι) (D : ι → CohomologicalCuspData n)
      (p : (i : ι) → SourceSpace.sourceCocycles (D i).inducingData .plane),
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hg)
          (∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i)) =
        SeedC3S4c.planeTransfer N h3 hN hg n trivialCharacter yg ∧
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hb)
          (∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i)) =
        SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb := by
  obtain ⟨c, hc1, hc2⟩ := (Statements.LemmaC3Final.lemma_C3_final_sentence N h3 hN hg hb hgood hbad n).2 yg hyg yb hyb
  obtain ⟨ι, hι, D, p, hp⟩ := mem_span_exists_sourceClass_sum n c.1
    (innerBoundary_plane_mem_span n hn c.1 c.2)
  refine ⟨ι, hι, D, p, ?_, ?_⟩
  · exact (congrArg (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hg)) hp.symm).trans hc1
  · exact (congrArg (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hb)) hp.symm).trans hc2

open TernaryPeriodPolynomials.Argument.LevelTransfer TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.ConvergenceC4 in
/-- **The plane coordinate of the classical series is inner** (mixed cuspidal) at `K†`. -/
theorem formClass_plane_inner [Fintype (SeedC3S4c.PlaneFaces N)] (hn : 4 ≤ n)
    (f : SeedC3S4c.PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (Quotient.out x) b hn))) :
    InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 := by
  have he : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel_le_level e)
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
    intro e
    rw [hc]
    exact classK_edge_vanishing N h3 hN n _ (formClass_planeLocallyInner_uncond N h3 hN n hn f) e
  exact innerBoundary_of_edgeVanishing n trivialCharacter .plane c he

open TernaryPeriodPolynomials.Argument.LevelTransfer TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.ConvergenceC4 in
/-- **The classical plane coordinate, named.**  For the classical series (any tuple of cusp forms of level `Γ(N)`), its `K†` plane coordinate `ξ` has, at the good and bad reference
planes, Shapiro components that are the transfers of classes `yg`, `yb` in the seed spans of `Γ(N)` (the classical seed data: combinations of holomorphic and antiholomorphic
seeds), AND is a finite sum of plane source classes; its line coordinate is the sum of the printed integrals.  Literal: the equalities.  Existential: the classes `yg, yb` (the
exact values would follow from S6's cell values and `planeCoordinate_formula`) and the source family (needs the adelic realization of `S_{n+3}(Γ(N))`). -/
theorem formClass_plane_coordinate_named [Fintype (SeedC3S4c.PlaneFaces N)] (hn : 4 ≤ n)
    (f : SeedC3S4c.PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (hc : classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c =
      classK N h3 hN n (∑ x, ∑ b, EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (f x b) (Quotient.out x) b hn)))
    (hg hb : SL(3, ℤ)) (hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt hg))
    (hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt hb)) :
    (∃ yg ∈ SeedC3S4c.faceSeedSpan N hg n, ∃ yb ∈ SeedC3S4c.faceSeedSpan N hb n,
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hg)
          (globalCoordinates n trivialCharacter c).1 = SeedC3S4c.planeTransfer N h3 hN hg n trivialCharacter yg ∧
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hb)
          (globalCoordinates n trivialCharacter c).1 = SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb) ∧
    ∃ (ι : Type) (_ : Fintype ι) (D : ι → CohomologicalCuspData n)
      (p : (i : ι) → SourceSpace.sourceCocycles (D i).inducingData .plane),
      (globalCoordinates n trivialCharacter c).1 = ∑ i, SourceSpace.sourceClass (D i).inducingData .plane (p i) ∧
      (globalCoordinates n trivialCharacter c).2 =
        ∑ i, SourceSpace.sourceClass (D i).inducingData .line
          (EndpointSourceStandard.sourceStandard (D i).inducingData hn
            (planeEisensteinConvergent hn (D i).inducingData) (p i)) := by
  have hin := formClass_plane_inner N h3 hN n hn f c hc
  refine ⟨?_, formClass_line_eq_printedT_sum_uncond N h3 hN n hn f c hc⟩
  obtain ⟨yg, hyg, yb, hyb, h1, h2⟩ := (Statements.LemmaC3Final.lemma_C3_final_sentence N h3 hN hg hb hgood hbad n).1
    ⟨(globalCoordinates n trivialCharacter c).1, hin⟩
  exact ⟨yg, hyg, yb, hyb, h1, h2⟩

end TernaryPeriodPolynomials.Argument.FormClassK
