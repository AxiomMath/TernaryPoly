module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Transport
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.LineSeedEdge
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.GoodWeights

@[expose] public section


/-!
# The good-line sections vanish at the non-good line cusps (Passage, part D2)

A class `sourceClass (goodLineWeight · c)` has zero coordinate at every line flag that is not good: the weight `goodLineWeight` represents the good flags (`goodLineWeight_rational`), so the evaluated
cocycle vanishes at the flag.  Hence `phiLineAt h` of the entry section `a_li = goodLineClass S I` (and of the paper's section) is `0` at every face whose line flag `lineFlagAt h` is not good.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.KDaggerComparison
open TernaryPeriodPolynomials.Argument.SeedC3S4c (resPrincipal)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

/-- **The fixed point class of a good-line weighted source vanishes at a non-good line flag.** -/
theorem fixedPointH2_weightedLine_bad {n : ℕ} (D : InducingData n) (c : (Fin 3 → RealGL3) → AdelicGL → GeneralEisenstein.HomogeneousPoly n)
    (hc : IsSourceCocycle D .line (fun y g => goodLineWeight g • c y g)) (r : RationalGL3)
    (hbad : ¬ GoodFlag .line (QuotientGroup.mk r : Flags .line)) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) (QuotientGroup.mk r : Flags .line)
      (SourceSpace.sourceClass D .line ⟨fun y g => goodLineWeight g • c y g, hc⟩) = 0 := by
  have e : SourceSpace.sourceClass D .line ⟨fun y g => goodLineWeight g • c y g, hc⟩ =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)
        (SourceSpace.evaluatedSource D .line ⟨fun y g => goodLineWeight g • c y g, hc⟩) := rfl
  rw [e]
  refine (fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n D.chi) (QuotientGroup.mk r : Flags .line) _).trans ?_
  have hz : fixedPointCycle rationalLevel (rationalCoefficientComponent n D.chi) (QuotientGroup.mk r : Flags .line)
      (SourceSpace.evaluatedSource D .line ⟨fun y g => goodLineWeight g • c y g, hc⟩) = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    have hq := SourceSpace.evaluatedSource_realizes D .line ⟨fun y g => goodLineWeight g • c y g, hc⟩
      vertices r
    refine hq.trans ?_
    change goodLineWeight (rationalGroup r⁻¹) • _ = 0
    rw [goodLineWeight_rational]
    unfold goodWeight
    rw [ite_eq_right hbad, zero_smul]
  rw [hz]
  exact map_zero _


theorem phiLineAt_weighted_bad (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) {n : ℕ} (M : CohomologicalCuspData n)
    (c : (Fin 3 → RealGL3) → AdelicGL → GeneralEisenstein.HomogeneousPoly n)
    (hc : IsSourceCocycle M.inducingData .line (fun y g => goodLineWeight g • c y g)) (h : SL(3, ℤ))
    (hbad : ¬ GoodFlag .line (lineFlagAt h)) :
    phiLineAt N h3 hN n h (SourceSpace.sourceClass M.inducingData .line ⟨fun y g => goodLineWeight g • c y g, hc⟩) = 0 := by
  have h0 := fixedPointH2_weightedLine_bad M.inducingData c hc (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) hbad
  change lineH2Equiv N h3 h n trivialCharacter hN
    (resPrincipal N (lineFlagAt h) (rationalCoefficientComponent n trivialCharacter)
      (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (lineFlagAt h)
        (SourceSpace.sourceClass M.inducingData .line ⟨fun y g => goodLineWeight g • c y g, hc⟩))) = 0
  have h0' : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (lineFlagAt h)
      (SourceSpace.sourceClass M.inducingData .line ⟨fun y g => goodLineWeight g • c y g, hc⟩) = 0 := h0
  rw [h0', LinearMap.map_zero, LinearEquiv.map_zero]

theorem phiLineAt_goodLineClass_bad (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) {n : ℕ} (M : CohomologicalCuspData n)
    (S : SphericalEntryData M.inducingData) (I : EichlerInput M.cusp n) (h : SL(3, ℤ))
    (hbad : ¬ GoodFlag .line (lineFlagAt h)) :
    phiLineAt N h3 hN n h (goodLineClass S I).val = 0 :=
  phiLineAt_weighted_bad N h3 hN M _ _ h hbad

end TernaryPeriodPolynomials.Argument.LineSeed
