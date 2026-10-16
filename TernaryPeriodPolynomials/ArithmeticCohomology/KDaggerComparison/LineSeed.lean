module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.LineSeedEdge
public import TernaryPeriodPolynomials.BoundaryComparison.EntryDictionary.Dictionary

@[expose] public section


/-!
# CMP-8 (entry, line half): the good-line section of the entry against the classical line seed (level one)

Formalized by Claude Sonnet 5.5.

`paperGoodLine_edge`: the paper's good-line section (the line seed `σ_h = h(τ)(τZ-Y)^n(τ dv₁+dv₂)∧dτ`, whose integral cochain with the datum of
the same sign as the plane seed is `cΣ^{paper}`) is `λ_li = -1` times the library's `a_li` (`EntryDictionary.entry_dictionary`, reused), so its
good-line coordinate has the Hochschild-Serre edge `+3(n+1) · [Sw ∘ ψ_f ∘ pivot]` (`LineSeedEdge.goodLine_edge` for `a_li`, edge `-3(n+1)`): the explicit
scalar relating the good-line section to the classical (Eichler-Shimura) period class of the level-one form of the Eichler input.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.EntryDictionary
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

/-- **The edge of the paper's good-line section** (the line seed `σ_h` with the datum of the same sign as the plane seed `ω_h`): the class `goodLineWeight · cΣ^{paper}` is `λ_li = -1` times the library's `a_li` (`entry_dictionary`), so its transported
good-line coordinate is a mixed class with edge `+3(n+1) · [pivot-swap of the classical period cocycle of the form of `I`]`. -/
theorem paperGoodLine_edge {n : ℕ} (hn : Odd n) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand M.inducingData .plane →ₗ[ℂ] boundarySummand M.inducingData .line)
    (hT : RealizesStandardConv M.inducingData T)
    (γ : rationalLevel) (hγ : γ.val • cuspFlag .line true = (QuotientGroup.mk rationalGoodLine : Flags .line)) :
    ∃ hLP : IsSourceCocycle M.inducingData .line
        (fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g),
      ∃ h : (stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
          (QuotientGroup.mk rationalGoodLine) hγ
          (cuspRes n trivialCharacter .line true
            (SourceQuotient.sourceToSummand M.inducingData .line
              ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val) : H2 Λ₁ (ρn n)) ∈ KL n,
        edgeK n hn.pos ⟨_, h⟩ = ((3 : ℂ) * ((n + 1 : ℕ) : ℂ)) •
          groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (dlCocycleOf n (eichlerClassicalCocycle I hn)) := by
  have hdict := entry_dictionary n M.inducingData S I hw hv T hT
  obtain ⟨_, _, hLP, hLL, _, hline, -⟩ := hdict
  have hobtain1 := goodLine_edge hn M S I γ hγ
  obtain ⟨h, hedge⟩ := hobtain1
  refine ⟨hLP, ?_⟩
  have hx : (SourceQuotient.sourceToSummand M.inducingData .line
      ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val =
      lamLi • (goodLineClass S I).val := hline
  have hy : stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
      (QuotientGroup.mk rationalGoodLine) hγ
      (cuspRes n trivialCharacter .line true
        (SourceQuotient.sourceToSummand M.inducingData .line
          ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val) =
      -(stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
        (QuotientGroup.mk rationalGoodLine) hγ
        (cuspRes n trivialCharacter .line true (goodLineClass S I).val)) := by
    have e1 : lamLi • (goodLineClass S I).val = -(goodLineClass S I).val := by
      rw [lamLi, neg_one_smul]
    refine (congrArg (fun z => stabilizerTransportH2 rationalLevel
      (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
      (QuotientGroup.mk rationalGoodLine) hγ (cuspRes n trivialCharacter .line true z))
      (hx.trans e1)).trans ?_
    rw [map_neg, map_neg]
  refine ⟨(congrArg (· ∈ KL n) hy).mpr (neg_mem h), ?_⟩
  have hsub : (⟨_, (congrArg (· ∈ KL n) hy).mpr (neg_mem h)⟩ : KL n) = -⟨_, h⟩ := Subtype.ext hy
  rw [hsub, map_neg, hedge, ← neg_smul]
  congr 1
  ring

end TernaryPeriodPolynomials.Argument.KDaggerComparison
