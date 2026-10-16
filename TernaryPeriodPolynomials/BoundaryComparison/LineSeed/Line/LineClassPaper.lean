module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ClassFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.LineSeed

@[expose] public section


/-!
# The paper's good-line section restricted to `Λ₁⁺` (LS15d)

`paperLineSeedIdentity`: the paper's good-line section (the line seed `σ_h` with the datum of the same sign as the plane seed, integral cochain `cΣ^{paper}`) is
`λ_li = -1` times the library's `a_li` (`EntryDictionary.entry_dictionary`), so the restriction to `Λ₁⁺` of its good-line coordinate is `-(n+1)/2` times the complexified de Rham class of the
reflection-invariant line seed `σ_f + (-1)ⁿ \overline{σ_{f^*}}` (`lineSeedIdentity`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
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
open TernaryPeriodPolynomials.Argument.KDaggerComparison (goodLineClass)
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.LineSeed (reflSeedInv)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

local notation "Lvl1" => TernaryPeriodPolynomials.Argument.SeedC3S4c.Lvl1

/-- **The paper's good-line section, restricted to `Λ₁⁺`, is `-(n+1)/2` times the line seed class.** -/
theorem paperLineSeedIdentity {n : ℕ} (hn : Odd n) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand M.inducingData .plane →ₗ[ℂ] boundarySummand M.inducingData .line)
    (hT : RealizesStandardConv M.inducingData T) :
    ∃ f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ),
      (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I ∧
      ∃ hLP : IsSourceCocycle M.inducingData .line
          (fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g),
        linePlusRes n (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
            (QuotientGroup.mk rationalGoodLine : Flags .line)
            (SourceQuotient.sourceToSummand M.inducingData .line
              ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val) =
          (-(((n : ℂ) + 1) / 2)) • lineComplexify n
            (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
              (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f 1)) := by
  obtain ⟨f, hfun, hid⟩ := lineSeedIdentity hn M S I
  obtain ⟨_, _, hLP, hLL, _, hline, -⟩ := entry_dictionary n M.inducingData S I hw hv T hT
  refine ⟨f, hfun, hLP, ?_⟩
  have hx : (SourceQuotient.sourceToSummand M.inducingData .line
      ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val =
      lamLi • (goodLineClass S I).val := hline
  rw [hx]
  erw [map_smul (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
    (QuotientGroup.mk rationalGoodLine : Flags .line)) lamLi]
  erw [map_smul (linePlusRes n) lamLi]
  rw [hid, smul_smul]
  congr 1
  rw [lamLi]
  ring

end TernaryPeriodPolynomials.Argument.LineSeed
