module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Frame2
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Clean4
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Final2
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Vanish

@[expose] public section


/-!
# The line boundary vector of the entry section at every face (Passage, part D5)

`phiLineAt_any_of_res`: if the standard good-line coordinate of a stratum class `a` restricts on `Λ₁⁺` to `c` times the complexified `ε = 1` seed, then for *every* face `h` of a good line (no clean-frame
hypothesis) `phiLineAt h a = c • (seedKer h f + (-1)ⁿ • seedConjKer h f^*)`: write `h = b * h'` with a clean frame `h'` (`exists_clean_frame`), use the coordinate formula at the frame `b * h'`
(`phiLineAt_frame_of_res`) and the frame invariance of the seed combination (`seedComb_frame`).  Hence `phiLine_goodLineClass_uncond` and `phiLine_paperLine`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Adelic Matrix CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 fStar)
open TernaryPeriodPolynomials.Argument.KDaggerComparison (stdLine phiLineAt phiLine levelN)
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.LineSeed (reflSeedInv)
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.EntryDictionary
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Argument.KDaggerComparison (goodLineClass)

section

variable {N : ℕ} [NeZero N] {n : ℕ}

theorem phiLineAt_any_of_res (hn : Odd n) (h3 : 3 ∣ N) (hN : 3 ≤ N) (a : StratumH2 n trivialCharacter .line)
    (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (c : ℂ)
    (hres : linePlusRes n (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) stdLine a) =
      c • lineComplexify n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
        (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f 1)))
    (h : SL(3, ℤ)) (hgood : GoodFlag .line (lineFlagAt h)) :
    phiLineAt N h3 hN n h a = c • ((lineFaceSeedKerClass N n h (levelN N f)).1 +
      (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1) := by
  obtain ⟨b, h', q, hb, hq, rfl, hclean, hF⟩ := exists_clean_frame h hgood
  rw [phiLineAt_frame_of_res N h3 hN n h' b hb hq hF hclean a f 1 c hres, one_mul]
  have hfr := seedComb_frame (N := N) (n := n) hn f h' b hb
  rw [hfr]

end


section Entry

variable {N : ℕ} [NeZero N] {n : ℕ} (hn : Odd n) (h3 : 3 ∣ N) (hN : 3 ≤ N) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
  (I : EichlerInput M.cusp n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
  (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I)

include hn hf in
/-- **The face coordinate of the library's section `a_li` at every good line cusp** (`(n+1)/2` times the seed combination). -/
theorem phiLineAt_goodLineClass_any (h : SL(3, ℤ)) (hgood : GoodFlag .line (lineFlagAt h)) :
    phiLineAt N h3 hN n h (goodLineClass S I).val = (((n : ℂ) + 1) / 2) •
      ((lineFaceSeedKerClass N n h (levelN N f)).1 +
        (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1) := by
  obtain ⟨f', hf', hid⟩ := lineSeedIdentity hn M S I
  obtain rfl : f = f' := DFunLike.coe_injective (hf.trans hf'.symm)
  exact phiLineAt_any_of_res hn h3 hN _ f _ hid h hgood

include hn hf in
/-- **`phiLine_goodLineClass_uncond`**: the line boundary vector of the entry section `a_li` is the seed boundary of `lineEntryTuple f`, with no hypothesis on the faces. -/
theorem phiLine_goodLineClass_uncond :
    phiLine N h3 hN n (goodLineClass S I).val = lineSeedBoundary N n (lineEntryTuple N n f) :=
  phiLine_goodLineClass h3 hN M S I f (fun i hg => phiLineAt_goodLineClass_any hn h3 hN M S I f hf i.rep hg)

include hn hf in
/-- **The line boundary vector of the paper's good-line section** (`λ_li = -1`): scalar `-(n+1)/2`. -/
theorem phiLine_paperLine (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand M.inducingData .plane →ₗ[ℂ] boundarySummand M.inducingData .line)
    (hT : RealizesStandardConv M.inducingData T) :
    ∃ hLP : IsSourceCocycle M.inducingData .line
        (fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g),
      phiLine N h3 hN n (SourceQuotient.sourceToSummand M.inducingData .line
          ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val =
        lineSeedBoundary N n (lineEntryTupleC (-(((n : ℂ) + 1) / 2)) f) := by
  obtain ⟨f', hf', hLP, hid⟩ := paperLineSeedIdentity hn M S I hw hv T hT
  obtain rfl : f = f' := DFunLike.coe_injective (hf.trans hf'.symm)
  exact ⟨hLP, phiLine_eq_lineSeedBoundaryC h3 hN _ _ f
    (fun i hb => phiLineAt_weighted_bad N h3 hN M _ hLP i.rep hb)
    (fun i hg => phiLineAt_any_of_res hn h3 hN _ f _ hid i.rep hg)⟩

end Entry

end TernaryPeriodPolynomials.Argument.LineSeed
