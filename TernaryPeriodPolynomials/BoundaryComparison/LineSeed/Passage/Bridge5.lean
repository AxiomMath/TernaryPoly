module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Bridge4
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.LineClassPaper

@[expose] public section


/-!
# The face coordinates of the good-line sections at a clean frame (Passage bridge, part 5)

`phiLineAt_of_res`: if the restriction `linePlusRes n` of the standard good-line coordinate `X = fixedPointH2 … stdLine a` of a stratum class `a` is `c` times the complexified de Rham class of the `ε`-seed of a
level-one form `f`, then for every face `h` with a clean-frame transporter `q` (`mapGL ℚ h * q = Π`, `q • std = h⁻¹⟨e₁⟩`) its face coordinate is
`phiLineAt h a = c • (lineFaceSeedKerClass h (levelN N f) + ε(-1)ⁿ • lineFaceSeedConjKerClass h (levelN N f^*))`.  With `lineSeedIdentity` and `paperLineSeedIdentity` this gives the scalars
`(n+1)/2` (library section `a_li`) and `-(n+1)/2` (paper's section) at every clean-frame face (`phiLineAt_goodLineClass`, `phiLineAt_paperLine`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.KDaggerComparison (stdLine phiLineAt phiLineAt_transport levelN)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 fStar)
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.LineSeed (reflSeedInv)

section

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel)
  (hF : q • stdLine = lineFlagAt h) (hclean : Matrix.SpecialLinearGroup.mapGL ℚ h * q = rationalGoodLine)

include hq hF hclean in
theorem phiLineAt_of_res (a : StratumH2 n trivialCharacter .line) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (ε : ℝ) (c : ℂ)
    (hres : linePlusRes n (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) stdLine a) =
      c • lineComplexify n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
        (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f ε))) :
    phiLineAt N h3 hN n h a = c • ((lineFaceSeedKerClass N n h (levelN N f)).1 +
      (((ε * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1) := by
  refine (phiLineAt_transport N n h3 hN h hq hF a).trans ?_
  refine (phiLineAt_clean N h3 n h hq hF hclean
    (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) stdLine a)).trans ?_
  rw [hres]
  exact ((groupCohomology.map (cleanHom N h3 h) (cleanMor N h3 h n) 2).hom.map_smul c _).trans
    (congrArg (fun z => c • z) (clean_complexify N h3 h f ε))

end


open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
open TernaryPeriodPolynomials.Argument.EntryDictionary
open GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Argument.KDaggerComparison (goodLineClass)

section Sections

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) {n : ℕ} (h : SL(3, ℤ)) {q : RationalGL3} (hq : q ∈ rationalLevel)
  (hF : q • stdLine = lineFlagAt h) (hclean : Matrix.SpecialLinearGroup.mapGL ℚ h * q = rationalGoodLine)

include hq hF hclean in
/-- **The face coordinate of the library's good-line section `a_li` at a clean-frame face**: `(n+1)/2` times the sum of the line seed classes of `f` and `f^*` (`ε = 1`). -/
theorem phiLineAt_goodLineClass (hn : Odd n) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I) :
    phiLineAt N h3 hN n h (goodLineClass S I).val =
      (((n : ℂ) + 1) / 2) • ((lineFaceSeedKerClass N n h (levelN N f)).1 +
        (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1) := by
  obtain ⟨f', hf', hid⟩ := lineSeedIdentity hn M S I
  obtain rfl : f = f' := DFunLike.coe_injective (hf.trans hf'.symm)
  exact phiLineAt_of_res N h3 hN n h hq hF hclean _ f 1 _ hid

include hq hF hclean in
/-- **The face coordinate of the paper's good-line section at a clean-frame face**: `-(n+1)/2` times the same combination. -/
theorem phiLineAt_paperLine (hn : Odd n) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n) (hw : I.halfWeight = S.halfWeight) (hv : I.vector = S.vector)
    (T : boundarySummand M.inducingData .plane →ₗ[ℂ] boundarySummand M.inducingData .line)
    (hT : RealizesStandardConv M.inducingData T) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))
    (hf : (f : UpperHalfPlane → ℂ) = classicalFormOfEichlerInput I) :
    ∃ hLP : IsSourceCocycle M.inducingData .line
        (fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g),
      phiLineAt N h3 hN n h (SourceQuotient.sourceToSummand M.inducingData .line
          ⟨fun y g => goodLineWeight g • cSigmaPaper n M.inducingData S.F y g, hLP⟩).val =
        (-(((n : ℂ) + 1) / 2)) • ((lineFaceSeedKerClass N n h (levelN N f)).1 +
          (((1 * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n h (levelN N (fStar f))).1) := by
  obtain ⟨f', hf', hLP, hid⟩ := paperLineSeedIdentity hn M S I hw hv T hT
  obtain rfl : f = f' := DFunLike.coe_injective (hf.trans hf'.symm)
  exact ⟨hLP, phiLineAt_of_res N h3 hN n h hq hF hclean _ f 1 _ hid⟩

end Sections

end TernaryPeriodPolynomials.Argument.LineSeed
