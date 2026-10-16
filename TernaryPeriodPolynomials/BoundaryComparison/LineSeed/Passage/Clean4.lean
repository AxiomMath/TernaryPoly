module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Clean2
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Clean3

@[expose] public section


/-!
# The face coordinate at a frame `b * h'` of a clean frame `h'` (Passage frame, part P3a)

`phiLineAt_frame_clean`: if `h'` is a clean frame for the transporter `q` and `b ∈ lineBorel`, the face coordinate `phiLineAt (b * h') a` is the frame transport of the image under
`H²(cleanHom h', cleanMor h')` of `linePlusRes n X`.  `phiLineAt_frame_of_res` specialises this to a class whose restriction is `c` times the complexified `ε`-seed.

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
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.KDaggerComparison (stdLine phiLineAt phiLineAt_transport levelN)
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.LineSeed (reflSeedInv)

section

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) (h' b : SL(3, ℤ)) (hb : b ∈ lineBorel) {q : RationalGL3}
  (hq : q ∈ rationalLevel) (hF : q • stdLine = lineFlagAt (b * h'))
  (hclean : Matrix.SpecialLinearGroup.mapGL ℚ h' * q = rationalGoodLine)

omit [NeZero N] in
include hclean in
theorem flag_clean : q • stdLine = lineFlagAt h' := by
  have hq' : q = Matrix.SpecialLinearGroup.mapGL ℚ h'⁻¹ * rationalGoodLine := q_eq_clean h' hclean
  have hs : rationalGoodLine * rationalGoodLine = 1 := rationalGoodLine_sq
  change (QuotientGroup.mk (q * rationalGoodLine) : Flags .line) = QuotientGroup.mk _
  rw [hq', mul_assoc, hs, mul_one]

include hb hq hF hclean in
theorem phiLineAt_frame_clean (a : StratumH2 n trivialCharacter .line) :
    phiLineAt N h3 hN n (b * h') a =
      EdgeNat.h2Map (frameHomQ N h' b hb) (lineFaceRep N h' n) (lineFaceRep N (b * h') n) (frameT n)
        (frameTQ_intertwines N h' n b hb)
        ((groupCohomology.map (cleanHom N h3 h') (cleanMor N h3 h' n) 2).hom
          (linePlusRes n (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) stdLine a))) := by
  have hF' : q • stdLine = lineFlagAt h' := flag_clean h' hclean
  refine (phiLineAt_transport N n h3 hN (b * h') hq hF a).trans ?_
  refine (h2Map_faceToStd_frame N h3 n h' b hb hq hF hF' _).trans ?_
  exact congrArg (EdgeNat.h2Map (frameHomQ N h' b hb) (lineFaceRep N h' n) (lineFaceRep N (b * h') n) (frameT n)
    (frameTQ_intertwines N h' n b hb)) (phiLineAt_clean N h3 n h' hq hF' hclean _)

include hb hq hF hclean in
theorem phiLineAt_frame_of_res (a : StratumH2 n trivialCharacter .line) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (ε : ℝ)
    (c : ℂ)
    (hres : linePlusRes n (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) stdLine a) =
      c • lineComplexify n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
        (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f ε))) :
    phiLineAt N h3 hN n (b * h') a =
      c • EdgeNat.h2Map (frameHomQ N h' b hb) (lineFaceRep N h' n) (lineFaceRep N (b * h') n) (frameT n)
        (frameTQ_intertwines N h' n b hb)
        ((lineFaceSeedKerClass N n h' (levelN N f)).1 +
          (((ε * (-1 : ℝ) ^ n : ℝ) : ℂ)) • (lineFaceSeedConjKerClass N n h' (levelN N (fStar f))).1) := by
  refine (phiLineAt_frame_clean N h3 hN n h' b hb hq hF hclean a).trans ?_
  rw [hres]
  have e1 := (groupCohomology.map (cleanHom N h3 h') (cleanMor N h3 h' n) 2).hom.map_smul c
    (lineComplexify n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty linePlusData.action
        (linePlusData.rhoR n) (reflSeedInv linePlusData linePlus_hΛ f ε)))
  rw [e1, clean_complexify N h3 h' f ε]
  exact ((EdgeNat.h2Map (frameHomQ N h' b hb) (lineFaceRep N h' n) (lineFaceRep N (b * h') n) (frameT n)
    (frameTQ_intertwines N h' n b hb)).map_smul c _)

end

end TernaryPeriodPolynomials.Argument.LineSeed
