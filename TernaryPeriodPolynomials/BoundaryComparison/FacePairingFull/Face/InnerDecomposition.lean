module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Shapiro
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.CuspIso

@[expose] public section


/-!
# The inner classes of a side are the direct sum of its two mixed cuspidal groups

`innerClasses n .line ≃ 𝒞_{good line}(Sym^n) × 𝒞_{bad line}(Sym^n)` and
`innerClasses n .plane ≃ 𝒞_{good plane}(Sym^n) × 𝒞_{identity plane}(Sym^n)`, where each factor is the
mixed cuspidal subspace `FaceCuspidal ⊂ H¹(L_F, H¹(N_F, Sym^n))` of the paper (Appendix C.2),
for the trivial character and every degree `n`. This is the Shapiro decomposition
(`Face/Shapiro`) composed with the Hochschild-Serre isomorphisms (`Face/CuspIso`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (goodLineSplitting identityPlaneSplitting)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- **Line side:** `innerClasses n .line ≃ 𝒞_{good line} × 𝒞_{bad line}`. -/
def innerClassesLineEquiv (n : ℕ) :
    innerClasses n .line ≃ₗ[ℂ]
      FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
          goodLineSemidirectEquivFixed ×
        FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter standardBadLine
          standardBadLineSemidirectEquiv :=
  (innerClassesEquivLocal n goodLineFlag standardBadLine goodLineFlag_good
    standardBadLine_not_good).trans
    ((goodLineLocallyInnerEquiv n trivialCharacter).prodCongr
      (badLineLocallyInnerEquiv n trivialCharacter))

/-- **Plane side:** `innerClasses n .plane ≃ 𝒞_{good plane} × 𝒞_{identity plane}`. -/
def innerClassesPlaneEquiv (n : ℕ) :
    innerClasses n .plane ≃ₗ[ℂ]
      FaceCuspidal integralBadLineSplitting.conjAct n trivialCharacter goodPlaneFlag
          goodPlaneSemidirectEquiv ×
        FaceCuspidal identityPlaneSplitting.conjAct n trivialCharacter badPlaneFlag
          badPlaneSemidirectEquiv :=
  (innerClassesEquivLocal n goodPlaneFlag badPlaneFlag goodPlaneFlag_good
    badPlaneFlag_not_good).trans
    ((goodPlaneLocallyInnerEquiv n trivialCharacter).prodCongr
      (badPlaneLocallyInnerEquiv n trivialCharacter))

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
