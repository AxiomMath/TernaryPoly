module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Iso
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Vanishing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Cusps

@[expose] public section


/-!
# The locally inner classes at the four reference cusps are the mixed cuspidal groups

Instances of `Face/Iso` at the good and standard bad line and at the good and identity plane: the
locally inner classes of `H²(Γ_F, Sym^n)` are isomorphic, for every degree and character, to the
mixed cuspidal subspace of `H¹(L_F, H¹(N_F, Sym^n))` (`𝒞_R(E)` of Appendix C.2, one component per
face orbit). Together with `Face/Cusps` this describes `InnerBoundary` classes on each side as the
direct sum of the two mixed cuspidal groups of its two reference cusps.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (goodLineSplitting identityPlaneSplitting)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

theorem leviH2Vanishes_of_binary {Γ : Type} [Group Γ]
    (ψ : Γ →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ) :
    LeviH2Vanishes Γ :=
  fun ρ x => inhomogeneousH2_zero_of_binary ψ injective ρ x

/-- The standard bad line: locally inner classes `≃` mixed cuspidal group. -/
def badLineLocallyInnerEquiv (degree : ℕ) (character : RankOneCharacter) :
    locallyInnerClasses degree character .line standardBadLine ≃ₗ[ℂ]
      FaceCuspidal integralBadLineSplitting.conjAct degree character standardBadLine
        standardBadLineSemidirectEquiv :=
  locallyInnerEquivCuspidal _ degree character standardBadLine standardBadLineSemidirectEquiv
    (leviH2Vanishes_of_binary badLineLeviEmbedding badLineLeviEmbedding_injective)
    (fun radical e he => badLine_radical_fixes radical e he)
    badLineLeviEmbedding badLineLeviEmbedding_injective

/-- The good line. -/
def goodLineLocallyInnerEquiv (degree : ℕ) (character : RankOneCharacter) :
    locallyInnerClasses degree character .line goodLineFlag ≃ₗ[ℂ]
      FaceCuspidal goodLineSplitting.conjAct degree character goodLineFlag
        goodLineSemidirectEquivFixed :=
  locallyInnerEquivCuspidal _ degree character goodLineFlag goodLineSemidirectEquivFixed
    (leviH2Vanishes_of_binary goodLineLeviEmbedding goodLineLeviEmbedding_injective)
    (fun radical e he => goodLine_radical_fixes radical e he)
    goodLineLeviEmbedding goodLineLeviEmbedding_injective

/-- The identity plane. -/
def badPlaneLocallyInnerEquiv (degree : ℕ) (character : RankOneCharacter) :
    locallyInnerClasses degree character .plane badPlaneFlag ≃ₗ[ℂ]
      FaceCuspidal identityPlaneSplitting.conjAct degree character badPlaneFlag
        badPlaneSemidirectEquiv :=
  locallyInnerEquivCuspidal _ degree character badPlaneFlag badPlaneSemidirectEquiv
    (leviH2Vanishes_of_binary badPlaneLeviEmbedding badPlaneLeviEmbedding_injective)
    (fun radical e he => badPlane_radical_fixes radical e he)
    badPlaneLeviEmbedding badPlaneLeviEmbedding_injective

/-- The good plane. -/
def goodPlaneLocallyInnerEquiv (degree : ℕ) (character : RankOneCharacter) :
    locallyInnerClasses degree character .plane goodPlaneFlag ≃ₗ[ℂ]
      FaceCuspidal integralBadLineSplitting.conjAct degree character goodPlaneFlag
        goodPlaneSemidirectEquiv :=
  locallyInnerEquivCuspidal _ degree character goodPlaneFlag goodPlaneSemidirectEquiv
    (leviH2Vanishes_of_binary badLineLeviEmbedding badLineLeviEmbedding_injective)
    (fun radical e he => goodPlane_radical_fixes radical e he)
    badLineLeviEmbedding badLineLeviEmbedding_injective

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
