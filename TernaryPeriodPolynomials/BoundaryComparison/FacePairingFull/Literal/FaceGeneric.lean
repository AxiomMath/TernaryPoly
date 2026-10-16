module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Iso

@[expose] public section


/-!
# The Hochschild-Serre isomorphism on a representative, for an arbitrary face

Generic form of the two facts used to compare the library's explicit edge maps with the Hochschild-Serre
isomorphism `locallyInnerEquivCuspidal` of `Face/Iso`, so that the face-specific comparisons
(`Literal.GoodLineIdentification`, `Literal.BadPlaneIdentification`, `Literal.GoodPlaneIdentification`) only
instantiate them:

* `exists_radicalZero_representative`: a locally inner class has a radical-zero inhomogeneous representative;
* `locallyInnerEquivCuspidal_coe_eq_mixed`: its image under `locallyInnerEquivCuspidal` is the mixed class of that
  representative (`mixedH1CocycleMap`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.FaceGeneric

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)
  (hL : LeviH2Vanishes Levi)
  (hfix : ∀ radical : Radical, ∀ e : Edges, endpoint side e = F →
    (ι (SemidirectProduct.inl radical)).val • e = e)
  (ψ : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ) (injective : Function.Injective ψ)

include hfix ψ injective

/-- A locally inner class has a radical-zero inhomogeneous representative. -/
theorem exists_radicalZero_representative
    (x : H2 (fixedPointLevel rationalLevel F) (rationalCoefficientComponent degree character))
    (hx : x ∈ locallyInnerClasses degree character side F) :
    ∃ c₀ : radicalZeroTwoCycles action (faceRep action degree character F ι),
      (inhomogeneousBoundaries (faceRep action degree character F ι)).mkQ c₀.val =
        faceH2Equiv action degree character F ι x :=
  radicalRestrictionH2_ker_representative action (faceRep action degree character F ι) _
    (locallyInner_le_faceRadicalZero action degree character F ι hfix ψ injective hx)

/-- The Hochschild-Serre image of a locally inner class is the mixed class of any radical-zero representative. -/
theorem locallyInnerEquivCuspidal_coe_eq_mixed
    (x : H2 (fixedPointLevel rationalLevel F) (rationalCoefficientComponent degree character))
    (hx : x ∈ locallyInnerClasses degree character side F)
    (c₀ : radicalZeroTwoCycles action (faceRep action degree character F ι))
    (hc₀ : (inhomogeneousBoundaries (faceRep action degree character F ι)).mkQ c₀.val =
      faceH2Equiv action degree character F ι x) :
    ((locallyInnerEquivCuspidal action degree character F ι hL hfix ψ injective ⟨x, hx⟩ :
        FaceCuspidal action degree character F ι) :
        CrossedH1 (leviCrossedH1Representation action (faceRep action degree character F ι))) =
      (crossedBoundaries (leviCrossedH1Representation action
        (faceRep action degree character F ι))).mkQ
        (mixedH1CocycleMap action (faceRep action degree character F ι) c₀) := by
  have hrz := locallyInner_le_faceRadicalZero action degree character F ι hfix ψ injective hx
  have hsub : (⟨faceH2Equiv action degree character F ι x, hrz⟩ :
      (radicalRestrictionH2 action (faceRep action degree character F ι)).ker) =
      radicalZeroH2ToKernel action (faceRep action degree character F ι)
        ((radicalZeroBoundaries action (faceRep action degree character F ι)).mkQ c₀) :=
    Subtype.ext hc₀.symm
  have h0 : ((locallyInnerEquivCuspidal action degree character F ι hL hfix ψ injective ⟨x, hx⟩ :
        FaceCuspidal action degree character F ι) :
        CrossedH1 (leviCrossedH1Representation action (faceRep action degree character F ι))) =
      radicalKernelMixedMap action (faceRep action degree character F ι)
        ⟨faceH2Equiv action degree character F ι x, hrz⟩ := rfl
  exact h0.trans ((congrArg (radicalKernelMixedMap action (faceRep action degree character F ι)) hsub).trans
    (radicalKernelMixedMap_representative action (faceRep action degree character F ι) c₀))

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal.FaceGeneric
