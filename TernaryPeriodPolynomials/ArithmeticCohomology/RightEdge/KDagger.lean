module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.Faces
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.CuspIso

@[expose] public section


/-!
# The right edge for the four reference faces of the model

Formalized by Claude Sonnet 5.5.

Paper: "for a maximal-face stabilizer `R = N_R ⋊ L_R` ... `0 → H¹(L_R, H¹(N_R, E)) → H²(R, E) → H²(N_R, E)^{L_R} → 0`".  `RightEdge.semidirect_right_edge` applied to the
semidirect models of `FacePairingFull.Face` (`faceRep action degree character F ι`, the coefficient representation restricted to the stabilizer `Γ_F ≃* Radical ⋊ Levi` of the reference
flag `F` and transported to the semidirect product): for the standard bad line, the good line, the identity plane and the good plane, and every degree and character, the image of the radical restriction
`H²(Γ_F, E) → H²(N_F, E)` is the invariants of the Levi action `splitRadicalH2Action`.  (The left half is `Face.faceMixedEquiv`, `Face.locallyInnerEquivCuspidal`.)
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RightEdge

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- **Right edge at the standard bad line.** -/
theorem badLine_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : groupCohomology.H2 (Rep.res (SemidirectProduct.toGroupExtension integralBadLineSplitting.conjAct).inl
      (Rep.of (faceRep integralBadLineSplitting.conjAct degree character standardBadLine standardBadLineSemidirectEquiv)))) :
    y ∈ LinearMap.range (twoCohomologyRestriction
        (SemidirectProduct.toGroupExtension integralBadLineSplitting.conjAct).inl
        (Rep.of (faceRep integralBadLineSplitting.conjAct degree character standardBadLine standardBadLineSemidirectEquiv))) ↔
      ∀ l, splitRadicalH2Action (SemidirectProduct.inr_splitting integralBadLineSplitting.conjAct)
        (Rep.of (faceRep integralBadLineSplitting.conjAct degree character standardBadLine standardBadLineSemidirectEquiv)) l y = y :=
  semidirect_right_edge _ badLineLeviEmbedding badLineLeviEmbedding_injective _ y

/-- **Right edge at the good line.** -/
theorem goodLine_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : groupCohomology.H2 (Rep.res (SemidirectProduct.toGroupExtension goodLineSplitting.conjAct).inl
      (Rep.of (faceRep goodLineSplitting.conjAct degree character goodLineFlag goodLineSemidirectEquivFixed)))) :
    y ∈ LinearMap.range (twoCohomologyRestriction
        (SemidirectProduct.toGroupExtension goodLineSplitting.conjAct).inl
        (Rep.of (faceRep goodLineSplitting.conjAct degree character goodLineFlag goodLineSemidirectEquivFixed))) ↔
      ∀ l, splitRadicalH2Action (SemidirectProduct.inr_splitting goodLineSplitting.conjAct)
        (Rep.of (faceRep goodLineSplitting.conjAct degree character goodLineFlag goodLineSemidirectEquivFixed)) l y = y :=
  semidirect_right_edge _ goodLineLeviEmbedding goodLineLeviEmbedding_injective _ y

/-- **Right edge at the identity plane.** -/
theorem badPlane_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : groupCohomology.H2 (Rep.res (SemidirectProduct.toGroupExtension identityPlaneSplitting.conjAct).inl
      (Rep.of (faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag badPlaneSemidirectEquiv)))) :
    y ∈ LinearMap.range (twoCohomologyRestriction
        (SemidirectProduct.toGroupExtension identityPlaneSplitting.conjAct).inl
        (Rep.of (faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag badPlaneSemidirectEquiv))) ↔
      ∀ l, splitRadicalH2Action (SemidirectProduct.inr_splitting identityPlaneSplitting.conjAct)
        (Rep.of (faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag badPlaneSemidirectEquiv)) l y = y :=
  semidirect_right_edge _ badPlaneLeviEmbedding badPlaneLeviEmbedding_injective _ y

/-- **Right edge at the good plane.** -/
theorem goodPlane_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : groupCohomology.H2 (Rep.res (SemidirectProduct.toGroupExtension integralBadLineSplitting.conjAct).inl
      (Rep.of (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag goodPlaneSemidirectEquiv)))) :
    y ∈ LinearMap.range (twoCohomologyRestriction
        (SemidirectProduct.toGroupExtension integralBadLineSplitting.conjAct).inl
        (Rep.of (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag goodPlaneSemidirectEquiv))) ↔
      ∀ l, splitRadicalH2Action (SemidirectProduct.inr_splitting integralBadLineSplitting.conjAct)
        (Rep.of (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag goodPlaneSemidirectEquiv)) l y = y :=
  semidirect_right_edge _ badLineLeviEmbedding badLineLeviEmbedding_injective _ y

end TernaryPeriodPolynomials.Argument.RightEdge
