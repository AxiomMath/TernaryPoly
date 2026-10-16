module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RightEdge.KDagger
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.Bridge

@[expose] public section


/-!
# The right edge for the K† stabilizers, in the homogeneous model

Formalized by Claude Sonnet 5.5.

The classes of the model live in the HOMOGENEOUS cohomology `H2 (fixedPointLevel rationalLevel F) (rationalCoefficientComponent degree character)` of the stabilizer
`Γ_F` of a flag `F`; the face library moves them to the inhomogeneous model of the semidirect presentation `Γ_F ≃* Radical ⋊ Levi` by `Face.faceH2Equiv`, where the radical restriction is
`radicalRestrictionH2`.  Here the literal sequence for these groups:

* `leviH2ActionInh`: the Levi action on the library's `H²(N_F, E)` (`InhomogeneousH2 (faceRep ∘ inl)`), the transport of `splitRadicalH2Action` by `h2Equiv`;
* `face_homogeneous_right_edge`: for every flag `F` with semidirect presentation `ι` and Levi of vanishing `H²`,
  `y ∈ { radicalRestrictionH2 (faceH2Equiv x) | x ∈ H²_{hom}(Γ_F, E) } ↔ y` is `leviH2ActionInh`-invariant;
* `badLine_homogeneous_right_edge`, `goodLine_…`, `badPlane_…`, `goodPlane_…`: the four reference faces, every degree and character.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RightEdge

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.SeedC3S4c

section Generic

variable {Radical Levi : Type} [Group Radical] [Group Levi] (action : Levi →* MulAut Radical)
  (degree : ℕ) (character : RankOneCharacter) {side : Side} (F : Flags side)
  (ι : SemidirectProduct Radical Levi action ≃* fixedPointLevel rationalLevel F)

/-- **The Levi action on the library's `H²(N_F, E)`**: `splitRadicalH2Action` transported by `h2Equiv`. -/
def leviH2ActionInh (ρ' : Representation ℂ (SemidirectProduct Radical Levi action) (HomogeneousPoly degree)) (l : Levi) :
    InhomogeneousH2 (ρ'.comp SemidirectProduct.inl) →ₗ[ℂ] InhomogeneousH2 (ρ'.comp SemidirectProduct.inl) :=
  ((h2Equiv (ρ'.comp SemidirectProduct.inl)).symm.toLinearMap ∘ₗ
    splitRadicalH2Action (SemidirectProduct.inr_splitting action) (Rep.of ρ') l) ∘ₗ
      (h2Equiv (ρ'.comp SemidirectProduct.inl)).toLinearMap

theorem leviH2ActionInh_eq_iff (ρ' : Representation ℂ (SemidirectProduct Radical Levi action) (HomogeneousPoly degree)) (l : Levi)
    (y : InhomogeneousH2 (ρ'.comp SemidirectProduct.inl)) :
    leviH2ActionInh action degree ρ' l y = y ↔
      splitRadicalH2Action (SemidirectProduct.inr_splitting action) (Rep.of ρ') l (h2Equiv (ρ'.comp SemidirectProduct.inl) y) =
        h2Equiv (ρ'.comp SemidirectProduct.inl) y := by
  have : leviH2ActionInh action degree ρ' l y =
      (h2Equiv (ρ'.comp SemidirectProduct.inl)).symm
        (splitRadicalH2Action (SemidirectProduct.inr_splitting action) (Rep.of ρ') l
          (h2Equiv (ρ'.comp SemidirectProduct.inl) y)) := rfl
  rw [this]
  exact LinearEquiv.symm_apply_eq _

/-- **The Hochschild-Serre right edge for the stabilizer `Γ_F ≃* Radical ⋊ Levi` of a flag of the model**, in the homogeneous model: a class of the library's `H²(N_F, E)` is the radical
restriction of a homogeneous class of `H²(Γ_F, E)` iff it is invariant under the Levi action. -/
theorem face_homogeneous_right_edge (hL : H2Vanishes Levi)
    (y : InhomogeneousH2 ((faceRep action degree character F ι).comp SemidirectProduct.inl)) :
    (∃ x : H2 (fixedPointLevel rationalLevel F) (rationalCoefficientComponent degree character),
        radicalRestrictionH2 action (faceRep action degree character F ι) (faceH2Equiv action degree character F ι x) = y) ↔
      ∀ l, leviH2ActionInh action degree (faceRep action degree character F ι) l y = y := by
  have hres : ∀ x : InhomogeneousH2 (faceRep action degree character F ι),
      h2Equiv ((faceRep action degree character F ι).comp SemidirectProduct.inl)
        (radicalRestrictionH2 action (faceRep action degree character F ι) x) =
      twoCohomologyRestriction (SemidirectProduct.toGroupExtension action).inl
        (Rep.of (faceRep action degree character F ι)) (h2Equiv (faceRep action degree character F ι) x) :=
    fun x => (h2Equiv_radicalRestriction action (faceRep action degree character F ι) x).symm
  constructor
  · rintro ⟨x, rfl⟩ l
    rw [leviH2ActionInh_eq_iff, hres]
    exact restriction_invariant (SemidirectProduct.inr_splitting action) (Rep.of (faceRep action degree character F ι)) l _
  · intro hy
    have hy' : ∀ l, splitRadicalH2Action (SemidirectProduct.inr_splitting action) (Rep.of (faceRep action degree character F ι)) l
        (h2Equiv ((faceRep action degree character F ι).comp SemidirectProduct.inl) y) =
        h2Equiv ((faceRep action degree character F ι).comp SemidirectProduct.inl) y :=
      fun l => (leviH2ActionInh_eq_iff action degree _ l y).1 (hy l)
    obtain ⟨z', hz'⟩ := exists_lift (SemidirectProduct.inr_splitting action)
      (Rep.of (faceRep action degree character F ι)) hL _ hy'
    obtain ⟨x, hx⟩ := (faceH2Equiv action degree character F ι).surjective
      ((h2Equiv (faceRep action degree character F ι)).symm z')
    refine ⟨x, ?_⟩
    apply (h2Equiv ((faceRep action degree character F ι).comp SemidirectProduct.inl)).injective
    rw [hres, hx, LinearEquiv.apply_symm_apply]
    exact hz'

end Generic


section Named

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **Right edge at the standard bad line of the model, homogeneous model.** -/
theorem badLine_homogeneous_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : InhomogeneousH2 ((faceRep integralBadLineSplitting.conjAct degree character standardBadLine
      standardBadLineSemidirectEquiv).comp SemidirectProduct.inl)) :
    (∃ x : H2 (fixedPointLevel rationalLevel standardBadLine) (rationalCoefficientComponent degree character),
        radicalRestrictionH2 integralBadLineSplitting.conjAct
          (faceRep integralBadLineSplitting.conjAct degree character standardBadLine standardBadLineSemidirectEquiv)
          (faceH2Equiv integralBadLineSplitting.conjAct degree character standardBadLine standardBadLineSemidirectEquiv x) = y) ↔
      ∀ l, leviH2ActionInh integralBadLineSplitting.conjAct degree
        (faceRep integralBadLineSplitting.conjAct degree character standardBadLine standardBadLineSemidirectEquiv) l y = y :=
  face_homogeneous_right_edge _ degree character _ _
    (h2Vanishes_of_leviH2Vanishes (leviH2Vanishes_of_binary badLineLeviEmbedding badLineLeviEmbedding_injective)) y

/-- **Right edge at the good line, homogeneous model.** -/
theorem goodLine_homogeneous_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : InhomogeneousH2 ((faceRep goodLineSplitting.conjAct degree character goodLineFlag
      goodLineSemidirectEquivFixed).comp SemidirectProduct.inl)) :
    (∃ x : H2 (fixedPointLevel rationalLevel goodLineFlag) (rationalCoefficientComponent degree character),
        radicalRestrictionH2 goodLineSplitting.conjAct
          (faceRep goodLineSplitting.conjAct degree character goodLineFlag goodLineSemidirectEquivFixed)
          (faceH2Equiv goodLineSplitting.conjAct degree character goodLineFlag goodLineSemidirectEquivFixed x) = y) ↔
      ∀ l, leviH2ActionInh goodLineSplitting.conjAct degree
        (faceRep goodLineSplitting.conjAct degree character goodLineFlag goodLineSemidirectEquivFixed) l y = y :=
  face_homogeneous_right_edge _ degree character _ _
    (h2Vanishes_of_leviH2Vanishes (leviH2Vanishes_of_binary goodLineLeviEmbedding goodLineLeviEmbedding_injective)) y

/-- **Right edge at the identity plane, homogeneous model.** -/
theorem badPlane_homogeneous_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : InhomogeneousH2 ((faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag
      badPlaneSemidirectEquiv).comp SemidirectProduct.inl)) :
    (∃ x : H2 (fixedPointLevel rationalLevel badPlaneFlag) (rationalCoefficientComponent degree character),
        radicalRestrictionH2 identityPlaneSplitting.conjAct
          (faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag badPlaneSemidirectEquiv)
          (faceH2Equiv identityPlaneSplitting.conjAct degree character badPlaneFlag badPlaneSemidirectEquiv x) = y) ↔
      ∀ l, leviH2ActionInh identityPlaneSplitting.conjAct degree
        (faceRep identityPlaneSplitting.conjAct degree character badPlaneFlag badPlaneSemidirectEquiv) l y = y :=
  face_homogeneous_right_edge _ degree character _ _
    (h2Vanishes_of_leviH2Vanishes (leviH2Vanishes_of_binary badPlaneLeviEmbedding badPlaneLeviEmbedding_injective)) y

/-- **Right edge at the good plane, homogeneous model.** -/
theorem goodPlane_homogeneous_right_edge (degree : ℕ) (character : RankOneCharacter)
    (y : InhomogeneousH2 ((faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag
      goodPlaneSemidirectEquiv).comp SemidirectProduct.inl)) :
    (∃ x : H2 (fixedPointLevel rationalLevel goodPlaneFlag) (rationalCoefficientComponent degree character),
        radicalRestrictionH2 integralBadLineSplitting.conjAct
          (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag goodPlaneSemidirectEquiv)
          (faceH2Equiv integralBadLineSplitting.conjAct degree character goodPlaneFlag goodPlaneSemidirectEquiv x) = y) ↔
      ∀ l, leviH2ActionInh integralBadLineSplitting.conjAct degree
        (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag goodPlaneSemidirectEquiv) l y = y :=
  face_homogeneous_right_edge _ degree character _ _
    (h2Vanishes_of_leviH2Vanishes (leviH2Vanishes_of_binary badLineLeviEmbedding badLineLeviEmbedding_injective)) y

end Named

end TernaryPeriodPolynomials.Argument.RightEdge
