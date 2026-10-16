module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Aug

@[expose] public section


/-!
# Any comparison over the augmentation induces the singular restriction on restriction classes

For a chain map `G : coneR ⟶ boundaryChains` with `G ≫ augB = augR`, the transport
`(cochainIso boundary)⁻¹ ≫ homPullback G W : localBoundaryCochains W ⟶ homCochains coneR W` sends the singular restriction
`j^* x` to the boundary of the bordification of a class `x` of `H^n(Γ(6); W)` (computed on the point resolution) to the
geometric restriction `H(coneToPt) x` of the model cone.  This is the statement of `singular_restriction_eq_geoRestriction`
for the library comparison `cb = coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary` (which has the same
augmentation, `coneBoundary_augB`), with `cb` replaced by an arbitrary `G` over the augmentation: only the augmentation of
the composite `G ≫ boundaryIncl ≫ resolutionComparison ≫ fixThetaBar` enters (`homologyMap_homPullback_eq_of_augmentation`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceRationalGluing
open TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularCoverNaturality
open TernaryPoly.EquivariantSingularSmall
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

/-- The transport of the local-system cochains of the boundary to the Hom cochains of the model cone along `G`. -/
def transport (G : coneR ⟶ boundaryChains) (W : Rep.{0} ℚ principalSix) :
    localBoundaryCochains W ⟶ homCochains coneR W :=
  (SingularLocalCoefficient.cochainIso boundaryProjection boundaryQuotientCovering W).inv ≫ homPullback G W

/-- The chain map from the model cone to the point resolution through the bordification, built from `G`. -/
def coneToPtVia (G : coneR ⟶ boundaryChains) : coneR ⟶ prodComplex Γ6 RationalGL3 PUnit :=
  G ≫ boundaryIncl ≫ EquivariantSingularCohomology.resolutionComparison principalSix (TopCat.of Glued) ≫
    fixThetaBar (1 : RationalGL3) PUnit.unit (fun _ => rfl)

theorem coneToPtVia_aug (G : coneR ⟶ boundaryChains) (hG : G ≫ augB = augR) :
    coneToPtVia G ≫ resAug ptRes = augR := by
  have e : coneToPtVia G ≫ resAug ptRes =
      G ≫ (boundaryIncl ≫ (EquivariantSingularCohomology.resolutionComparison principalSix (TopCat.of Glued) ≫
          (fixThetaBar (1 : RationalGL3) PUnit.unit (fun _ => rfl) ≫ resAug ptRes))) := by
    simp only [coneToPtVia, Category.assoc]
  rw [e, fixThetaBar_resAug, resolutionComparison_aug, boundaryIncl_aug]
  exact hG

theorem coneToPtVia_augmentation (G : coneR ⟶ boundaryChains) (hG : G ≫ augB = augR) :
    (coneToPtVia G).f 0 ≫ ptRes.π.f 0 = coneToPt.f 0 ≫ ptRes.π.f 0 := by
  have := labelSum_pt_mono
  refine (cancel_mono (labelSum (ι := PUnit))).mp ?_
  have h := congrArg (fun t => t.f 0) ((coneToPtVia_aug G hG).trans coneToPt_resAug.symm)
  exact (Category.assoc _ _ _).trans ((comp_f _ _ 0).symm.trans (h.trans
    ((comp_f _ _ 0).trans (Category.assoc _ _ _).symm)))

variable (W : Rep.{0} ℚ principalSix)

theorem restriction_chain_square_via (G : coneR ⟶ boundaryChains) :
    ((SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering W).hom ≫
        geometricBoundaryRestriction W) ≫ transport G W =
      boundaryRestriction W ≫ homPullback G W := by
  rw [← boundary_cochainIso_square W]
  unfold transport
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **Canonicity of the comparison on restriction classes.** -/
theorem transport_restriction (G : coneR ⟶ boundaryChains) (hG : G ≫ augB = augR) (n : ℕ) :
    fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W n ≫
        (SingularLocalCoefficient.groupLocalCohomologyIso wholeProjection wholeQuotientCovering W n).hom ≫
        homologyMap (geometricBoundaryRestriction W) n ≫ homologyMap (transport G W) n =
      homologyMap (homPullback coneToPt W) n := by
  have hg : homologyMap (homPullback (coneToPtVia G) W) n = homologyMap (homPullback coneToPt W) n :=
    homologyMap_homPullback_eq_of_augmentation (coneToPtVia G) (coneToPtVia_augmentation G hG) W n
  rw [← hg]
  have hcomp : (SingularLocalCoefficient.groupLocalCohomologyIso wholeProjection wholeQuotientCovering
      W n).hom = (gisoBar W n).hom ≫
        homologyMap (EquivariantSingularCohomology.barComparison principalSix (TopCat.of Glued) W ≫
          (SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering W).hom) n := by
    rw [SingularLocalCoefficient.groupLocalCohomologyIso_hom, EquivariantSingularCohomology.comparisonMap,
      gisoBar_hom]
    simp only [homologyMap_comp, Category.assoc]
    rfl
  have hchain : fixCoord (1 : RationalGL3) PUnit.unit (fun _ => rfl) W ≫
      (EquivariantSingularCohomology.barComparison principalSix (TopCat.of Glued) W ≫
        ((SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering W).hom ≫
          geometricBoundaryRestriction W ≫ transport G W)) = homPullback (coneToPtVia G) W := by
    have e := restriction_chain_square_via W G
    rw [Category.assoc] at e
    rw [e, barComparison_eq_homPullback, boundaryRestriction_eq_homPullback]
    unfold fixCoord coneToPtVia
    simp only [Category.assoc, homPullback_comp]
  unfold fixCoordH
  rw [hcomp, ← hchain]
  simp only [homologyMap_comp, Category.assoc, Iso.inv_hom_id_assoc]

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
