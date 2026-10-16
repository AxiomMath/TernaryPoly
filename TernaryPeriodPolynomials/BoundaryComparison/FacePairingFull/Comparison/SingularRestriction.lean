module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Augmentation
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryCohomology
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionCochains
public import TernaryPeriodPolynomials.Topology.GroupSingularCoefficientComparison

@[expose] public section


/-!
# The geometric restriction is the singular restriction to the boundary

The restriction `coneToPt : coneR ⟶ ptRes` of the model cone to the
point resolution (`geoRestriction`, `ConeRestriction`) is compared with the library's singular restriction
`H^n(M; W) → H^n(∂M; W)` (`geometricBoundaryRestriction`) through the identification
`groupLocalCohomologyIso` of group cohomology with the singular cohomology of the contractible bordification and
the quasi-isomorphism `modelBoundaryQuasiIso` of the singular boundary cochains with the model cone cochains
(which is built from `cone_to_boundary_quasiIso` and the homotopy equivalences `coneEquiv`,
`faceConeStabilizerEquiv`).

The chain-level content: the chain map `coneToPtSingular` from the model cone to the point resolution, which is
the boundary comparison `coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary` followed by the
inclusion `boundaryIncl` of the boundary chains in the chains of the bordification, the comparison of the
singular and the bar resolutions of `Γ(6)`, and `fixThetaBar` from the bar to the point resolution, has the
augmentation of `coneToPt` (`coneToPtSingular_augmentation`), because every map in the composite preserves the
coefficient sum (`ConeAugmentation`).  Two chain maps out of the cone, a complex of projectives, into a resolution
with the same augmentation are homotopic (`coneHomotopy`), so they induce the same map on cohomology
(`singular_restriction_eq_geoRestriction`).  The cohomology-level statement in degree two for the classes `ptCls`
of cocycles of `Γ(6)` is `geoRestriction_eq_singular_restriction`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology
open GeneralEisenstein

attribute [local instance] vertexAction

/-- The chain map out of the standard resolution to the point resolution. -/
abbrev fixThetaPt : Rep.standardComplex ℚ Γ6 ⟶ prodComplex Γ6 RationalGL3 PUnit :=
  fixTheta (1 : RationalGL3) PUnit.unit (fun _ => rfl)

theorem fixThetaPt_f_zero_aug :
    fixThetaPt.f 0 ≫ prodEps Γ6 RationalGL3 PUnit ≫ labelSum = Rep.standardComplex.ε ℚ Γ6 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  have key : ∀ y : Fin 1 → Γ6, (Rep.standardComplex.ε ℚ Γ6).hom (MonoidAlgebra.single y (1 : ℚ)) = 1 := by
    intro y
    simp [Rep.standardComplex.ε, MonoidAlgebra.coeff_single]
  have e1 := fixTheta_f_single (G := Γ6) (V := RationalGL3) (Z := PUnit) (1 : RationalGL3) PUnit.unit
    (fun _ => rfl) 0 x
  have e2 := prodEps_single Γ6 RationalGL3 PUnit (fun i => (x : Fin 1 → Γ6) i • (1 : RationalGL3)) PUnit.unit
  change labelSum ((prodEps Γ6 RationalGL3 PUnit).hom ((fixThetaPt.f 0).hom (MonoidAlgebra.single x 1))) =
    (Rep.standardComplex.ε ℚ Γ6).hom (MonoidAlgebra.single x 1)
  erw [e1, e2, labelSum_single]
  exact (key x).symm

theorem fixThetaBar_resAug :
    fixThetaBar (1 : RationalGL3) PUnit.unit (fun _ => rfl) ≫ resAug ptRes =
      (Rep.barResolution ℚ Γ6).π := by
  have h : fixThetaPt ≫ resAug ptRes = Rep.standardComplex.εToSingle₀ ℚ Γ6 := by
    apply eq_of_f_zero_single₀
    exact fixThetaPt_f_zero_aug
  change (Rep.barComplex.isoStandardComplex ℚ Γ6).hom ≫ fixThetaPt ≫ resAug ptRes = _
  rw [h]
  rfl

open TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceRationalGluing
open TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularCoverNaturality

/-- The chain map of the inclusion of the boundary into the bordification. -/
def boundaryIncl : boundaryChains ⟶ equivariantChains principalSix (TopCat.of Glued) :=
  chainMap boundaryInclusion boundaryInclusion_equivariant

theorem boundaryIncl_aug : boundaryIncl ≫ augmentationChain principalSix (TopCat.of Glued) = augB :=
  chainMap_augmentationChain boundaryInclusion boundaryInclusion_equivariant

theorem resolutionComparison_aug :
    EquivariantSingularCohomology.resolutionComparison principalSix (TopCat.of Glued) ≫
      (Rep.barResolution ℚ Γ6).π = augmentationChain principalSix (TopCat.of Glued) :=
  ProjectiveResolution.homotopyEquiv_hom_π _ _

/-- **The chain map from the model cone to the point resolution through the singular chains of the
bordification**: the boundary comparison, the inclusion of the boundary, the comparison of the
singular and bar resolutions of `Γ(6)`, and the comparison of the bar and point resolutions. -/
def coneToPtSingular : coneR ⟶ prodComplex Γ6 RationalGL3 PUnit :=
  (coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary) ≫ boundaryIncl ≫
    EquivariantSingularCohomology.resolutionComparison principalSix (TopCat.of Glued) ≫
      fixThetaBar (1 : RationalGL3) PUnit.unit (fun _ => rfl)

theorem coneToPtSingular_aug : coneToPtSingular ≫ resAug ptRes = augR := by
  have e : coneToPtSingular ≫ resAug ptRes =
      (coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary) ≫ (boundaryIncl ≫
        (EquivariantSingularCohomology.resolutionComparison principalSix (TopCat.of Glued) ≫
          (fixThetaBar (1 : RationalGL3) PUnit.unit (fun _ => rfl) ≫ resAug ptRes))) := by
    simp only [coneToPtSingular, Category.assoc]
  rw [e, fixThetaBar_resAug, resolutionComparison_aug, boundaryIncl_aug]
  exact coneBoundary_augB

theorem coneToPtSingular_augmentation :
    coneToPtSingular.f 0 ≫ ptRes.π.f 0 = coneToPt.f 0 ≫ ptRes.π.f 0 := by
  have := labelSum_pt_mono
  refine (cancel_mono (labelSum (ι := PUnit))).mp ?_
  have h := congrArg (fun t => t.f 0) (coneToPtSingular_aug.trans coneToPt_resAug.symm)
  exact (Category.assoc _ _ _).trans ((comp_f _ _ 0).symm.trans (h.trans
    ((comp_f _ _ 0).trans (Category.assoc _ _ _).symm)))

section Cochains

open TernaryPoly.EquivariantSingularSmall

variable (W : Rep.{0} ℚ principalSix)

theorem barComparison_eq_homPullback :
    EquivariantSingularCohomology.barComparison principalSix (TopCat.of Glued) W =
      homPullback (EquivariantSingularCohomology.resolutionComparison principalSix (TopCat.of Glued)) W := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  rfl

theorem boundaryRestriction_eq_homPullback : boundaryRestriction W = homPullback boundaryIncl W := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  rfl

/-- The chain-level identity behind `singular_restriction_eq_geoRestriction`: the singular restriction to the
boundary, followed by the comparison with the model cone, is the pullback along the boundary comparison. -/
theorem restriction_chain_square :
    ((SingularLocalCoefficient.cochainIso wholeProjection wholeQuotientCovering W).hom ≫
        geometricBoundaryRestriction W) ≫ modelBoundaryQuasiIso W =
      boundaryRestriction W ≫
        homPullback (coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary) W := by
  rw [← boundary_cochainIso_square, Category.assoc, modelBoundaryQuasiIso, localBoundaryToStabilizerTotal,
    localBoundaryToFaceTotal, boundaryToFaceTotal]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← homPullback_comp]

/-- **The geometric restriction of the model is the singular restriction to the boundary (link L5).** For every
rational representation `W` of `Γ(6)` and every degree `n`: restricting a class of the model cohomology of the
point resolution `ptRes` (equivalently, of `H^n(Γ(6); W)` through the bar resolution) to the model cone by
`coneToPt` is the same as identifying it with the singular cohomology of the contractible bordification
(`groupLocalCohomologyIso`), restricting to the actual boundary by the inclusion of `∂M` into `M`
(`geometricBoundaryRestriction`), and transporting to the model cone by the library's quasi-isomorphism
(`modelBoundaryQuasiIso`, which composes `cone_to_boundary_quasiIso` with the homotopy equivalences
`coneEquiv` and `faceConeStabilizerEquiv`). -/
theorem singular_restriction_eq_geoRestriction (n : ℕ) :
    fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W n ≫
        (SingularLocalCoefficient.groupLocalCohomologyIso wholeProjection wholeQuotientCovering W n).hom ≫
        homologyMap (geometricBoundaryRestriction W) n ≫ homologyMap (modelBoundaryQuasiIso W) n =
      homologyMap (homPullback coneToPt W) n := by
  have hg : homologyMap (homPullback coneToPtSingular W) n = homologyMap (homPullback coneToPt W) n :=
    homologyMap_homPullback_eq_of_augmentation coneToPtSingular coneToPtSingular_augmentation W n
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
          geometricBoundaryRestriction W ≫ modelBoundaryQuasiIso W)) = homPullback coneToPtSingular W := by
    have e := restriction_chain_square W
    rw [Category.assoc] at e
    rw [e, barComparison_eq_homPullback, boundaryRestriction_eq_homPullback]
    unfold fixCoord coneToPtSingular
    simp only [Category.assoc, homPullback_comp]
  unfold fixCoordH
  rw [hcomp, ← hchain]
  simp only [homologyMap_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- **The same, with the iso `modelBoundary_cohomology_iso`**: the singular restriction of the group class `fixCoordH y`
to the boundary is the geometric restriction of `y` transported to `H^n(∂M; W)`. -/
theorem singular_restriction_eq_geoRestriction_iso (n : ℕ) :
    homologyMap (homPullback coneToPt W) n ≫ (modelBoundary_cohomology_iso W n).hom =
      fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) W n ≫
        (SingularLocalCoefficient.groupLocalCohomologyIso wholeProjection wholeQuotientCovering W n).hom ≫
        homologyMap (geometricBoundaryRestriction W) n := by
  have h := singular_restriction_eq_geoRestriction W n
  rw [← h]
  simp only [modelBoundary_cohomology_iso, Category.assoc]
  simp

end Cochains

section Degree2

open GeneralEisenstein.Homogeneous

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- **Link L5 in degree two for cocycles of `Γ(6)`.** The geometric restriction `geoRestriction ρ c` of the
class of a cocycle `c` of `N6` to the model cone is the singular restriction to the boundary of the same class,
identified through `fixCoordH`, `groupLocalCohomologyIso`, `geometricBoundaryRestriction` and
`modelBoundaryQuasiIso`. -/
theorem geoRestriction_eq_singular_restriction (c : cocycles N6 ρ) :
    geoRestriction ρ c =
      (homologyMap (modelBoundaryQuasiIso (coeffRep ρ)) 2).hom
        ((homologyMap (geometricBoundaryRestriction (coeffRep ρ)) 2).hom
          ((SingularLocalCoefficient.groupLocalCohomologyIso wholeProjection wholeQuotientCovering
            (coeffRep ρ) 2).hom.hom
            ((fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (coeffRep ρ) 2).hom (ptCls ρ c)))) := by
  have h := congrArg (fun t => t.hom (ptCls ρ c))
    (singular_restriction_eq_geoRestriction (coeffRep ρ) 2)
  exact h.symm

end Degree2

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
