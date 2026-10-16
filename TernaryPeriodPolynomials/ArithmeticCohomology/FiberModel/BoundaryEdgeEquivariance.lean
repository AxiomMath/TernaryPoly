module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.GeometricRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.TranslatedApartment
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalAction

@[expose] public section


/-!
# `IntegralGL`-equivariance of the Mayer-Vietoris edge map

The principal-six boundary chains `boundaryChains` carry the restriction of the `IntegralGL`-complex
`fullBoundaryChains` (`bdryAct : GActC boundaryChains`).  The library identifies the geometric
Mayer-Vietoris edge map `boundaryEdgeMap` on `H₁` of the boundary, through the `IntegralGL`-equivariant
quasi-isomorphism from the full face cone, with minus the (equivariant) corner coordinate of the cone
(`restrictedFullFace_boundary_edge`).  Hence `boundaryEdgeMap` and the identification
`boundaryH1OrdinaryCyclesIso` of `H₁` of the boundary with the ordinary cycles intertwine the action of
`g ∈ IntegralGL` on cycle representatives with its action on flag labels, resp. ordinary cycles
(`boundaryEdgeMap_cycAct`, `boundaryH1OrdinaryCyclesIso_cycAct`).  No collar, cover or frame choice
enters.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.SymmetricSpaceBoundaryFullTransfer
  TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPoly.OrdinaryBoundaryActualEvaluation TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
  TernaryPeriodPolynomials.Argument.GroupHomology

/-- The `IntegralGL`-action on the principal-six boundary chains. -/
def bdryAct : GActC (H := principalSix) boundaryChains :=
  GActC.ofChain principalSix fullBoundaryChains

/-- The `IntegralGL`-action on the restricted full face cone. -/
def coneAct : GActC (H := principalSix) (coverRestrictionFunctor.obj fullFaceCone) :=
  GActC.ofChain principalSix fullFaceCone

/-- The full face cone map, restricted to level six, with its target the principal-six boundary. -/
abbrev qBd : coverRestrictionFunctor.obj fullFaceCone ⟶ boundaryChains :=
  coverRestrictionFunctor.map fullFaceConeToBoundary

theorem coneToBoundary_gmor : IsGMorC coneAct bdryAct qBd :=
  GActC.isGMorC_ofChain principalSix fullFaceConeToBoundary

theorem coneToBoundary_surj (z : Cyc boundaryChains 0) :
    ∃ c : Cyc (coverRestrictionFunctor.obj fullFaceCone) 0,
      (Cyc.map qBd c).cls = z.cls := by
  have hq : QuasiIso (coverRestrictionFunctor.map fullFaceConeToBoundary) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology fullFaceConeToBoundary
      (Rep.resFunctor principalSix.subtype)).mpr inferInstance
  have hi : IsIso (homologyMap (coverRestrictionFunctor.map fullFaceConeToBoundary) 1) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp (hq.quasiIsoAt 1)
  obtain ⟨h, hh⟩ := (Rep.epi_iff_surjective
    (homologyMap (coverRestrictionFunctor.map fullFaceConeToBoundary) 1)).mp inferInstance z.cls
  obtain ⟨c, rfl⟩ := Cyc.exists_cls h
  exact ⟨c, (Cyc.cls_map _ c).symm.trans hh⟩

/-- The geometric edge of a cone cycle is minus its augmented corner coordinate. -/
theorem edge_cone (c : Cyc (coverRestrictionFunctor.obj fullFaceCone) 0) :
    boundaryEdgeMap (Cyc.map qBd c).cls =
      -(coneCornerCochain fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)).hom c.1 := by
  have h := congrArg (fun f => f.hom c.cls) restrictedFullFace_boundary_edge
  have hp := congrArg (fun f => f.hom (cycMk (coverRestrictionFunctor.obj fullFaceCone) 0 c.1 c.2))
    (restrictedEvaluation_projection principalSix fullFaceCone fullFlagLabels 1
      (coneCornerCochain fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0))
      (coneCornerCochain_boundary fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)
        fullFlagResolution.complex_d_comp_π_f_zero))
  have hcorner : restrictedFullCorner c.cls =
      (coneCornerCochain fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)).hom c.1 := by
    unfold restrictedFullCorner
    refine hp.trans ?_
    change (coneCornerCochain fullFaceArrow fullFlagLabels (fullFlagResolution.π.f 0)).hom
      ((coverRestrictionFunctor.obj fullFaceCone).iCycles 1
        (cycMk (coverRestrictionFunctor.obj fullFaceCone) 0 c.1 c.2)) = _
    rw [iCycles_cycMk]
  have h1 : (homologyMap (coverRestrictionFunctor.map fullFaceConeToBoundary) 1 ≫ boundaryEdgeMap).hom
      c.cls = boundaryEdgeMap (Cyc.map qBd c).cls :=
    congrArg boundaryEdgeMap.hom (Cyc.cls_map _ c)
  rw [← h1]
  refine h.trans ?_
  change -(restrictedFullCorner c.cls) = _
  rw [hcorner]

/-- **Equivariance of the Mayer-Vietoris edge map under `IntegralGL`.**  For every cycle `z` of the
principal-six boundary chains and `g ∈ IntegralGL`, the edge coefficients of the translated class
`[g z]` are the `g`-translate of those of `[z]`. -/
theorem boundaryEdgeMap_cycAct (g : IntegralGL) (z : Cyc boundaryChains 0) :
    boundaryEdgeMap (bdryAct.cycAct g z).cls = fullFlagLabels.ρ g (boundaryEdgeMap z.cls) := by
  obtain ⟨c, hc⟩ := coneToBoundary_surj z
  obtain ⟨b, hb⟩ := (Cyc.cls_eq_iff _ _).mp hc
  have key : (bdryAct.cycAct g z).cls =
      (Cyc.map qBd (coneAct.cycAct g c)).cls := by
    rw [(coneToBoundary_gmor).map_cycAct g c]
    apply (Cyc.cls_eq_iff _ _).mpr
    refine ⟨(bdryAct.act 2).ρ g (-b), ?_⟩
    have hb' : (boundaryChains.d 2 1).hom b = (Cyc.map qBd c).1 - z.1 := hb
    have h2 : (boundaryChains.d 2 1).hom (-b) = z.1 - (Cyc.map qBd c).1 := by
      rw [map_neg, hb', neg_sub]
    have h1 := bdryAct.comm g 2 1 (-b)
    rw [h2] at h1
    change (boundaryChains.d 2 1).hom ((bdryAct.act 2).ρ g (-b)) =
      (bdryAct.act 1).ρ g z.1 - (bdryAct.act 1).ρ g (Cyc.map qBd c).1
    rw [h1, map_sub]
  rw [key, edge_cone, ← hc, edge_cone, map_neg]
  congr 1
  exact (Rep.hom_comm_apply (coneCornerCochain fullFaceArrow fullFlagLabels
    (fullFlagResolution.π.f 0)) g c.1)

/-- **Equivariance of the boundary-`H₁` identification with the ordinary cycles.** -/
theorem boundaryH1OrdinaryCyclesIso_cycAct (g : IntegralGL) (z : Cyc boundaryChains 0) :
    boundaryH1OrdinaryCyclesIso.hom (bdryAct.cycAct g z).cls =
      TernaryPoly.OrdinaryFullAction.cycleAction (TernaryPoly.OrdinaryFullAction.integral g)
        (boundaryH1OrdinaryCyclesIso.hom z.cls) := by
  apply (Rep.mono_iff_injective ordinaryCycleInclusion).mp inferInstance
  have h1 := congrArg (fun f => f.hom (bdryAct.cycAct g z).cls) boundaryH1OrdinaryCyclesIso_edge
  have h2 := congrArg (fun f => f.hom z.cls) boundaryH1OrdinaryCyclesIso_edge
  change ordinaryCycleInclusion.hom (boundaryH1OrdinaryCyclesIso.hom (bdryAct.cycAct g z).cls) =
    boundaryEdgeMap (bdryAct.cycAct g z).cls at h1
  change ordinaryCycleInclusion.hom (boundaryH1OrdinaryCyclesIso.hom z.cls) =
    boundaryEdgeMap z.cls at h2
  rw [h1, boundaryEdgeMap_cycAct, ← h2]
  exact (integral_ordinaryCycleInclusion_action g _).symm

end TernaryPeriodPolynomials.Argument.FiberModel
