module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Main
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.StrataCanon
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.Canon

@[expose] public section


/-!
# Canonicity of `Ψ` on all of cohomology; the face-wise glue through `modelBoundary_cohomology_iso`

The comparison `Ψ = u ≫ faceConeToBoundary` of the face-wise glue (`facePairing_glue_carried`), with `u` the carried
comparison of the model cone with the face cone, is chain homotopic to the library's comparison
`coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary` (`carried_boundary_homotopy`; the uniqueness of cone
maps up to homotopy of `ConeHomotopy` / `StrataCanon`).  Hence the transport `transport Ψ W` of the boundary cochains to the
Hom cochains of the model cone induces on cohomology, in every degree and for every coefficient system, exactly the map
underlying `modelBoundary_cohomology_iso` (`carried_transport_eq`), and the face-wise glue holds with the cohomology
classes of the boundary identified with those of the model cone through `modelBoundary_cohomology_iso`
(`facePairing_glue_canonical`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SingularBoundaryRestriction TernaryPoly.SymmetricSpaceRationalGluing
open TernaryPoly.EquivariantSingularResolution TernaryPoly.EquivariantSingularSmall
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open GeneralEisenstein
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction
attribute [local instance] CapCompat.lineLabelTopology CapCompat.planeLabelTopology CapCompat.flagLabelTopology CapCompat.lineLabelDiscrete
  CapCompat.planeLabelDiscrete CapCompat.flagLabelDiscrete

/-- A carried comparison, followed by `faceConeToBoundary`, is chain homotopic to the library's comparison
`coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary` of the model cone with the boundary chains. -/
theorem carried_boundary_homotopy (u : coneR ⟶ faceCone) (hu : CarriedPsi u) :
    Nonempty (Homotopy (u ≫ faceConeToBoundary)
      (coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary)) := by
  obtain ⟨H⟩ := carried_canonical u hu
  have H1 : Homotopy (u ≫ faceConeStabilizerEquiv.hom) coneEquiv.hom := by
    rw [faceConeStabilizerEquiv_hom, coneEquiv_hom_eq]; exact H
  have H2 : Homotopy u (coneEquiv.hom ≫ faceConeStabilizerEquiv.inv) :=
    ((Homotopy.ofEq (Category.comp_id u).symm).trans
      ((faceConeStabilizerEquiv.homotopyHomInvId.symm.compLeft u).trans
        ((Homotopy.ofEq (Category.assoc _ _ _).symm).trans (H1.compRight _))))
  exact ⟨(Homotopy.ofEq (Category.assoc _ _ _)).trans ((H2.compRight faceConeToBoundary).trans
    (Homotopy.ofEq (Category.assoc _ _ _)))⟩

/-- The library's `modelBoundaryQuasiIso` is the transport along its comparison `coneEquiv.hom ≫ stabilizerEquiv.inv ≫ faceConeToBoundary`. -/
theorem modelBoundaryQuasiIso_eq_transport (W : Rep.{0} ℚ principalSix) :
    modelBoundaryQuasiIso W =
      transport (coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary) W := by
  unfold modelBoundaryQuasiIso transport localBoundaryToStabilizerTotal localBoundaryToFaceTotal boundaryToFaceTotal
  simp only [Category.assoc, ← homPullback_comp]

/-- **Canonicity of `Ψ = u ≫ faceConeToBoundary` on all of cohomology.**  For a carried comparison `u`, the transport of
the local-system cochains of the boundary along `Ψ` to the Hom cochains of the model cone induces, in every degree and for
every coefficient system, the same map on cohomology as the library's `modelBoundaryQuasiIso`, the map underlying
`modelBoundary_cohomology_iso`. -/
theorem carried_transport_eq (u : coneR ⟶ faceCone) (hu : CarriedPsi u)
    (W : Rep.{0} ℚ principalSix) (n : ℕ) :
    homologyMap (transport (u ≫ faceConeToBoundary) W) n = homologyMap (modelBoundaryQuasiIso W) n := by
  obtain ⟨H⟩ := carried_boundary_homotopy u hu
  rw [modelBoundaryQuasiIso_eq_transport]
  exact ((TernaryPoly.EquivariantSingularPairHomotopy.homPullbackHomotopy H W).compLeft
    (SingularLocalCoefficient.cochainIso boundaryProjection boundaryQuotientCovering W).inv).homologyMap_eq n

/-- **The comparison of a carried `Ψ` is the library's, on all of cohomology.** -/
theorem isCarriedPsi_transport_eq {Ψ : coneR ⟶ boundaryChains} (hΨ : IsCarriedPsi Ψ) (W : Rep.{0} ℚ principalSix)
    (n : ℕ) : homologyMap (transport Ψ W) n = homologyMap (modelBoundaryQuasiIso W) n := by
  obtain ⟨u, hu, rfl⟩ := hΨ
  exact carried_transport_eq u hu W n

/-- The inverse of `modelBoundary_cohomology_iso` is the map induced by `modelBoundaryQuasiIso`. -/
theorem modelBoundary_cohomology_iso_inv (W : Rep.{0} ℚ principalSix) (n : ℕ) :
    (modelBoundary_cohomology_iso W n).inv = homologyMap (modelBoundaryQuasiIso W) n := rfl

/-- **The face-wise glue with the canonical identification.**  The comparison `Ψ` of the face-wise glue induces on
cohomology exactly the map `(modelBoundary_cohomology_iso W n).inv : H^n(∂M; W) → H^n(model cone; W)`, in every degree and for
every coefficient system `W`: the cone-side classes `[Ψ-pullback]` of the glue are the images under it of the classes of
the boundary cocycles. -/
theorem facePairing_glue_canonical : ∃ (Ψ : coneR ⟶ boundaryChains) (c : ℂ), QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧ c ≠ 0 ∧
    LineGlue Ψ c ∧ PlaneGlue Ψ (-c) ∧
    ∀ (W : Rep.{0} ℚ principalSix) (n : ℕ),
      homologyMap (transport Ψ W) n = (modelBoundary_cohomology_iso W n).inv := by
  obtain ⟨Ψ, c, hΨ, hq, haug, hc, hL, hP⟩ := facePairing_glue_carried
  exact ⟨Ψ, c, hq, haug, hc, hL, hP, fun W n =>
    (isCarriedPsi_transport_eq hΨ W n).trans (modelBoundary_cohomology_iso_inv W n).symm⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
