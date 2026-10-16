module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeComparison
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullParabolicTotal

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryFullTransfer EquivariantSingularResolution EquivariantSingularSmall

instance restrictionReflectsIsomorphisms :
    (Rep.resFunctor principalSix.subtype (k := ℚ)).ReflectsIsomorphisms where
  reflects f _ := by
    let : Mono f := (Rep.mono_iff_injective f).mpr
      ((Rep.mono_iff_injective ((Rep.resFunctor principalSix.subtype).map f)).mp inferInstance)
    let : Epi f := (Rep.epi_iff_surjective f).mpr
      ((Rep.epi_iff_surjective ((Rep.resFunctor principalSix.subtype).map f)).mp inferInstance)
    exact isIso_of_mono_of_epi f

/-- The actual full integral cone map is a quasi-isomorphism, detected on the real cover chain complex. -/
instance fullFaceConeToBoundary_quasiIso : QuasiIso fullFaceConeToBoundary := by
  have h : faceConeRestrictionIso.inv ≫ coverRestrictionFunctor.map fullFaceConeToBoundary =
      SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary :=
    fullConeMap_restriction.trans coverStrictConeToBoundary_eq
  have hq : QuasiIso (faceConeRestrictionIso.inv ≫ coverRestrictionFunctor.map fullFaceConeToBoundary) := by
    rw [h]
    exact SymmetricSpaceBoundaryGeometricCone.faceConeToBoundary_quasiIso
  have hq' : QuasiIso (coverRestrictionFunctor.map fullFaceConeToBoundary) :=
    (quasiIso_iff_comp_left faceConeRestrictionIso.inv _).mp hq
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology fullFaceConeToBoundary
    (Rep.resFunctor principalSix.subtype)).mp hq'

instance fullBoundaryChain_projective (n : ℕ) : Projective (fullBoundaryChains.X n) := by
  let : Projective (Rep.res principalSix.subtype (fullBoundaryChains.X n)) :=
    chainRep_projective principalSix (TopCat.of SingularBoundaryRestriction.BoundaryCover) n
  exact projective_of_restriction principalSix _

theorem exists_fullFaceBoundaryEquiv : ∃ e : _root_.HomotopyEquiv fullFaceCone fullBoundaryChains,
    e.hom = fullFaceConeToBoundary := by
  have : ∀ n, Projective (fullFaceCone.X n) := fullFaceCone_projective
  exact (ChainComplex.quasiIso_iff_of_projective fullFaceConeToBoundary).mp inferInstance

/-- Genuine full integral equivariant homotopy equivalence to the entire boundary. -/
def fullFaceBoundaryEquiv := Classical.choose exists_fullFaceBoundaryEquiv

theorem fullFaceBoundaryEquiv_hom : fullFaceBoundaryEquiv.hom = fullFaceConeToBoundary :=
  Classical.choose_spec exists_fullFaceBoundaryEquiv

def fullBoundaryToFaceTotal (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    homCochains fullBoundaryChains W ⟶ fullFaceTotalCochains W :=
  homPullback fullFaceConeToBoundary W

instance fullBoundaryToFaceTotal_quasiIso (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL) :
    QuasiIso (fullBoundaryToFaceTotal W) := by
  have h := homPullback_quasiIso_of_homotopyEquiv fullFaceBoundaryEquiv W
  rw [fullFaceBoundaryEquiv_hom] at h
  exact h

end TernaryPoly.SymmetricSpaceBoundaryFull
