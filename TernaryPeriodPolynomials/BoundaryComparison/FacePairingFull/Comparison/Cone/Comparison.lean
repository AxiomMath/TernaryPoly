module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeComplete
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Setup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.BoundaryH4
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Corner
public import TernaryPeriodPolynomials.Topology.TopHomology.CoinvariantCycle

@[expose] public section


/-!
# The model cone and the library's stabilizer cone

The cone `coneR` of the signed incidence `ℚ[V^{•+1} × Flag] → ℚ[V^{•+1} × Line] ⊕ ℚ[V^{•+1} × Plane]` of the
three model resolutions is compared with the library's cone `stabilizerFaceCone` of the induced-bar
resolutions of the label stabilizers.  The library's generic comparison of resolutions
(`comparison`, `comparisonHomotopy`) and of cones (`CofiberSequence.comparisonMap`) gives a quasi-isomorphism
`uCone : coneR ⟶ stabilizerFaceCone` of complexes of projectives, hence a chain homotopy equivalence
(`exists_coneEquiv`).  Consequently the top cohomology of `coneR` with trivial rational coefficients is
`ℚ` (`coneR_H4`, from `stabilizerTotal_H4_iso`, Poincaré duality of the arithmetic boundary).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.EquivariantSingularSmall TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

/-- The model cone: the cone of the signed incidence of the three model resolutions. -/
abbrev coneR : ChainComplex (Rep.{0} ℚ Γ6) ℕ := signedCone flagLineHom.hom flagPlaneHom.hom

/-- The comparison map from the model cone to the stabilizer cone. -/
def uCone : coneR ⟶ stabilizerFaceCone :=
  CofiberSequence.comparisonMap (signedArrow flagLineHom.hom flagPlaneHom.hom) stabilizerFaceArrow
    (comparison resFlag flagStabilizerModel).hom
    (biprod.map (comparison resLine lineStabilizerModel).hom
      (comparison resPlane planeStabilizerModel).hom)
    (signedSquareHomotopy _ _ _ _ _ _ _
      (comparisonHomotopy resFlag flagStabilizerModel resLine lineStabilizerModel lineIncidence
        flagLineHom)
      (comparisonHomotopy resFlag flagStabilizerModel resPlane planeStabilizerModel planeIncidence
        flagPlaneHom))

theorem projective_middle (n : ℕ) :
    Projective ((resLine.complex ⊞ resPlane.complex).X n) := by
  have := resLine.projective n
  have := resPlane.projective n
  exact Projective.of_iso (HomologicalComplex.biprodXIso resLine.complex resPlane.complex n).symm
    inferInstance

theorem exists_middleEquiv :
    ∃ e : _root_.HomotopyEquiv (resLine.complex ⊞ resPlane.complex)
      (lineStabilizerModel.complex ⊞ planeStabilizerModel.complex),
      e.hom = biprod.map (comparison resLine lineStabilizerModel).hom
        (comparison resPlane planeStabilizerModel).hom := by
  have : ∀ n, Projective ((resLine.complex ⊞ resPlane.complex).X n) := projective_middle
  have : ∀ n, Projective ((lineStabilizerModel.complex ⊞ planeStabilizerModel.complex).X n) :=
    stabilizerMiddle_projective
  exact (ChainComplex.quasiIso_iff_of_projective _).mp
    (biprodMap_quasiIso (comparison resLine lineStabilizerModel).hom
      (comparison resPlane planeStabilizerModel).hom)

instance uCone_quasiIso : QuasiIso uCone :=
  CofiberSequence.comparisonMap_quasiIso _ _ _ _ _ (comparison resFlag flagStabilizerModel) rfl
    (Classical.choose exists_middleEquiv) (Classical.choose_spec exists_middleEquiv)

theorem exists_coneEquiv : ∃ e : _root_.HomotopyEquiv coneR stabilizerFaceCone, e.hom = uCone := by
  have : ∀ n, Projective (resFlag.complex.X n) := fun n => resFlag.projective n
  have : ∀ n, Projective ((resLine.complex ⊞ resPlane.complex).X n) := projective_middle
  have : ∀ n, Projective (coneR.X n) := fun n =>
    projectiveCone (signedArrow flagLineHom.hom flagPlaneHom.hom) n
  have : ∀ n, Projective (stabilizerFaceCone.X n) := stabilizerFaceCone_projective
  exact (ChainComplex.quasiIso_iff_of_projective uCone).mp inferInstance

/-- The top cohomology of the model cone with trivial rational coefficients is one-dimensional. -/
theorem coneR_H4 : Nonempty ((homCochains coneR trivialW).homology 4 ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨e, he⟩ := exists_coneEquiv
  have hq : QuasiIso (homPullback e.hom trivialW) := homPullback_quasiIso_of_homotopyEquiv e trivialW
  obtain ⟨iso⟩ := stabilizerTotal_H4_iso
  exact ⟨(isoOfQuasiIsoAt (homPullback e.hom trivialW) 4).symm ≪≫ iso⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
