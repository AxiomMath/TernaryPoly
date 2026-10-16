module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyAugmentation
public import TernaryPeriodPolynomials.Topology.Equivariant.MayerVietoris.HomologySquares

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits HomologicalComplex FreeActionLinearization
open IntegralGL3Congruence SingularBoundaryRestriction SymmetricSpaceBoundaryMV
open EquivariantSingularResolution EquivariantSingularSmall EquivariantSingularMayerVietoris
open EquivariantMayerVietorisHomology SymmetricSpaceBoundaryFaceAugmentation SingularCoverNaturality

/-- The actual open-subspace inclusion into the geometric boundary. -/
def leftInclusionMap : TopCat.of UpstairsLine ⟶ ambient := TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩
def rightInclusionMap : TopCat.of UpstairsPlane ⟶ ambient := TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

theorem leftInclusionMap_equivariant (g : principalSix) (x : UpstairsLine) :
    leftInclusionMap (g • x)=g • leftInclusionMap x := rfl

theorem rightInclusionMap_equivariant (g : principalSix) (x : UpstairsPlane) :
    rightInclusionMap (g • x)=g • rightInclusionMap x := rfl

/-- The actual small-chain inclusion retains exactly the geometric left inclusion. -/
theorem left_chain_ambient :
    leftToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover ≫
      smallEquiv.hom=lineSubspaceIso.inv ≫ chainMap leftInclusionMap leftInclusionMap_equivariant := by
  have hs : smallEquiv.hom=smallInclusion principalSix ambient _ _ := smallHomotopyEquiv_hom _ _ _ _
  have h : lineSubspaceIso.hom ≫
      leftToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover ≫
        smallEquiv.hom=chainMap leftInclusionMap leftInclusionMap_equivariant := by
    rw [hs]
    apply HomologicalComplex.hom_ext
    intro n
    ext c
    rfl
  apply (cancel_epi lineSubspaceIso.hom).mp
  exact h.trans (Iso.hom_inv_id_assoc lineSubspaceIso _).symm

theorem right_chain_ambient :
    rightToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover ≫
      smallEquiv.hom=planeSubspaceIso.inv ≫ chainMap rightInclusionMap rightInclusionMap_equivariant := by
  have hs : smallEquiv.hom=smallInclusion principalSix ambient _ _ := smallHomotopyEquiv_hom _ _ _ _
  have h : planeSubspaceIso.hom ≫
      rightToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover ≫
        smallEquiv.hom=chainMap rightInclusionMap rightInclusionMap_equivariant := by
    rw [hs]
    apply HomologicalComplex.hom_ext
    intro n
    ext c
    rfl
  apply (cancel_epi planeSubspaceIso.hom).mp
  exact h.trans (Iso.hom_inv_id_assoc planeSubspaceIso _).symm

theorem leftH0_augmentation : leftH0Iso.hom ≫ labelSum=
    homologyMap lineSubspaceIso.inv 0 ≫ homologyAugmentation principalSix (TopCat.of UpstairsLine) :=
  (augmentation_composite (homologyMap lineSubspaceIso.inv 0)
    (homologyMap (chainMap lineRetractionMap lineSumRetraction_equivariant) 0) _ _ _ lineH0_sum).trans
      (congrArg (fun m => homologyMap lineSubspaceIso.inv 0 ≫ m)
        (homologyAugmentation_natural lineRetractionMap lineSumRetraction_equivariant))

theorem rightH0_augmentation : rightH0Iso.hom ≫ labelSum=
    homologyMap planeSubspaceIso.inv 0 ≫ homologyAugmentation principalSix (TopCat.of UpstairsPlane) :=
  (augmentation_composite (homologyMap planeSubspaceIso.inv 0)
    (homologyMap (chainMap planeRetractionMap planeSumRetraction_equivariant) 0) _ _ _ planeH0_sum).trans
      (congrArg (fun m => homologyMap planeSubspaceIso.inv 0 ≫ m)
        (homologyAugmentation_natural planeRetractionMap planeSumRetraction_equivariant))

/-- The homology map of the literal left inclusion preserves total coefficient under the face model. -/
theorem left_to_boundary_augmentation :
    homologyMap (leftToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover) 0 ≫
      (ambientHomologyIso 0).hom ≫ homologyAugmentation principalSix ambient=leftH0Iso.hom ≫ labelSum := by
  have h := congrArg (fun f => homologyMap f 0) left_chain_ambient
  rw [homologyMap_comp,homologyMap_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ homologyAugmentation principalSix ambient) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => homologyMap lineSubspaceIso.inv 0 ≫ m)
          (homologyAugmentation_natural leftInclusionMap leftInclusionMap_equivariant)).trans leftH0_augmentation.symm)))

theorem right_to_boundary_augmentation :
    homologyMap (rightToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover) 0 ≫
      (ambientHomologyIso 0).hom ≫ homologyAugmentation principalSix ambient=rightH0Iso.hom ≫ labelSum := by
  have h := congrArg (fun f => homologyMap f 0) right_chain_ambient
  rw [homologyMap_comp,homologyMap_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ homologyAugmentation principalSix ambient) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => homologyMap planeSubspaceIso.inv 0 ≫ m)
          (homologyAugmentation_natural rightInclusionMap rightInclusionMap_equivariant)).trans rightH0_augmentation.symm)))

/-- The genuine MV right arrow and boundary augmentation agree with the literal vertex sum. -/
theorem middle_to_boundary_augmentation : homologyMap mvComplex.g 0 ≫
    (ambientHomologyIso 0).hom ≫ homologyAugmentation principalSix ambient=
      middleH0Iso.hom ≫ vertexAugmentation := by
  let H := homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) 0
  let a := leftToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover
  let b := rightToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover
  have hmap := biprod.mapBiprod_inv_map_desc H leftComplex rightComplex a b
  have h := biprod_augmentation_square (H.map a) (H.map b)
    ((ambientHomologyIso 0).hom ≫ homologyAugmentation principalSix ambient) leftH0Iso rightH0Iso
      labelSum labelSum left_to_boundary_augmentation right_to_boundary_augmentation
  apply (cancel_epi (H.mapBiprod leftComplex rightComplex).inv).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ ((ambientHomologyIso 0).hom ≫ homologyAugmentation principalSix ambient)) hmap).trans
      (h.trans (Iso.inv_hom_id_assoc (H.mapBiprod leftComplex rightComplex) _).symm))

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
