module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyAugmentationNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits HomologicalComplex FreeActionLinearization
open IntegralGL3Congruence EquivariantSingularResolution EquivariantMayerVietorisHomology
open scoped MonoidAlgebra

/-- The constructed graph comparison sends the actual right MV map to total vertex coefficient. -/
theorem middle_to_boundaryH0Iso : homologyMap mvComplex.g 0 ≫ (ambientHomologyIso 0).hom ≫
    boundaryH0Iso.hom=middleH0Iso.hom ≫ vertexAugmentation := by
  let e := homologyZeroCokernelIso mvComplex mvShortExact
  let k := cokernel.mapIso (homologyMap mvComplex.f 0) incidence interH0Iso middleH0Iso incidence_natural
  have he : homologyMap mvComplex.g 0 ≫ e.hom=cokernel.π (homologyMap mvComplex.f 0) :=
    homologyMap_homologyZeroCokernelIso mvComplex mvShortExact
  have hk : cokernel.π (homologyMap mvComplex.f 0) ≫ k.hom=middleH0Iso.hom ≫ cokernel.π incidence :=
    cokernel.π_desc (homologyMap mvComplex.f 0) (middleH0Iso.hom ≫ cokernel.π incidence) _
  have h : homologyMap mvComplex.g 0 ≫ e.hom ≫ k.hom ≫ incidenceCokernelIso.hom=
      middleH0Iso.hom ≫ vertexAugmentation :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ (k.hom ≫ incidenceCokernelIso.hom)) he).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ incidenceCokernelIso.hom) hk).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun m => middleH0Iso.hom ≫ m) incidenceCokernelIso_augmentation)))))
  exact (congrArg (fun m => homologyMap mvComplex.g 0 ≫ m)
    (iso_cancel_composite (ambientHomologyIso 0) e k incidenceCokernelIso)).trans h

/-- H0 isomorphism is literally the genuine singular coefficient-sum augmentation. -/
theorem boundaryH0Iso_augmentation : boundaryH0Iso.hom=homologyAugmentation principalSix ambient := by
  have : Epi (homologyMap mvComplex.g 0) := homologyZero_epi mvComplex mvShortExact
  apply (cancel_epi (ambientHomologyIso 0).hom).mp
  apply (cancel_epi (homologyMap mvComplex.g 0)).mp
  exact middle_to_boundaryH0Iso.trans middle_to_boundary_augmentation.symm

instance boundaryHomologyAugmentation_isIso : IsIso (homologyAugmentation principalSix ambient) := by
  rw [←boundaryH0Iso_augmentation]
  infer_instance

/-- The literal class of an actual singular zero-chain. -/
def boundaryZeroClass : boundaryChains.X 0 ⟶ boundaryChains.homology 0 :=
  boundaryChains.cycles₀Iso.inv ≫ boundaryChains.homologyπ 0

theorem boundaryZeroClass_augmentation : boundaryZeroClass ≫ boundaryH0Iso.hom=augmentation principalSix ambient :=
  (congrArg (fun m => boundaryZeroClass ≫ m) boundaryH0Iso_augmentation).trans
    (zeroClass_homologyAugmentation _ _)

/-- The genuine boundary H0 isomorphism sends each singleton zero-simplex of coefficient r to r. -/
theorem boundaryH0Iso_single (simplex : SingularSimplex ambient 0) (r : ℚ) :
    boundaryH0Iso.hom (boundaryZeroClass (degreeLinearEquiv ambient 0 (MonoidAlgebra.single simplex r)))=r := by
  have h := congrArg (fun f => f (degreeLinearEquiv ambient 0 (MonoidAlgebra.single simplex r)))
    boundaryZeroClass_augmentation
  refine h.trans ?_
  change augmentationModule ambient (degreeLinearEquiv ambient 0 (MonoidAlgebra.single simplex r))=r
  rw [degreeLinearEquiv_single]
  exact congrArg (fun f => f r) (generator_augmentation ambient simplex)

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
