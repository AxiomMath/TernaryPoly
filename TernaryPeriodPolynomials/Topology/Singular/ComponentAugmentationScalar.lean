module

public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationTopology
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionProjective
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionAugmentation

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularComponentAugmentation
open Topology CategoryTheory Limits AlgebraicTopology EquivariantSingularResolution
open scoped MonoidAlgebra Simplicial

/-- The actual constant coproduct is the usual finitely-supported module. -/
def coproductFinsuppIso (κ : Type) :
    (∐ fun _ : κ => ModuleCat.of ℚ ℚ) ≅ ModuleCat.of ℚ (κ →₀ ℚ) :=
  (coproductIsCoproduct (fun _ : κ => ModuleCat.of ℚ ℚ)).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℚ ℚ κ)

theorem coproductFinsuppIso_single (κ : Type) (i : κ) :
    Sigma.ι (fun _ : κ => ModuleCat.of ℚ ℚ) i ≫ (coproductFinsuppIso κ).hom =
      ModuleCat.ofHom (Finsupp.lsingle i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun _ : κ => ModuleCat.of ℚ ℚ))
    (ModuleCat.finsuppCoconeIsColimit ℚ ℚ κ) ⟨i⟩

variable {ι : Type} (E : ι → Type) [∀ i,TopologicalSpace (E i)]
  [∀ i,ContractibleSpace (E i)] [TopologicalSpace ι] [DiscreteTopology ι]

abbrev SingularComponents := SSet.π₀ (TopCat.toSSet.obj (TopCat.of (Total E)))

def componentModuleIso :
    (∐ fun _ : SingularComponents E => ModuleCat.of ℚ ℚ) ≅ ModuleCat.of ℚ ℚ[ι] :=
  coproductFinsuppIso (SingularComponents E) ≪≫
    ((Finsupp.domLCongr (R := ℚ) (M := ℚ) (singularComponentEquiv E)).trans
      (MonoidAlgebra.coeffLinearEquiv ℚ).symm).toModuleIso

theorem componentModuleIso_single (i : SingularComponents E) :
    Sigma.ι (fun _ : SingularComponents E => ModuleCat.of ℚ ℚ) i ≫ (componentModuleIso E).hom =
      ModuleCat.ofHom (MonoidAlgebra.lsingle (singularComponentEquiv E i)) := by
  change Sigma.ι _ i ≫ (coproductFinsuppIso _).hom ≫ _ = _
  rw [←Category.assoc,coproductFinsuppIso_single]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (MonoidAlgebra.coeffLinearEquiv ℚ).symm
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) (singularComponentEquiv E) (Finsupp.single i r))=_
  rw [Finsupp.domLCongr_single]
  rfl

/-- The augmentation of actual zero chains records the single component label. -/
def scalarAugmentation : (underlyingChains (TopCat.of (Total E))).X 0 ⟶ ModuleCat.of ℚ ℚ[ι] :=
  SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj (TopCat.of (Total E))) (ModuleCat.of ℚ ℚ) ≫
    (componentModuleIso E).hom

theorem generator_scalarAugmentation
    (simplex : FreeActionLinearization.SingularSimplex (TopCat.of (Total E)) 0) :
    (TopCat.toSSet.obj (TopCat.of (Total E))).ιChainComplex simplex ≫ scalarAugmentation E =
      ModuleCat.ofHom (MonoidAlgebra.lsingle (TopCat.toSSetObj₀Equiv simplex).1) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (componentModuleIso E).hom)
      (SSet.π₀.comp_fromChainComplexXZero (TopCat.toSSet.obj (TopCat.of (Total E)))
        (ModuleCat.of ℚ ℚ) simplex)).trans (componentModuleIso_single E (SSet.π₀.mk simplex)))

theorem scalarAugmentation_single
    (simplex : FreeActionLinearization.SingularSimplex (TopCat.of (Total E)) 0) (r : ℚ) :
    scalarAugmentation E (degreeLinearEquiv (TopCat.of (Total E)) 0 (MonoidAlgebra.single simplex r))=
      MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r := by
  rw [degreeLinearEquiv_single]
  exact congrArg (fun f => f r) (generator_scalarAugmentation E simplex)

theorem d_scalarAugmentation :
    (underlyingChains (TopCat.of (Total E))).d 1 0 ≫ scalarAugmentation E=0 := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (componentModuleIso E).hom)
      (SSet.π₀.d_fromChainComplexXZero (TopCat.toSSet.obj (TopCat.of (Total E)))
        (ModuleCat.of ℚ ℚ) 1)).trans zero_comp)

/-- This particular literal label augmentation is a cokernel of the actual first boundary. -/
def scalarAugmentationIsCokernel :
    IsColimit (CokernelCofork.ofπ (scalarAugmentation E) (d_scalarAugmentation E)) :=
  (SSet.isColimitCokernelCoforkChainComplexDOneZero
    (TopCat.toSSet.obj (TopCat.of (Total E))) (ModuleCat.of ℚ ℚ)).ofIsoColimit
      (Cofork.ext (componentModuleIso E) rfl)

theorem scalar_augmented_exact : (ShortComplex.mk _ _ (d_scalarAugmentation E)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (scalarAugmentationIsCokernel E)

instance scalarAugmentation_epi : Epi (scalarAugmentation E) :=
  epi_of_isColimit_cofork (scalarAugmentationIsCokernel E)

theorem scalar_exactAt (n : ℕ) (hn : n≠0) :
    (underlyingChains (TopCat.of (Total E))).ExactAt n :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (positive_homology_isZero E n hn)

/-- The actual H0 module is isomorphic to the literal label module. -/
def scalarHomologyZeroIso : (underlyingChains (TopCat.of (Total E))).homology 0 ≅ ModuleCat.of ℚ ℚ[ι] :=
  (TopCat.toSSet.obj (TopCat.of (Total E))).homology₀Iso (ModuleCat.of ℚ ℚ) ≪≫ componentModuleIso E

theorem generator_scalarHomologyZeroIso
    (simplex : FreeActionLinearization.SingularSimplex (TopCat.of (Total E)) 0) :
    ((TopCat.toSSet.obj (TopCat.of (Total E))).chainComplex (ModuleCat.of ℚ ℚ)).liftCycles
      ((TopCat.toSSet.obj (TopCat.of (Total E))).ιChainComplex simplex) 0 (by simp) (by simp) ≫
      ((TopCat.toSSet.obj (TopCat.of (Total E))).chainComplex (ModuleCat.of ℚ ℚ)).homologyπ 0 ≫ (scalarHomologyZeroIso E).hom =
        ModuleCat.ofHom (MonoidAlgebra.lsingle (TopCat.toSSetObj₀Equiv simplex).1) := by
  have h := congrArg (fun f => f ≫ (componentModuleIso E).hom)
    (SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
      (TopCat.toSSet.obj (TopCat.of (Total E))) (ModuleCat.of ℚ ℚ) simplex)
  have h' := h.trans (componentModuleIso_single E (SSet.π₀.mk simplex))
  change _ ≫ _ ≫ (((TopCat.toSSet.obj (TopCat.of (Total E))).homology₀Iso
    (ModuleCat.of ℚ ℚ)).hom ≫ (componentModuleIso E).hom) = _
  simpa only [Category.assoc,singularComponentEquiv_mk] using h'

end TernaryPoly.SingularComponentAugmentation
