module

public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationEquivariant

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularComponentAugmentation
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution FreeActionLinearization
open scoped MonoidAlgebra

theorem zeroClass_augmentation {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    (K : ChainComplex C ℕ) [K.HasHomology 0] (A : C)
    (f : K ⟶ (ChainComplex.single₀ C).obj A) :
    K.cycles₀Iso.inv ≫ K.homologyπ 0 ≫ homologyMap f 0 ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 A).hom =
        f.f 0 ≫ (singleObjXSelf (ComplexShape.down ℕ) 0 A).hom := by
  rw [homologyπ_naturality_assoc,homologyπ_singleObjHomologySelfIso_hom,singleObjCyclesSelfIso_hom]
  rw [cyclesMap_i_assoc]
  rw [←Category.assoc,ChainComplex.cycles₀Iso,HomologicalComplex.iCyclesIso_inv_hom_id,Category.id_comp]

variable {ι : Type} (E : ι → Type) [∀ i,TopologicalSpace (E i)]
  [∀ i,ContractibleSpace (E i)] [TopologicalSpace ι] [DiscreteTopology ι]
variable (G : Type) [Group G] [MulAction G ι] [MulAction G (Total E)]
  [ContinuousConstSMul G (Total E)]
  (hlabel : ∀ (g : G) (x : Total E),(g • x).1=g • x.1)

/-- The literal class map from all zero chains to H0. -/
def zeroClassMap : (equivariantChains G (TopCat.of (Total E))).X 0 ⟶
    (equivariantChains G (TopCat.of (Total E))).homology 0 :=
  (equivariantChains G (TopCat.of (Total E))).cycles₀Iso.inv ≫
    (equivariantChains G (TopCat.of (Total E))).homologyπ 0

/-- The H0 identification is induced by exactly the chain augmentation. -/
theorem zeroClassMap_homologyZeroIso :
    zeroClassMap E G ≫ (homologyZeroIso E G hlabel).hom=augmentation E G hlabel := by
  have h := zeroClass_augmentation (equivariantChains G (TopCat.of (Total E)))
    (Rep.ofMulAction ℚ G ι) (augmentationChain E G hlabel)
  exact (Category.assoc _ _ _).trans h

/-- The exact singleton H0 formula in the actual equivariant homology representation. -/
theorem homologyZeroIso_single
    (simplex : SingularSimplex (TopCat.of (Total E)) 0) (r : ℚ) :
    (homologyZeroIso E G hlabel).hom
      (zeroClassMap E G (degreeLinearEquiv (TopCat.of (Total E)) 0 (MonoidAlgebra.single simplex r)))=
        MonoidAlgebra.single (TopCat.toSSetObj₀Equiv simplex).1 r := by
  have h := congrArg (fun f => f
    (degreeLinearEquiv (TopCat.of (Total E)) 0 (MonoidAlgebra.single simplex r)))
      (zeroClassMap_homologyZeroIso E G hlabel)
  exact h.trans (augmentation_single E G hlabel simplex r)

omit [∀ i,ContractibleSpace (E i)] [TopologicalSpace ι] [DiscreteTopology ι] [MulAction G ι] in
/-- The concrete H0 class map is equivariant, as a genuine representation morphism. -/
theorem zeroClassMap_equivariant (g : G) (c : chainRep G (TopCat.of (Total E)) 0) :
    zeroClassMap E G ((chainRep G (TopCat.of (Total E)) 0).ρ g c)=
      ((equivariantChains G (TopCat.of (Total E))).homology 0).ρ g (zeroClassMap E G c) :=
  Rep.hom_comm_apply _ g c

end TernaryPoly.SingularComponentAugmentation
