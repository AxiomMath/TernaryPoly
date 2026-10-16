module

public import TernaryPeriodPolynomials.Topology.Singular.ComponentAugmentationHomology
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityChains

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularComponentAugmentation
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution FreeActionLinearization
open scoped MonoidAlgebra Simplicial

variable {ι κ G : Type} [Group G] [MulAction G ι] [MulAction G κ]

def permutationMap (u : ι → κ) (hu : ∀ (g : G) i,u (g • i)=g • u i) :
    Rep.ofMulAction ℚ G ι ⟶ Rep.ofMulAction ℚ G κ :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap ℚ ℚ u,fun g => by
    apply MonoidAlgebra.lhom_ext'
    intro i
    apply LinearMap.ext
    intro r
    change MonoidAlgebra.mapDomainLinearMap ℚ ℚ u
      (Representation.ofMulAction ℚ G ι g (MonoidAlgebra.single i r))=
        Representation.ofMulAction ℚ G κ g
          (MonoidAlgebra.mapDomainLinearMap ℚ ℚ u (MonoidAlgebra.single i r))
    rw [Representation.ofMulAction_single,MonoidAlgebra.mapDomainLinearMap_single,
      MonoidAlgebra.mapDomainLinearMap_single,Representation.ofMulAction_single,hu]⟩

@[simp] theorem permutationMap_single (u : ι → κ) (hu : ∀ (g : G) i,u (g • i)=g • u i)
    (i : ι) (r : ℚ) : permutationMap u hu (MonoidAlgebra.single i r)=MonoidAlgebra.single (u i) r :=
  MonoidAlgebra.mapDomainLinearMap_single u r i

variable (E : ι → Type) (F : κ → Type) [∀ i,TopologicalSpace (E i)] [∀ j,TopologicalSpace (F j)]
  [∀ i,ContractibleSpace (E i)] [∀ j,ContractibleSpace (F j)]
  [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace κ] [DiscreteTopology κ]
  [MulAction G (Total E)] [MulAction G (Total F)]
  [ContinuousConstSMul G (Total E)] [ContinuousConstSMul G (Total F)]
  (hE : ∀ (g : G) (x : Total E),(g • x).1=g • x.1)
  (hF : ∀ (g : G) (x : Total F),(g • x).1=g • x.1)
  (u : ι → κ) (hu : ∀ (g : G) i,u (g • i)=g • u i)
  (f : TopCat.of (Total E) ⟶ TopCat.of (Total F))
  (hf : ∀ (g : G) (x : Total E),f (g • x)=g • f x)
  (hcomp : ∀ x : Total E,(f x).1=u x.1)

include hcomp in
omit [∀ i,ContractibleSpace (E i)] [∀ j,ContractibleSpace (F j)]
  [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace κ] [DiscreteTopology κ] in
theorem zeroLabel_map (simplex : SingularSimplex (TopCat.of (Total E)) 0) :
    (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map f).app (.op ⦋0⦌) simplex)).1=
      u (TopCat.toSSetObj₀Equiv simplex).1 := hcomp (TopCat.toSSetObj₀Equiv simplex)

include hcomp in
/-- A continuous map over labels commutes with the actual scalar component augmentation. -/
theorem scalarAugmentation_natural :
    (SingularCoverNaturality.underlyingMap f).f 0 ≫ scalarAugmentation F =
      scalarAugmentation E ≫ ModuleCat.ofHom (MonoidAlgebra.mapDomainLinearMap ℚ ℚ u) := by
  apply (TopCat.toSSet.obj (TopCat.of (Total E))).chainComplex_hom_ext
  intro simplex
  have ha := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ scalarAugmentation F)
      (SingularCoverNaturality.generator_map f 0 simplex)).trans
      (generator_scalarAugmentation F _))
  have hs : ModuleCat.ofHom (MonoidAlgebra.lsingle (TopCat.toSSetObj₀Equiv simplex).1) ≫
      ModuleCat.ofHom (MonoidAlgebra.mapDomainLinearMap ℚ ℚ u) =
        ModuleCat.ofHom (MonoidAlgebra.lsingle (u (TopCat.toSSetObj₀Equiv simplex).1)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact MonoidAlgebra.mapDomainLinearMap_single u r _
  have hb := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ ModuleCat.ofHom (MonoidAlgebra.mapDomainLinearMap ℚ ℚ u))
      (generator_scalarAugmentation E simplex)).trans hs)
  exact ha.trans ((congrArg (fun i : κ => ModuleCat.ofHom (MonoidAlgebra.lsingle (R := ℚ) (S := ℚ) i))
    (zeroLabel_map E F u f hcomp simplex)).trans hb.symm)

include hcomp in
/-- The actual equivariant singular map lies over the literal permutation map of labels. -/
theorem augmentation_natural :
    (SingularCoverNaturality.chainMap f hf).f 0 ≫ augmentation F G hF =
      augmentation E G hE ≫ permutationMap u hu := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact congrArg ModuleCat.Hom.hom (scalarAugmentation_natural E F u f hcomp)

include hcomp in
theorem augmentationChain_natural :
    SingularCoverNaturality.chainMap f hf ≫ augmentationChain F G hF =
      augmentationChain E G hE ≫ (ChainComplex.single₀ (Rep ℚ G)).map (permutationMap u hu) := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (SingularCoverNaturality.chainMap f hf).f 0 ≫ (augmentationChain F G hF).f 0=
    (augmentationChain E G hE).f 0 ≫ permutationMap u hu
  rw [augmentationChain_f_zero,augmentationChain_f_zero]
  exact augmentation_natural E F hE hF u hu f hf hcomp

include hcomp in
/-- The induced H0 map is exactly the literal permutation map on component labels. -/
theorem homologyZeroIso_natural :
    homologyMap (SingularCoverNaturality.chainMap f hf) 0 ≫ (homologyZeroIso F G hF).hom =
      (homologyZeroIso E G hE).hom ≫ permutationMap u hu := by
  have h := congrArg (fun m => homologyMap m 0)
    (augmentationChain_natural E F hE hF u hu f hf hcomp)
  rw [homologyMap_comp,homologyMap_comp] at h
  change homologyMap (SingularCoverNaturality.chainMap f hf) 0 ≫
      (homologyMap (augmentationChain F G hF) 0 ≫
        (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (Rep.ofMulAction ℚ G κ)).hom) =
    (homologyMap (augmentationChain E G hE) 0 ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (Rep.ofMulAction ℚ G ι)).hom) ≫ _
  rw [←Category.assoc,h,Category.assoc,singleObjHomologySelfIso_hom_naturality,←Category.assoc]

end TernaryPoly.SingularComponentAugmentation
