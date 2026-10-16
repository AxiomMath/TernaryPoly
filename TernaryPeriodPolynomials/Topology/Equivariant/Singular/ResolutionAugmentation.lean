module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionChains
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero

@[expose] public section


noncomputable section
open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial
namespace TernaryPoly.EquivariantSingularResolution
open FreeActionLinearization

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]

/-- The literal coefficient-sum augmentation on the actual singular zero-chains. -/
def augmentationModule : (underlyingChains X).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  Sigma.desc (fun _ : SingularSimplex X 0 => 𝟙 (ModuleCat.of ℚ ℚ))

@[simp] theorem generator_augmentation (σ : SingularSimplex X 0) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ augmentationModule X=𝟙 (ModuleCat.of ℚ ℚ) :=
  Sigma.ι_comp_desc _ _

/-- The literal coefficient sum agrees with the standard component augmentation. -/
theorem augmentationModule_eq_components : augmentationModule X=
    SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) ≫
      Sigma.desc (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => 𝟙 (ModuleCat.of ℚ ℚ)) := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  have h := congrArg (fun f => f ≫
    Sigma.desc (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => 𝟙 (ModuleCat.of ℚ ℚ)))
    (SSet.π₀.comp_fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) σ)
  exact (generator_augmentation X σ).trans
    ((Category.assoc _ _ _).symm.trans (h.trans (Sigma.ι_comp_desc _ _))).symm

/-- The alternating boundary has coefficient sum zero. -/
theorem d_augmentation : (underlyingChains X).d 1 0 ≫ augmentationModule X=0 := by
  have h := congrArg (fun f => f ≫
    Sigma.desc (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => 𝟙 (ModuleCat.of ℚ ℚ)))
    (SSet.π₀.d_fromChainComplexXZero (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) 1)
  exact (congrArg (fun f => (underlyingChains X).d 1 0 ≫ f)
    (augmentationModule_eq_components X)).trans
    ((Category.assoc _ _ _).symm.trans (h.trans zero_comp))

/-- The actual scalar chain maps preserve the coefficient sum. -/
theorem scalarChainMap_augmentation (g : G) :
    (scalarChainMap G X g).f 0 ≫ augmentationModule X=augmentationModule X := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  have h := congrArg (fun f => f ≫ augmentationModule X) (generator_smul G X 0 σ g)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((generator_augmentation X (g • σ)).trans (generator_augmentation X σ).symm))

/-- The coefficient-sum augmentation is genuinely equivariant to the trivial representation. -/
def augmentation : chainRep G X 0 ⟶ Rep.trivial ℚ G ℚ :=
  Rep.ofHom ⟨(augmentationModule X).hom,fun g =>
    congrArg ModuleCat.Hom.hom (scalarChainMap_augmentation G X g)⟩

/-- The actual equivariant boundary is killed by the coefficient-sum augmentation. -/
theorem equivariantD_augmentation : equivariantD G X 1 0 ≫ augmentation G X=0 := by
  ext x
  exact congrArg (fun u => u x) (d_augmentation X)

/-- The actual augmented chain map to the trivial module in degree zero. -/
def augmentationChain : equivariantChains G X ⟶
    (ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation G X,equivariantD_augmentation G X⟩

@[simp] theorem augmentationChain_f_zero : (augmentationChain G X).f 0=augmentation G X :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Forgetting the augmentation recovers the exact coefficient-sum map. -/
theorem forget_augmentation :
    (forget₂ (Rep ℚ G) (ModuleCat ℚ)).map (augmentation G X)=augmentationModule X := rfl

end TernaryPoly.EquivariantSingularResolution
