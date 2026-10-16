module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyComparison

@[expose] public section


noncomputable section
open CategoryTheory Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial
namespace TernaryPoly.SingularCoverNaturality
open FreeActionLinearization EquivariantSingularResolution

variable {G : Type} [Group G] {E E' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x)=g • F x)

/-- The literal rational singular chain map of the given continuous map. -/
abbrev underlyingMap : underlyingChains E ⟶ underlyingChains E' :=
  ((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map F

include hF in
/-- Equivariance of the given space map is preserved by the singular-chain functor. -/
theorem underlyingMap_equivariant (g : G) :
    scalarChainMap G E g ≫ underlyingMap F=underlyingMap F ≫ scalarChainMap G E' g := by
  have h : scalarMap G E g ≫ F=F ≫ scalarMap G E' g := by
    ext x
    exact hF g x
  exact (Functor.map_comp _ _ _).symm.trans ((congrArg
    (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map) h).trans
      (Functor.map_comp _ _ _))

/-- The induced map between the actual singular chain representations. -/
def chainMap : equivariantChains G E ⟶ equivariantChains G E' where
  f n := Rep.ofHom ⟨((underlyingMap F).f n).hom,fun g =>
    congrArg (fun m => (m.f n).hom) (underlyingMap_equivariant F hF g)⟩
  comm' i j _ := by
    ext x
    exact congrArg (fun m => m.hom x) ((underlyingMap F).comm i j)

/-- Actual singular generators are sent to their postcomposition with the continuous map. -/
theorem generator_map (n : ℕ) (σ : SingularSimplex E n) :
    (TopCat.toSSet.obj E).ιChainComplex σ ≫ (underlyingMap F).f n=
      (TopCat.toSSet.obj E').ιChainComplex ((TopCat.toSSet.map F).app (.op ⦋n⦌) σ) :=
  SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map F) (ModuleCat.of ℚ ℚ) σ

/-- Every continuous map preserves the literal coefficient-sum augmentation. -/
theorem underlyingMap_augmentation :
    (underlyingMap F).f 0 ≫ augmentationModule E'=augmentationModule E := by
  apply (TopCat.toSSet.obj E).chainComplex_hom_ext
  intro σ
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ augmentationModule E') (generator_map F 0 σ)).trans
      ((generator_augmentation E' _).trans (generator_augmentation E σ).symm))

/-- The equivariant singular map preserves the actual augmentation in degree zero. -/
theorem chainMap_augmentation : (chainMap F hF).f 0 ≫ augmentation G E'=augmentation G E := by
  ext x
  exact congrArg (fun m => m.hom x) (underlyingMap_augmentation F)

/-- The actual singular map commutes with the complete augmented chain maps. -/
theorem chainMap_augmentationChain :
    chainMap F hF ≫ augmentationChain G E'=augmentationChain G E := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (chainMap F hF).f 0 ≫ (augmentationChain G E').f 0=(augmentationChain G E).f 0
  simp only [augmentationChain_f_zero]
  exact chainMap_augmentation F hF

/-- The induced pullback of actual equivariant singular Hom cochains. -/
def cochainPullback (V : Rep ℚ G) :
    EquivariantSingularCohomology.cochains G E' V ⟶
      EquivariantSingularCohomology.cochains G E V :=
  (unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    ((((linearYoneda ℚ (Rep ℚ G)).obj V).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map (chainMap F hF)).op

@[simp] theorem cochainPullback_apply (V : Rep ℚ G) (n : ℕ) (c : chainRep G E' n ⟶ V) :
    (cochainPullback F hF V).f n c=(chainMap F hF).f n ≫ c := rfl

end TernaryPoly.SingularCoverNaturality
