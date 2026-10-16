module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyComparison

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicTopology HomologicalComplex
namespace TernaryPoly.EquivariantSingularCohomology
open EquivariantSingularResolution

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]

/-- Literal coefficient postcomposition on a general representation Hom cochain complex. -/
def homCoefficientMap (K : ChainComplex (Rep ℚ G) ℕ) {V W : Rep ℚ G} (φ : V ⟶ W) :
    K.linearYonedaObj ℚ V ⟶ K.linearYonedaObj ℚ W :=
  (unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    ((NatTrans.mapHomologicalComplex (((linearYoneda ℚ (Rep ℚ G)).map φ).rightOp)
      (ComplexShape.down ℕ)).app K).op

@[simp] theorem homCoefficientMap_apply (K : ChainComplex (Rep ℚ G) ℕ)
    {V W : Rep ℚ G} (φ : V ⟶ W) (n : ℕ) (f : K.X n ⟶ V) :
    (homCoefficientMap G K φ).f n f=f ≫ φ := rfl

/-- The coefficient maps agree with literal pointwise postcomposition on inhomogeneous cochains. -/
theorem inhomogeneousIso_natural {V W : Rep ℚ G} (φ : V ⟶ W) :
    groupCohomology.cochainsMap (MonoidHom.id G) φ ≫
      (groupCohomology.inhomogeneousCochainsIso W).hom=
    (groupCohomology.inhomogeneousCochainsIso V).hom ≫
      homCoefficientMap G (Rep.barComplex ℚ G) φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Rep.free_ext
  intro i
  change (Representation.freeLift W.ρ (fun a => φ.hom (f a)))
      (Finsupp.single i (MonoidAlgebra.single 1 1))=
    φ.hom ((Representation.freeLift V.ρ f) (Finsupp.single i (MonoidAlgebra.single 1 1)))
  simp only [Representation.freeLift_single_single, map_one, Module.End.one_apply, one_smul]

variable [ContractibleSpace X] [IsCancelSMul G X]

/-- The bar-to-singular cochain comparison commutes with coefficient morphisms. -/
theorem barComparison_natural {V W : Rep ℚ G} (φ : V ⟶ W) :
    homCoefficientMap G (Rep.barComplex ℚ G) φ ≫ barComparison G X W=
      barComparison G X V ≫ cochainMap G X φ := by
  ext n f
  rfl

/-- The actual quasi-isomorphism from group cochains is natural in the coefficients. -/
theorem comparisonMap_natural {V W : Rep ℚ G} (φ : V ⟶ W) :
    groupCohomology.cochainsMap (MonoidHom.id G) φ ≫ comparisonMap G X W=
      comparisonMap G X V ≫ cochainMap G X φ := by
  dsimp only [comparisonMap]
  rw [←Category.assoc,inhomogeneousIso_natural,Category.assoc,barComparison_natural,
    ←Category.assoc]

/-- The bar-comparison cohomology isomorphism is natural for actual coefficient maps. -/
theorem groupCohomologyIso_natural {V W : Rep ℚ G} (φ : V ⟶ W) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) φ n ≫ (groupCohomologyIso G X W n).hom=
      (groupCohomologyIso G X V n).hom ≫ homologyMap (cochainMap G X φ) n := by
  change homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) φ) n ≫
      homologyMap (comparisonMap G X W) n=
    homologyMap (comparisonMap G X V) n ≫ homologyMap (cochainMap G X φ) n
  rw [←homologyMap_comp,←homologyMap_comp,comparisonMap_natural]

end TernaryPoly.EquivariantSingularCohomology
