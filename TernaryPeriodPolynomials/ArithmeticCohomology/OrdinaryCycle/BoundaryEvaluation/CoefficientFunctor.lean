module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.SectorInduction

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex EquivariantSingularResolution SingularLocalHomology

variable {G : Type} [Group G]

/-- Actual singular tensor-coinvariant chains form an additive coefficient functor. -/
def singularCoinvariantCoefficientFunctor (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E] :
    Rep.{0} ℚ G ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ where
  obj V := coinvariantChains G E V
  map φ := coinvariantCoefficientMap φ
  map_id V := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (((Rep.coinvariantsTensor ℚ G).map (𝟙 V)).app (chainRep G E n)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (((Rep.coinvariantsTensor ℚ G).map (φ ≫ ψ)).app (chainRep G E n)) = _
    rw [Functor.map_comp]
    rfl

instance singularCoinvariantCoefficientFunctor_additive (E : TopCat.{0})
    [MulAction G E] [ContinuousConstSMul G E] :
    (singularCoinvariantCoefficientFunctor (G := G) E).Additive where
  map_add := by
    intro V W φ ψ
    apply HomologicalComplex.Hom.ext
    funext n
    change (((Rep.coinvariantsTensor ℚ G).map (φ + ψ)).app (chainRep G E n)) = _
    rw [Functor.map_add]
    rfl

variable {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)

/-- The literal local-chain coefficient morphisms satisfy composition. -/
theorem actualLocalCoefficientMap_comp {U V W : Rep.{0} ℚ G} (φ : U ⟶ V) (ψ : V ⟶ W) :
    localCoefficientMap p hp (φ ≫ ψ) = localCoefficientMap p hp φ ≫ localCoefficientMap p hp ψ := by
  have hc := (singularCoinvariantCoefficientFunctor (G := G) E).map_comp φ ψ
  change coinvariantCoefficientMap (E := E) (φ ≫ ψ) =
    coinvariantCoefficientMap (E := E) φ ≫ coinvariantCoefficientMap (E := E) ψ at hc
  unfold localCoefficientMap
  rw [hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The geometric local-chain coefficient functor uses exactly the localCoefficientMap. -/
def singularLocalCoefficientFunctor : Rep.{0} ℚ G ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ where
  obj V := localChains p hp V
  map φ := localCoefficientMap p hp φ
  map_id V := by
    have hc := (singularCoinvariantCoefficientFunctor (G := G) E).map_id V
    change coinvariantCoefficientMap (E := E) (𝟙 V) = 𝟙 _ at hc
    unfold localCoefficientMap
    rw [hc, Category.id_comp, Iso.inv_hom_id]
  map_comp φ ψ := actualLocalCoefficientMap_comp p hp φ ψ

instance singularLocalCoefficientFunctor_additive : (singularLocalCoefficientFunctor p hp).Additive where
  map_add := by
    intro V W φ ψ
    have hc := (singularCoinvariantCoefficientFunctor (G := G) E).map_add (f := φ) (g := ψ)
    change coinvariantCoefficientMap (E := E) (φ + ψ) =
      coinvariantCoefficientMap (E := E) φ + coinvariantCoefficientMap (E := E) ψ at hc
    change localCoefficientMap p hp (φ + ψ) = localCoefficientMap p hp φ + localCoefficientMap p hp ψ
    unfold localCoefficientMap
    rw [hc, Preadditive.add_comp, Preadditive.comp_add]

variable {E' B' : TopCat.{0}} [MulAction G E'] [ContinuousConstSMul G E'] [IsCancelSMul G E']
  (p' : E' ⟶ B') (hp' : IsQuotientCoveringMap p' G)
  (F : E ⟶ E') (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)

omit [IsCancelSMul G E] [IsCancelSMul G E'] in
/-- Covariant actual singular space maps commute with actual coefficient morphisms. -/
theorem actualCoinvariantSpaceMap_coefficient_natural {V W : Rep.{0} ℚ G} (φ : V ⟶ W) :
    coinvariantCoefficientMap (E := E) φ ≫ coinvariantSpaceMap F hF W =
      coinvariantSpaceMap F hF V ≫ coinvariantCoefficientMap (E := E') φ := by
  exact (((Rep.coinvariantsTensor ℚ G).map φ).mapHomologicalComplex
    (ComplexShape.down ℕ)).naturality (SingularCoverNaturality.chainMap F hF) |>.symm

/-- The actual geometric space map is coefficient-natural under the actual singular comparison. -/
theorem actualLocalSpaceMap_coefficient_natural {V W : Rep.{0} ℚ G} (φ : V ⟶ W) :
    localCoefficientMap p hp φ ≫ localSpaceMap F hF W p p' hp hp' =
      localSpaceMap F hF V p p' hp hp' ≫ localCoefficientMap p' hp' φ := by
  unfold localCoefficientMap localSpaceMap
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (coinvariantCoefficientMap (E := E) φ),
    actualCoinvariantSpaceMap_coefficient_natural F hF φ, Category.assoc]

/-- Actual equivariant maps of spaces induce a natural transformation on geometric coefficient chains. -/
def actualLocalSpaceCoefficientNat : singularLocalCoefficientFunctor p hp ⟶ singularLocalCoefficientFunctor p' hp' where
  app V := localSpaceMap F hF V p p' hp hp'
  naturality := by
    intro V W φ
    exact actualLocalSpaceMap_coefficient_natural p hp p' hp' F hF φ

end TernaryPoly.OrdinaryBoundaryActualEvaluation
