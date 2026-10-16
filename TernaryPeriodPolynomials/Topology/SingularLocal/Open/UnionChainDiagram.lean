module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionChainCarriers

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (U : ℕ → Opens B) (hU : Monotone U)

/-- The actual local-chain inclusion of a restricted cover in itself is the identity. -/
theorem nestedLocalInclusion_self (A : Set B) : nestedLocalInclusion p A A Set.Subset.rfl V = 𝟙 _ := by
  apply (cancel_mono (localInclusion p A V)).mp
  rw [nestedLocalInclusion_inclusion,Category.id_comp]

/-- The chain diagram of an increasing open cover uses literal localSpaceMap inclusions
between the actual restricted quotient covers. -/
def chainDiagram : ℕ ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ where
  obj i := restrictedLocalChains p (U i) V
  map f := nestedLocalInclusion p (U _) (U _) (hU (leOfHom f)) V
  map_id i := nestedLocalInclusion_self p V (U i)
  map_comp f g := (nestedLocalInclusion_comp p _ _ _ (hU (leOfHom f)) (hU (leOfHom g)) V).symm

/-- Ordinary local homology over an increasing open cover, with actual inclusion maps. -/
def homologyDiagram (b : ℕ) : ℕ ⥤ ModuleCat.{0} ℚ :=
  chainDiagram p V U hU ⋙ homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) b

/-- Actual ambient local-chain inclusions induce the genuine homology cocone. -/
def homologyCocone (b : ℕ) : Cocone (homologyDiagram p V U hU b) where
  pt := (localChains p hp.out V).homology b
  ι := {
    app := fun i => homologyMap (localInclusion p (U i) V) b
    naturality := fun i j f => by
      change homologyMap (nestedLocalInclusion p (U i) (U j) (hU (leOfHom f)) V) b ≫
        homologyMap (localInclusion p (U j) V) b = homologyMap (localInclusion p (U i) V) b ≫ 𝟙 _
      rw [← homologyMap_comp,Category.comp_id]
      exact congrArg (fun f => homologyMap f b)
        (nestedLocalInclusion_inclusion p (U i) (U j) (hU (leOfHom f)) V) }

/-- The canonical map from the increasing-open homology colimit to actual ambient local homology. -/
def homologyColimitMap (b : ℕ) : colimit (homologyDiagram p V U hU b) ⟶
    (localChains p hp.out V).homology b := colimit.desc _ (homologyCocone p V U hU b)

/-- On every stage the canonical comparison is precisely the actual local-chain inclusion on homology. -/
theorem homologyColimitMap_ι (b i : ℕ) :
    colimit.ι (homologyDiagram p V U hU b) i ≫ homologyColimitMap p V U hU b =
      homologyMap (localInclusion p (U i) V) b := colimit.ι_desc _ _

end TernaryPoly.SingularLocalOpenUnion
