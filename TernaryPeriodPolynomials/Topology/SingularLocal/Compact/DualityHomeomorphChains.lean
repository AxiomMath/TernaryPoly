module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityCoverHomeomorph
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphMaps

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory HomologicalComplex
open SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality SingularLocalSupport
variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  {p : E ⟶ B} {p' : E' ⟶ B'}
  [hp : Fact (IsQuotientCoveringMap p G)] [hp' : Fact (IsQuotientCoveringMap p' G)]
  (h : CoverHomeomorph (G := G) p p') (V : Rep.{0} ℚ G)
variable [IsCancelSMul G E] [IsCancelSMul G E']

/-- The literal geometric local-chain map of an equivariant covering homeomorphism. -/
def coveringChainMap : localChains p hp.out V ⟶ localChains p' hp'.out V :=
  localSpaceMap (TopCat.isoOfHomeo h.total).hom h.equivariant V p p' hp.out hp'.out

/-- Actual geometric chain pushforward by the covering homeomorphism is invertible. -/
theorem coveringChainMap_isIso : IsIso (coveringChainMap h V) := by
  have hi : IsIso (SingularCoverNaturality.chainMap (TopCat.isoOfHomeo h.total).hom h.equivariant) := by
    refine ⟨SingularCoverNaturality.chainMap (TopCat.isoOfHomeo h.total).inv h.symm.equivariant,?_,?_⟩
    · erw [← SingularCoverNaturality.chainMap_comp]
      simpa only [Iso.hom_inv_id] using (SingularCoverNaturality.chainMap_id (G := G) (E := E))
    · erw [← SingularCoverNaturality.chainMap_comp]
      simpa only [Iso.inv_hom_id] using (SingularCoverNaturality.chainMap_id (G := G) (E := E'))
  unfold coveringChainMap localSpaceMap coinvariantSpaceMap
  infer_instance

/-- Actual covering-local homology is preserved, with its literal geometric forward map. -/
def coveringHomologyIso (b : ℕ) : (localChains p hp.out V).homology b ≅
    (localChains p' hp'.out V).homology b := by
  have := coveringChainMap_isIso h V
  exact (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) b).mapIso (asIso (coveringChainMap h V))

end TernaryPoly.SingularLocalCompactDuality
