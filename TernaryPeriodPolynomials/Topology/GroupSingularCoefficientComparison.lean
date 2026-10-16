module

public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientComplex
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyNaturality

@[expose] public section


noncomputable section
open CategoryTheory HomologicalComplex
namespace TernaryPoly.SingularLocalCoefficient

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) [ContractibleSpace E] [IsCancelSMul G E]

/-- Group cohomology agrees with the actual transported-face local-coefficient singular cohomology. -/
def groupLocalCohomologyIso (V : Rep.{0} ℚ G) (n : ℕ) :
    groupCohomology V n ≅ (localCochains p hp V).homology n :=
  EquivariantSingularCohomology.groupCohomologyIso G E V n ≪≫
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso (cochainIso p hp V)

/-- The comparison is induced by the actual group-to-singular map and the actual fiber-cochain map. -/
theorem groupLocalCohomologyIso_hom (V : Rep.{0} ℚ G) (n : ℕ) :
    (groupLocalCohomologyIso p hp V n).hom=
      homologyMap (EquivariantSingularCohomology.comparisonMap G E V ≫ (cochainIso p hp V).hom) n := by
  exact (homologyMap_comp _ _ n).symm

end TernaryPoly.SingularLocalCoefficient
