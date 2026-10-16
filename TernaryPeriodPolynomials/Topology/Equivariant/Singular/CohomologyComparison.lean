module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyComplex
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionExactness
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section


noncomputable section
open CategoryTheory Limits AlgebraicTopology HomologicalComplex
namespace TernaryPoly.EquivariantSingularCohomology
open EquivariantSingularResolution

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]
  [ContractibleSpace X] [IsCancelSMul G X]

/-- The actual singular Hom complex computes group cohomology, by the resolution and Ext. -/
def cohomologyIsoViaExt (V : Rep ℚ G) (n : ℕ) :
    (cochains G X V).homology n ≅ groupCohomology V n :=
  (groupCohomologyIso V n (projectiveResolution G X)).symm

/-- An actual augmentation-compatible comparison from the singular to the bar resolution. -/
def resolutionComparison : equivariantChains G X ⟶ Rep.barComplex ℚ G :=
  ((projectiveResolution G X).homotopyEquiv (Rep.barResolution ℚ G)).hom

/-- Precomposition by the actual resolution comparison gives a map of Hom cochain complexes. -/
def barComparison (V : Rep ℚ G) :
    (Rep.barComplex ℚ G).linearYonedaObj ℚ V ⟶ cochains G X V :=
  (unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    ((((linearYoneda ℚ (Rep ℚ G)).obj V).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map (resolutionComparison G X)).op

@[simp] theorem barComparison_apply (V : Rep ℚ G) (n : ℕ)
    (f : (Rep.barComplex ℚ G).X n ⟶ V) :
    (barComparison G X V).f n f=(resolutionComparison G X).f n ≫ f := rfl

/-- The map on Hom cochains is a genuine quasi-isomorphism, by the resolution homotopy equivalence. -/
instance barComparison_quasiIso (V : Rep ℚ G) : QuasiIso (barComparison G X V) := by
  let e := ((linearYoneda ℚ (Rep ℚ G)).obj V).rightOp.mapHomotopyEquiv
    ((projectiveResolution G X).homotopyEquiv (Rep.barResolution ℚ G))
  exact inferInstanceAs (QuasiIso ((unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map e.hom.op))

/-- The actual inhomogeneous group cochains map quasi-isomorphically to singular Hom cochains. -/
def comparisonMap (V : Rep ℚ G) :
    groupCohomology.inhomogeneousCochains V ⟶ cochains G X V :=
  (groupCohomology.inhomogeneousCochainsIso V).hom ≫ barComparison G X V

instance comparisonMap_quasiIso (V : Rep ℚ G) : QuasiIso (comparisonMap G X V) :=
  inferInstanceAs (QuasiIso ((groupCohomology.inhomogeneousCochainsIso V).hom ≫ barComparison G X V))

/-- The bar-comparison isomorphism from actual group cohomology to singular Hom cohomology. -/
def groupCohomologyIso (V : Rep ℚ G) (n : ℕ) :
    groupCohomology V n ≅ (cochains G X V).homology n :=
  isoOfQuasiIsoAt (comparisonMap G X V) n

end TernaryPoly.EquivariantSingularCohomology
