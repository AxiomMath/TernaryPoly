module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCoefficientNaturality
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactRelativeSmall
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.RealCoefficientNorm
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactAssemblyAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering

variable (A : Rep.{0} ℚ DeckGroup) [FiniteDimensional ℚ A]
attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

/-- Genuine ordinary smooth/singular H² comparison for the actual real extension of rational coefficients. -/
def realOrdinarySmoothComparison (C : CompactConvexCover) :
    (globalComplex (realRep A).ρ).homology 2 ≅ (coveringCochains (realRep A).ρ univ).homology 2 :=
  compactCoverGlobalComparison (realRep A).ρ C

/-- Genuine compact smooth H² identifies with the original actual real compact relative-kernel colimit. -/
def realCompactSmoothComparison (C : CompactConvexCover) :
    (globalCompactComplex (realRep A).ρ).homology 2 ≅ realCoverCompactCohomology A 2 :=
  compactSmallComparison (realRep A).ρ C ≪≫ (realCompactFiniteSmallIso A C 2).symm

/-- The actual global and compact smooth/singular comparisons preserve the exact original real compactForget map. -/
theorem realCompactSmoothComparison_forget (C : CompactConvexCover) :
    (realCompactSmoothComparison A C).hom ≫ realCoverCompactForget A 2 =
      homologyMap (compactInclusion (realRep A).ρ isOpen_univ) 2 ≫ (realOrdinarySmoothComparison A C).hom := by
  let := coveringSmallRestriction_quasiIso (realRep A).ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge
  exact compactComparison_square (compactSmallComparison (realRep A).ρ C) (realCompactFiniteSmallIso A C 2)
    (realOrdinarySmoothComparison A C) (homologyMap (compactInclusion (realRep A).ρ isOpen_univ) 2)
    (homologyMap (finiteRestrictionSmallSubmodules (realRep A).ρ C).inclusion 2)
    (homologyMap (coveringSmallRestriction (realRep A).ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge) 2)
    (realCoverCompactForget A 2) (compactCoverSmallComparison (realRep A).ρ C).hom
    (realCompactFiniteSmallIso_forget A C 2) (compactSmallComparison_forget (realRep A).ρ C)
    (compactCoverGlobalComparison_small (realRep A).ρ C)

end TernaryPoly.SmoothSingularGlobal
