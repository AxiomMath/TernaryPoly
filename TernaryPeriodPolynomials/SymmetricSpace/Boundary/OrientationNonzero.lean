module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.OrientationClass
public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationLocalization
public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationLocalZero

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalLocalChartHomology RationalRelativeExcision
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SingularBoundaryRestriction HalfSpaceBoundaryOrientation SymmetricSpaceQuotientBoundary
open SymmetricSpaceRelativeFundamental

/-- Actual ambient local top homology vanishes at every boundary point, by the genuine
product chart and the explicit inward contraction of its puncture. -/
theorem boundaryAmbient_local_isZero (x : BoundaryBase) :
    IsZero ((localChains x.val).homology 5) := by
  obtain ⟨g,hg⟩ := productCharts_cover x.val
  have hp : (productChart g x.val).2.val = 0 := (productChart_boundary g hg).mp x.property
  exact (productBoundary_local_isZero (productChart g x.val) hp 4 (by decide)).of_iso
    (chartLocalHomologyIso (productChart g) x.val hg 5)

/-- Each actual interior point sees a nonzero restriction of the fixed relative class. -/
theorem fundamentalClass_interior_nonzero (y : BordifiedOrbit) (hy : y ∉ boundary principalSix) :
    homologyMap (pointRestriction (boundary principalSix) y hy) 5 fundamentalClass ≠ 0 := by
  change homologyMap (RationalCompactBoundary.boundaryPointMap (boundary principalSix) y hy) 5
    fundamentalClass ≠ 0
  rw [fundamentalClass_at_point]
  let V : Opens BordifiedOrbit := ⟨(boundary principalSix)ᶜ,(boundary_closed principalSix).isOpen_compl⟩
  let e := pointLocalHomologyIso y V hy 5
  intro h
  apply interiorOrientation.nonzero ⟨y,hy⟩
  apply e.toLinearEquiv.injective
  exact h.trans (map_zero e.hom.hom).symm

/-- Every genuine boundary-point neighborhood contains an actual interior point with a
nonzero restriction of the prescribed arithmetic relative fundamental class. -/
theorem boundary_neighborhood_nonzero (x : BoundaryBase) (U : Set BordifiedOrbit)
    (hU : IsOpen U) (hxU : x.val ∈ U) :
    ∃ y ∈ U, ∃ hy : y ∉ boundary principalSix,
      homologyMap (pointRestriction (boundary principalSix) y hy) 5 fundamentalClass ≠ 0 := by
  obtain ⟨y,hyU⟩ := arithmeticEmbedding_dense.exists_mem_open hU ⟨x.val,hxU⟩
  have hy : arithmeticEmbedding y ∉ boundary principalSix := by
    change arithmeticEmbedding y ∈ (boundary principalSix)ᶜ
    rw [boundary_compl_eq_range]
    exact ⟨y,rfl⟩
  exact ⟨arithmeticEmbedding y,hyU,hy,fundamentalClass_interior_nonzero _ hy⟩

/-- The literal connecting image of the fixed arithmetic relative fundamental class
is a nonzero local generator at every actual boundary point. -/
theorem boundaryGenerator_nonzero (x : BoundaryBase) : boundaryGenerator x ≠ 0 :=
  boundaryPoint_nonzero_of_interior (boundary principalSix) x 4 fundamentalClass
    (boundaryAmbient_local_isZero x) (boundary_neighborhood_nonzero x)

end TernaryPoly.SymmetricSpaceBoundaryOrientation
