module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryAtlas

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientBoundary
open Topology SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence
open scoped Manifold

/-- The quotient half-space inverse detects the literal arithmetic interior by positive height. -/
theorem quotientChart_symm_interior (x : Glued) (u : EuclideanHalfSpace 5) :
    (quotientChart x).symm u∈Set.range arithmeticEmbedding ↔ 0<u.val 0 := by
  rw [quotientChart_symm_apply,projection_arithmetic_iff,gluedChart_symm_apply]
  exact SymmetricSpaceBoundaryCharts.halfSpaceParam_interior _ _

/-- The quotient half-space inverse detects the already-defined actual boundary by height zero. -/
theorem quotientChart_symm_boundary (x : Glued) (u : EuclideanHalfSpace 5) :
    (quotientChart x).symm u∈boundary principalSix ↔ u.val 0=0 := by
  rw [quotientChart_symm_apply,gluedChart_symm_apply]
  have h := Set.ext_iff.mp (projection_preimage_boundary principalSix)
    (SymmetricSpaceBoundaryCharts.halfSpaceParam (SymmetricSpaceBoundaryCharts.selectedFrame x) u)
  change projection principalSix (SymmetricSpaceBoundaryCharts.halfSpaceParam
    (SymmetricSpaceBoundaryCharts.selectedFrame x) u)∈boundary principalSix ↔ _ at h
  rw [←SymmetricSpaceBoundaryCharts.boundary_eq_complement] at h
  exact h.trans (SymmetricSpaceBoundaryCharts.halfSpaceParam_boundary _ _)

theorem quotientChart_interior (x : Glued) {q : BordifiedOrbit}
    (hq : q∈(quotientChart x).source) :
    q∈Set.range arithmeticEmbedding ↔ 0<(quotientChart x q).val 0 := by
  have h := quotientChart_symm_interior x (quotientChart x q)
  rw [(quotientChart x).left_inv hq] at h
  exact h

theorem quotientChart_boundary (x : Glued) {q : BordifiedOrbit}
    (hq : q∈(quotientChart x).source) :
    q∈boundary principalSix ↔ (quotientChart x q).val 0=0 := by
  have h := quotientChart_symm_boundary x (quotientChart x q)
  rw [(quotientChart x).left_inv hq] at h
  exact h

/-- Mathlib's manifold interior for the descended atlas is exactly the original arithmetic manifold. -/
theorem interior_eq_arithmetic :
    (𝓡∂ 5).interior BordifiedOrbit=Set.range arithmeticEmbedding := by
  ext q
  change (𝓡∂ 5) (chartAt (EuclideanHalfSpace 5) q q)∈interior (Set.range (𝓡∂ 5)) ↔ _
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  change 0<(chartAt (EuclideanHalfSpace 5) q q).val 0 ↔ _
  exact (quotientChart_interior q.out (mem_chart_source (EuclideanHalfSpace 5) q)).symm

/-- The descended manifold boundary is the literal actual principal-six quotient boundary. -/
theorem boundary_eq_actual :
    (𝓡∂ 5).boundary BordifiedOrbit=boundary principalSix := by
  rw [←ModelWithCorners.compl_interior,interior_eq_arithmetic,arithmeticEmbedding_range]
  rfl

theorem frontier_arithmetic_eq_boundary :
    frontier (Set.range arithmeticEmbedding)=(𝓡∂ 5).boundary BordifiedOrbit := by
  rw [frontier,arithmeticEmbedding_dense.closure_range,
    arithmeticEmbedding_isOpenEmbedding.isOpen_range.interior_eq,
    ←Set.compl_eq_univ_sdiff,←interior_eq_arithmetic,ModelWithCorners.compl_interior]

/-- Quotient projection takes precisely the original manifold boundary onto quotient boundary. -/
theorem projection_preimage_manifold_boundary :
    projection principalSix ⁻¹' (𝓡∂ 5).boundary BordifiedOrbit=(𝓡∂ 5).boundary Glued := by
  rw [boundary_eq_actual,projection_preimage_boundary,SymmetricSpaceBoundaryCharts.boundary_eq_complement]

end TernaryPoly.SymmetricSpaceQuotientBoundary
