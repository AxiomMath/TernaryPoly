module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsAtlas
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryCharts
open Topology SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
  SymmetricSpaceRationalGluing
open scoped Manifold

/-- The distinguished chart's positive half-space points are exactly the actual embedded forms. -/
theorem selectedPoint_mem_interior (x : Glued) :
    selectedPoint x∈cornerInterior ↔ x∈Set.range embedding := by
  have h := Set.ext_iff.mp (chart_preimage_embedding (selectedFrame x)) (selectedPoint x)
  change chart (selectedFrame x) (selectedPoint x)∈Set.range embedding ↔
    selectedPoint x∈cornerInterior at h
  rw [chart_selectedPoint] at h
  exact h.symm

/-- Mathlib's manifold interior, for the constructed atlas, is the actual symmetric space. -/
theorem isInteriorPoint_iff_embedding (x : Glued) :
    (𝓡∂ 5).IsInteriorPoint x ↔ x∈Set.range embedding := by
  change (𝓡∂ 5) (chartAt (EuclideanHalfSpace 5) x x)∈interior (Set.range (𝓡∂ 5)) ↔ _
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  change 0<(chartAt (EuclideanHalfSpace 5) x x).val 0 ↔ _
  rw [chartAt_apply,cornerHalfSpace_positive]
  exact selectedPoint_mem_interior x

/-- The manifold-with-boundary interior is exactly the image of the actual positive-form space. -/
theorem interior_eq_embedding : (𝓡∂ 5).interior Glued=Set.range embedding := by
  ext x
  exact isInteriorPoint_iff_embedding x

/-- The topological manifold boundary consists exactly of the added points. -/
theorem boundary_eq_complement : (𝓡∂ 5).boundary Glued=(Set.range embedding)ᶜ := by
  rw [←ModelWithCorners.compl_interior,interior_eq_embedding]

theorem isClosed_boundary : IsClosed ((𝓡∂ 5).boundary Glued) := by
  rw [boundary_eq_complement]
  exact embedding_range_open.isClosed_compl

/-- The frontier of the dense open symmetric-space image is precisely the manifold boundary. -/
theorem frontier_embedding_eq_boundary : frontier (Set.range embedding)=(𝓡∂ 5).boundary Glued := by
  rw [frontier,embedding_denseRange.closure_range,embedding_range_open.interior_eq,
    ←Set.compl_eq_univ_sdiff,boundary_eq_complement]

/-- The complement of the positive quadrant is exactly its two closed faces. -/
theorem corner_not_interior_iff (p : Corner) :
    p∉cornerInterior ↔ p.2.1.val=0 ∨ p.2.2.val=0 := by
  rw [←cornerHalfSpace_zero,←cornerHalfSpace_positive]
  constructor
  · intro h
    exact le_antisymm (le_of_not_gt h) (cornerHalfSpaceHomeomorph p).property
  · intro h
    simp [h]

/-- Every original rational corner sees exactly the two actual zero-root faces as boundary. -/
theorem chart_preimage_boundary (g : RationalGL) :
    chart g ⁻¹' (𝓡∂ 5).boundary Glued={p : Corner | p.2.1.val=0 ∨ p.2.2.val=0} := by
  rw [boundary_eq_complement,Set.preimage_compl,chart_preimage_embedding]
  ext p
  exact corner_not_interior_iff p

/-- In each standard chart the first Euclidean coordinate detects its boundary slice. -/
theorem chart_boundary_height (g : RationalGL) (p : Corner) :
    chart g p∈(𝓡∂ 5).boundary Glued ↔ (halfSpaceChart g (chart g p)).val 0=0 := by
  rw [halfSpaceChart_apply_chart,cornerHalfSpace_zero]
  exact Set.ext_iff.mp (chart_preimage_boundary g) p

theorem halfSpaceParam_boundary (g : RationalGL) (p : EuclideanHalfSpace 5) :
    halfSpaceParam g p∈(𝓡∂ 5).boundary Glued ↔ p.val 0=0 := by
  have h := chart_boundary_height g (cornerHalfSpaceHomeomorph.symm p)
  simpa only [halfSpaceParam,Function.comp_apply,halfSpaceChart_apply_chart,
    Homeomorph.apply_symm_apply] using h

theorem halfSpaceParam_interior (g : RationalGL) (p : EuclideanHalfSpace 5) :
    halfSpaceParam g p∈Set.range embedding ↔ 0<p.val 0 := by
  have h := Set.ext_iff.mp (chart_preimage_embedding g) (cornerHalfSpaceHomeomorph.symm p)
  change halfSpaceParam g p∈Set.range embedding ↔ _ at h
  rw [←cornerHalfSpace_positive,Homeomorph.apply_symm_apply] at h
  exact h

end TernaryPoly.SymmetricSpaceBoundaryCharts
