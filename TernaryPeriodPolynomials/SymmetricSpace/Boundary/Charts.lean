module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsCollar

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryCharts
open Topology SymmetricSpacePositive SymmetricSpaceRationalAction SymmetricSpaceRationalGluing
open scoped Manifold

/-- The actual rational bordification has standard dimension-five half-space charts, on its
existing Hausdorff, second-countable topology. -/
theorem topological_manifold_data :
    Nonempty (ChartedSpace (EuclideanHalfSpace 5) Glued) ∧
      T2Space Glued ∧ SecondCountableTopology Glued :=
  ⟨⟨chartedSpace⟩,inferInstance,inferInstance⟩

/-- The added points are exactly both the chart-defined manifold boundary and the frontier of
the actual symmetric-space embedding. -/
theorem actual_boundary_identification :
    (𝓡∂ 5).boundary Glued=(Set.range embedding)ᶜ ∧
      frontier (Set.range embedding)=(𝓡∂ 5).boundary Glued :=
  ⟨boundary_eq_complement,frontier_embedding_eq_boundary⟩

/-- Each actual boundary point belongs to a genuine local product collar whose zero slice is
the boundary and whose positive radii are in the embedded positive-form space. -/
theorem actual_local_collar (x : Glued) (hx : x∈(𝓡∂ 5).boundary Glued) :
    ∃ g : RationalGL, ∃ v : BoundaryCoordinates,
      boundarySlice g v=x ∧ IsOpenEmbedding (collar g) ∧
      (∀ p : ProductModel, collar g p∈(𝓡∂ 5).boundary Glued ↔ p.2.val=0) ∧
      (∀ p : ProductModel, collar g p∈Set.range embedding ↔ 0<p.2.val) := by
  obtain ⟨g,v,hv⟩ := exists_local_collar x hx
  exact ⟨g,v,hv,collar_isOpenEmbedding g,collar_zero_iff g,collar_positive_iff g⟩

end TernaryPoly.SymmetricSpaceBoundaryCharts
