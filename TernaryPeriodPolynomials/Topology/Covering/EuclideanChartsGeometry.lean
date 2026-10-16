module

public import TernaryPeriodPolynomials.Topology.Euclidean.BoxTransport
public import Mathlib.Geometry.Manifold.ChartedSpace

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringEuclideanCharts
open TopologicalSpace Set
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict an actual partial chart to the inverse image of a subset of its target. -/
def chartSubsetHomeomorph (c : OpenPartialHomeomorph X Y) (K : Set Y) (hK : K ⊆ c.target) :
    ↥(c.source ∩ c ⁻¹' K) ≃ₜ ↥K where
  toFun x := ⟨c x,x.property.2⟩
  invFun y := ⟨c.symm y,c.map_target (hK y.property),by
    change c (c.symm y) ∈ K
    rw [c.right_inv (hK y.property)]
    exact y.property⟩
  left_inv x := Subtype.ext (c.left_inv x.property.1)
  right_inv y := Subtype.ext (c.right_inv (hK y.property))
  continuous_toFun := (c.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property.1)).subtype_mk _
  continuous_invFun := (c.symm.continuousOn.comp_continuous continuous_subtype_val (fun y => hK y.property)).subtype_mk _

/-- Inside any actual Euclidean partial chart, every point has a smaller whole-Euclidean neighborhood. -/
theorem euclidean_neighborhood_of_chart (m : ℕ)
    (c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m))) (x : X) (hx : x ∈ c.source) :
    ∃ D : Opens X, x ∈ D ∧ (D : Set X) ⊆ c.source ∧
      Nonempty (D ≃ₜ EuclideanSpace ℝ (Fin m)) := by
  obtain ⟨B,hB,_,hHomeo⟩ := EuclideanBoxBasis.euclidean_basis m
  obtain ⟨K,hKB,hxK,hKT⟩ := hB.exists_subset_of_mem_open (c.map_source hx) c.open_target
  let D : Opens X := ⟨c.source ∩ c ⁻¹' K,c.isOpen_inter_preimage (hB.isOpen hKB)⟩
  obtain ⟨e⟩ := hHomeo K hKB ⟨c x,hxK⟩
  exact ⟨D,⟨hx,hxK⟩,inter_subset_left,⟨(chartSubsetHomeomorph c K hKT).trans e⟩⟩

variable {H : Type} [TopologicalSpace H] [ChartedSpace H X]

/-- Every neighborhood in a Euclidean-charted manifold contains a neighborhood genuinely
homeomorphic to the whole Euclidean model, using a coordinate box inside an actual chart. -/
theorem manifold_euclidean_neighborhood (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (x : X) (W : Opens X) (hxW : x ∈ W) :
    ∃ D : Opens X, x ∈ D ∧ D ≤ W ∧ Nonempty (D ≃ₜ EuclideanSpace ℝ (Fin (n+2))) := by
  let c := ((chartAt H x).restr (W : Set X)).transHomeomorph e
  have hx : x ∈ c.source := by
    change x ∈ ((chartAt H x).restr (W : Set X)).source
    rw [OpenPartialHomeomorph.restr_source,W.isOpen.interior_eq]
    exact ⟨mem_chart_source H x,hxW⟩
  obtain ⟨D,hxD,hDc,he⟩ := euclidean_neighborhood_of_chart (n+2) c x hx
  refine ⟨D,hxD,?_,he⟩
  intro y hy
  have hc := hDc hy
  change y ∈ ((chartAt H x).restr (W : Set X)).source at hc
  rw [OpenPartialHomeomorph.restr_source,W.isOpen.interior_eq] at hc
  exact hc.2

end TernaryPoly.CoveringEuclideanCharts
