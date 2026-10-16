module

public import TernaryPeriodPolynomials.SymmetricSpace.BoundaryNeighborhood.RelativeRetraction
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryNeighborhood
open scoped unitInterval
variable {X : Type} [TopologicalSpace X] {A W : Set X}

/-- The set of all starting points whose deformation path meets S. -/
def Deformation.trace (d : Deformation A W) (S : Set X) : Set X :=
  Prod.snd '' (d.homotopy ⁻¹' S)

/-- A point lies in the trace exactly when some time-map sends it into S. -/
theorem Deformation.mem_trace (d : Deformation A W) (S : Set X) (x : X) :
    x ∈ d.trace S ↔ ∃ t : I, d.homotopy (t,x) ∈ S := by
  constructor
  · rintro ⟨⟨t,y⟩,hy,hxy⟩
    subst x
    exact ⟨t,hy⟩
  · rintro ⟨t,ht⟩
    exact ⟨(t,x),ht,rfl⟩

/-- Time zero places the original set inside its full homotopy trace. -/
theorem Deformation.subset_trace (d : Deformation A W) (S : Set X) : S ⊆ d.trace S := by
  intro x hx
  apply (d.mem_trace S x).mpr
  exact ⟨0,by rwa [d.zero]⟩

/-- In a compact ambient space, the full homotopy trace of a closed set is compact. -/
theorem Deformation.trace_isCompact [CompactSpace X] (d : Deformation A W)
    (S : Set X) (hS : IsClosed S) : IsCompact (d.trace S) :=
  (hS.preimage d.homotopy.continuous).isCompact.image continuous_snd

/-- A trace of a set disjoint from the pointwise fixed boundary stays outside the boundary. -/
theorem Deformation.trace_subset_compl (d : Deformation A W) (S : Set X) (hSA : S ⊆ Aᶜ) :
    d.trace S ⊆ Aᶜ := by
  intro x hx hxA
  obtain ⟨t,ht⟩ := (d.mem_trace S x).mp hx
  rw [d.fixes t x hxA] at ht
  exact hSA ht hxA

/-- Outside the full trace, every intermediate time-map avoids S. This supplies a genuine
pair homotopy with a fixed source support, even when time-maps move interior points. -/
theorem Deformation.mapsTo_compl_trace (d : Deformation A W) (S : Set X) (t : I) :
    Set.MapsTo (fun x => d.homotopy (t,x)) (d.trace S)ᶜ Sᶜ := by
  intro x hx hS
  exact hx ((d.mem_trace S x).mpr ⟨t,hS⟩)

end TernaryPoly.BoundaryNeighborhood
