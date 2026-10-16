module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVClamp

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology SingularBoundaryRestriction
open scoped unitInterval

def lineNeighborhood : Set BoundaryBase := planeBaseᶜ ∪ collarNeighborhood
def planeNeighborhood : Set BoundaryBase := lineBaseᶜ ∪ collarNeighborhood

theorem lineNeighborhood_open : IsOpen lineNeighborhood := planeBase_closed.isOpen_compl.union collarNeighborhood_open
theorem planeNeighborhood_open : IsOpen planeNeighborhood := lineBase_closed.isOpen_compl.union collarNeighborhood_open

theorem neighborhoods_cover : lineNeighborhood ∪ planeNeighborhood=Set.univ := by
  ext x
  simp only [Set.mem_univ,iff_true]
  by_cases hl : x∈lineBase
  · by_cases hp : x∈planeBase
    · exact Or.inl (Or.inr (cornerBase_subset_collar (bases_inter.subset ⟨hl,hp⟩)))
    · exact Or.inl (Or.inl hp)
  · exact Or.inr (Or.inl hl)

theorem neighborhoods_inter : lineNeighborhood ∩ planeNeighborhood=collarNeighborhood := by
  ext x
  constructor
  · rintro ⟨hl,hp⟩
    rcases hl with h | h
    · rcases hp with h' | h'
      · exact False.elim ((bases_cover.ge (Set.mem_univ x)).elim h' h)
      · exact h'
    · exact h
  · intro h
    exact ⟨Or.inr h,Or.inr h⟩

theorem planeBase_compl_subset_line : planeBaseᶜ⊆lineBase := by
  intro x hx
  exact (bases_cover.ge (Set.mem_univ x)).resolve_right hx

theorem lineBase_compl_subset_plane : lineBaseᶜ⊆planeBase := by
  intro x hx
  exact (bases_cover.ge (Set.mem_univ x)).resolve_left hx

theorem lineBase_subset_neighborhood : lineBase⊆lineNeighborhood := by
  intro x hx
  by_cases hp : x∈planeBase
  · exact Or.inr (cornerBase_subset_collar (bases_inter.subset ⟨hx,hp⟩))
  · exact Or.inl hp

theorem planeBase_subset_neighborhood : planeBase⊆planeNeighborhood := by
  intro x hx
  by_cases hl : x∈lineBase
  · exact Or.inr (cornerBase_subset_collar (bases_inter.subset ⟨hl,hx⟩))
  · exact Or.inl hl

def lineBaseFlow : C(I × lineNeighborhood,BoundaryBase) :=
  OpenGlue.homotopy planeBaseᶜ collarNeighborhood planeBase_closed.isOpen_compl collarNeighborhood_open
    lineCollarFlow (fun t x h => lineCollarFlow_fixed t x (planeBase_compl_subset_line h))

def planeBaseFlow : C(I × planeNeighborhood,BoundaryBase) :=
  OpenGlue.homotopy lineBaseᶜ collarNeighborhood lineBase_closed.isOpen_compl collarNeighborhood_open
    planeCollarFlow (fun t x h => planeCollarFlow_fixed t x (lineBase_compl_subset_plane h))

@[simp] theorem lineBaseFlow_zero (x : lineNeighborhood) : lineBaseFlow (0,x)=x.val :=
  OpenGlue.homotopy_zero _ _ _ _ _ _ (collarFlow_zero _ _) x

@[simp] theorem planeBaseFlow_zero (x : planeNeighborhood) : planeBaseFlow (0,x)=x.val :=
  OpenGlue.homotopy_zero _ _ _ _ _ _ (collarFlow_zero _ _) x

theorem lineBaseFlow_preserves (t : I) (x : lineNeighborhood) : lineBaseFlow (t,x)∈lineNeighborhood :=
  OpenGlue.homotopy_preserves _ _ _ _ _ _ (collarFlow_preserves _ _) t x

theorem planeBaseFlow_preserves (t : I) (x : planeNeighborhood) : planeBaseFlow (t,x)∈planeNeighborhood :=
  OpenGlue.homotopy_preserves _ _ _ _ _ _ (collarFlow_preserves _ _) t x

theorem lineBaseFlow_fixed (t : I) (x : lineNeighborhood) (hx : x.val∈lineBase) :
    lineBaseFlow (t,x)=x.val :=
  OpenGlue.homotopy_fixed _ _ _ _ _ _ lineCollarFlow_fixed t x hx

theorem planeBaseFlow_fixed (t : I) (x : planeNeighborhood) (hx : x.val∈planeBase) :
    planeBaseFlow (t,x)=x.val :=
  OpenGlue.homotopy_fixed _ _ _ _ _ _ planeCollarFlow_fixed t x hx

theorem lineBaseFlow_endpoint (x : lineNeighborhood) : lineBaseFlow (1,x)∈lineBase :=
  OpenGlue.homotopy_endpoint _ _ _ _ _ _ planeBase_compl_subset_line lineCollarFlow_endpoint x

theorem planeBaseFlow_endpoint (x : planeNeighborhood) : planeBaseFlow (1,x)∈planeBase :=
  OpenGlue.homotopy_endpoint _ _ _ _ _ _ lineBase_compl_subset_plane planeCollarFlow_endpoint x

/-- On the overlap, the side homotopy is literally the corresponding signed clamp. -/
theorem lineBaseFlow_collar (t : I) (x : lineNeighborhood) (hx : x.val∈collarNeighborhood) :
    lineBaseFlow (t,x)=lineCollarFlow (t,⟨x.val,hx⟩) :=
  OpenGlue.homotopy_of_mem_right _ _ _ _ _ _ t x hx

theorem planeBaseFlow_collar (t : I) (x : planeNeighborhood) (hx : x.val∈collarNeighborhood) :
    planeBaseFlow (t,x)=planeCollarFlow (t,⟨x.val,hx⟩) :=
  OpenGlue.homotopy_of_mem_right _ _ _ _ _ _ t x hx

end TernaryPoly.SymmetricSpaceBoundaryMV
