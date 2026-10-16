module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.NeighborhoodComplete

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryNeighborhood
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence

/-- Unconditional actual-boundary consumer: every open boundary neighborhood W contains
an open N whose inclusion into W is literally homotopic in W to a boundary retraction. -/
theorem actual_boundary_neighborhood_consumer (W : Set BordifiedOrbit) (hW : IsOpen W)
    (hAW : boundary principalSix ⊆ W) :
    ∃ (N : Set BordifiedOrbit) (_ : IsOpen N) (hAN : boundary principalSix ⊆ N) (hNW : N ⊆ W)
      (r : C(N, boundary principalSix)),
      (∀ x : boundary principalSix, r ⟨x.val, hAN x.property⟩ = x) ∧
      Nonempty (ContinuousMap.Homotopy
        (⟨fun y : N => (⟨y.val, hNW y.property⟩ : W),
          continuous_subtype_val.subtype_mk _⟩ : C(N, W))
        ((boundaryInclusion W hAW).comp r)) := by
  let c := collapse W hW hAW
  exact ⟨c.neighborhood, c.isOpen, c.contains_boundary, c.subset, c.retraction,
    c.retraction_boundary, ⟨c.homotopy hAW⟩⟩

end TernaryPoly.SymmetricSpaceBoundaryNeighborhood
