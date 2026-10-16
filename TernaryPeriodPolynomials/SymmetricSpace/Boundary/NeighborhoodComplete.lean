module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.NeighborhoodLocal

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryNeighborhood
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient
  IntegralGL3Congruence BoundaryNeighborhood
open scoped unitInterval

/-- Compactness assembles actual local downward collapses into a boundary-fixing deformation
which preserves W and collapses a smaller open neighborhood into the actual boundary. -/
theorem exists_neighborhood (W : Set BordifiedOrbit) (hW : IsOpen W)
    (hAW : boundary principalSix ⊆ W) :
    ∃ d : Deformation (boundary principalSix) W, ∃ N : Set BordifiedOrbit,
      IsOpen N ∧ boundary principalSix ⊆ N ∧ N ⊆ W ∧
        ∀ y ∈ N, d.homotopy (1, y) ∈ boundary principalSix :=
  BoundaryNeighborhood.exists_global
    SymmetricSpaceCompactBordification.actual_compact_bordification.2.2.2.1
    hW hAW (exists_local W hW hAW)

/-- Actual neighborhood data; the homotopy takes place in W, while only its initial domain is N. -/
structure Collapse (W : Set BordifiedOrbit) where
  deformation : Deformation (boundary principalSix) W
  neighborhood : Set BordifiedOrbit
  isOpen : IsOpen neighborhood
  contains_boundary : boundary principalSix ⊆ neighborhood
  subset : neighborhood ⊆ W
  collapses : ∀ y ∈ neighborhood, deformation.homotopy (1, y) ∈ boundary principalSix

/-- Choose the data supplied by actual compact-boundary finite assembly. -/
def collapse (W : Set BordifiedOrbit) (hW : IsOpen W) (hAW : boundary principalSix ⊆ W) :
    Collapse W := by
  let h := exists_neighborhood W hW hAW
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.2.2.1,
    h.choose_spec.choose_spec.2.2.2⟩

/-- The actual endpoint map from the smaller open neighborhood into the boundary. -/
def Collapse.retraction {W : Set BordifiedOrbit} (c : Collapse W) :
    C(c.neighborhood, boundary principalSix) :=
  endpointRetraction c.deformation c.neighborhood c.collapses

/-- The endpoint map fixes every actual boundary point. -/
theorem Collapse.retraction_boundary {W : Set BordifiedOrbit} (c : Collapse W)
    (x : boundary principalSix) : c.retraction ⟨x.val, c.contains_boundary x.property⟩ = x :=
  endpointRetraction_boundary c.deformation c.neighborhood c.contains_boundary c.collapses x

/-- The literal inclusion of the smaller open neighborhood into W. -/
def Collapse.inclusion {W : Set BordifiedOrbit} (c : Collapse W) : C(c.neighborhood, W) :=
  ⟨fun y => ⟨y.val, c.subset y.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- The literal inclusion of the actual boundary into W. -/
def boundaryInclusion (W : Set BordifiedOrbit) (hAW : boundary principalSix ⊆ W) :
    C(boundary principalSix, W) :=
  ⟨fun x => ⟨x.val, hAW x.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- The smaller-neighborhood inclusion is homotopic inside W to the map through the boundary. -/
def Collapse.homotopy {W : Set BordifiedOrbit} (c : Collapse W) (hAW : boundary principalSix ⊆ W) :
    ContinuousMap.Homotopy c.inclusion ((boundaryInclusion W hAW).comp c.retraction) :=
  endpointHomotopy c.deformation c.neighborhood c.subset hAW c.collapses

/-- The W-valued homotopy is exactly the supported finite assembly on underlying points. -/
theorem Collapse.homotopy_apply {W : Set BordifiedOrbit} (c : Collapse W)
    (hAW : boundary principalSix ⊆ W) (t : I) (y : c.neighborhood) :
    ((c.homotopy hAW) (t, y)).val = c.deformation.homotopy (t, y.val) := rfl

/-- Every intermediate time fixes the actual boundary pointwise. -/
theorem Collapse.homotopy_boundary {W : Set BordifiedOrbit} (c : Collapse W)
    (hAW : boundary principalSix ⊆ W) (t : I) (x : boundary principalSix) :
    (c.homotopy hAW) (t, ⟨x.val, c.contains_boundary x.property⟩) = boundaryInclusion W hAW x := by
  apply Subtype.ext
  exact c.deformation.fixes t x.val x.property

/-- Consumer with an actual open smaller neighborhood, a boundary retraction, and a literal
W-valued homotopy of its inclusion to the composite through the actual boundary. -/
theorem exists_retraction_homotopy (W : Set BordifiedOrbit) (hW : IsOpen W)
    (hAW : boundary principalSix ⊆ W) :
    ∃ c : Collapse W, Nonempty
      (ContinuousMap.Homotopy c.inclusion ((boundaryInclusion W hAW).comp c.retraction)) ∧
      ∀ x : boundary principalSix, c.retraction ⟨x.val, c.contains_boundary x.property⟩ = x :=
  ⟨collapse W hW hAW, ⟨(collapse W hW hAW).homotopy hAW⟩,
    (collapse W hW hAW).retraction_boundary⟩

end TernaryPoly.SymmetricSpaceBoundaryNeighborhood
