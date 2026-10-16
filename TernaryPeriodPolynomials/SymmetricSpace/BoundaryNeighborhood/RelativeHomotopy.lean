module

public import TernaryPeriodPolynomials.SymmetricSpace.BoundaryNeighborhood.Homotopy
public import TernaryPeriodPolynomials.Topology.Rational.Relative.PairHomotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryNeighborhood
open CategoryTheory HomologicalComplex RationalRelativeSingular
variable {X : Type} [TopologicalSpace X] {A W : Set X}

/-- The literal boundary subspace within a neighborhood. -/
def boundaryWithin (A N : Set X) : Set N := Subtype.val ⁻¹' A

/-- The literal map of nested neighborhoods. -/
def neighborhoodInclusion (N W : Set X) (hNW : N ⊆ W) : C(N,W) :=
  ⟨fun y => ⟨y.val,hNW y.property⟩,continuous_subtype_val.subtype_mk _⟩

/-- The literal relative chain map between two neighborhoods of the same boundary. -/
def neighborhoodRelativeMap (A N W : Set X) (hNW : N ⊆ W) :=
  relativeMap (neighborhoodInclusion N W hNW) (boundaryWithin A N) (boundaryWithin A W)
    (fun _ hx => hx)

/-- A neighborhood collapse yields an actual relative chain nullhomotopy of the smaller
neighborhood inclusion, since the homotopy fixes the boundary throughout. -/
def neighborhoodRelativeNullhomotopy (d : Deformation A W) (N : Set X)
    (hNW : N ⊆ W) (hAW : A ⊆ W) (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) :
    Homotopy (neighborhoodRelativeMap A N W hNW) 0 := by
  let g : C(N,W) := (neighborhoodInclusion A W hAW).comp (endpointRetraction d N hNA)
  have hg (x : N) : g x ∈ boundaryWithin A W := hNA x.val x.property
  apply relativePairNullhomotopy (boundaryWithin A N) (boundaryWithin A W)
    (fun _ hx => hx) (fun x _ => hg x) (endpointHomotopy d N hNW hAW hNA) _ hg
  intro t x hx
  change d.homotopy (t,x.val) ∈ A
  rw [d.fixes t x.val hx]
  exact hx

/-- The actual relative homology map vanishes in every degree. -/
theorem neighborhoodRelativeHomologyMap_zero (d : Deformation A W) (N : Set X)
    (hNW : N ⊆ W) (hAW : A ⊆ W) (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) (k : ℕ) :
    homologyMap (neighborhoodRelativeMap A N W hNW) k = 0 := by
  simpa using (neighborhoodRelativeNullhomotopy d N hNW hAW hNA).homologyMap_eq k

/-- Compactness and actual local boundary collapses imply eventual zero of relative
neighborhood maps, simultaneously in every degree, through a literal chain nullhomotopy. -/
theorem exists_relative_nullhomotopy (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W)
    (hlocal : ∀ x ∈ A, ∃ d : Deformation A W, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, d.homotopy (1,y) ∈ A) :
    ∃ (N : Set X), IsOpen N ∧ A ⊆ N ∧ ∃ (hNW : N ⊆ W),
      Nonempty (Homotopy (neighborhoodRelativeMap A N W hNW) 0) := by
  obtain ⟨d,N,hN,hAN,hNW,hNA⟩ := exists_global hA hW hAW hlocal
  exact ⟨N,hN,hAN,hNW,⟨neighborhoodRelativeNullhomotopy d N hNW hAW hNA⟩⟩

end TernaryPoly.BoundaryNeighborhood
