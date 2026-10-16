module

public import TernaryPeriodPolynomials.SymmetricSpace.BoundaryNeighborhood.RelativeHomotopy
public import TernaryPeriodPolynomials.Topology.Rational.Relative.MapComposition

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryNeighborhood
open CategoryTheory HomologicalComplex RationalRelativeSingular
variable {X : Type} [TopologicalSpace X] {A W : Set X}

/-- The time-one map of the actual ambient deformation. -/
def Deformation.endpoint (d : Deformation A W) : C(X,X) :=
  ⟨fun x => d.homotopy (1,x),d.homotopy.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- The supplied deformation is the actual ambient homotopy from identity to its endpoint. -/
def Deformation.ambientHomotopy (d : Deformation A W) :
    ContinuousMap.Homotopy (ContinuousMap.id X) d.endpoint :=
  ⟨d.homotopy,d.zero,fun _ => rfl⟩

/-- The actual quotient map from boundary-relative to neighborhood-relative chains. -/
def toNeighborhoodRelative (A N : Set X) (hAN : A ⊆ N) : relativeChains A ⟶ relativeChains N :=
  relativeMap (ContinuousMap.id X) A N (fun _ hx => hAN hx)

/-- The ambient endpoint sends the smaller neighborhood into the boundary, so it defines
an actual map back from neighborhood-relative chains to boundary-relative chains. -/
def fromNeighborhoodRelative (d : Deformation A W) (N : Set X)
    (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) : relativeChains N ⟶ relativeChains A :=
  relativeMap d.endpoint N A hNA

/-- The actual quotient followed by endpoint descent is homotopic to the identity.
The neighborhood need not itself be invariant under the deformation. -/
def relativeRetractionHomotopy (d : Deformation A W) (N : Set X) (hAN : A ⊆ N)
    (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) :
    Homotopy (toNeighborhoodRelative A N hAN ≫ fromNeighborhoodRelative d N hNA)
      (𝟙 (relativeChains A)) := by
  have h := relativePairHomotopy A A (fun _ hx => hx)
    (fun x hx => by change d.homotopy (1,x) ∈ A; rw [d.fixes 1 x hx]; exact hx)
    d.ambientHomotopy (fun t x hx => by
      change d.homotopy (t,x) ∈ A
      rw [d.fixes t x hx]
      exact hx)
  have hc : toNeighborhoodRelative A N hAN ≫ fromNeighborhoodRelative d N hNA =
      relativeMap d.endpoint A A (fun x hx => hNA x (hAN hx)) := by
    exact relativeMap_comp (ContinuousMap.id X) d.endpoint A N A _ _
  exact (Homotopy.ofEq hc).trans (h.symm.trans (Homotopy.ofEq (relativeMap_id A)))

/-- The homology retraction is literal: projection followed by the endpoint-induced map
is the identity in every degree. -/
theorem relativeRetraction_homology (d : Deformation A W) (N : Set X) (hAN : A ⊆ N)
    (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) (k : ℕ) :
    homologyMap (toNeighborhoodRelative A N hAN) k ≫
      homologyMap (fromNeighborhoodRelative d N hNA) k = 𝟙 _ := by
  simpa only [homologyMap_comp,homologyMap_id] using
    (relativeRetractionHomotopy d N hAN hNA).homologyMap_eq k

/-- In particular, the actual boundary-relative to neighborhood-relative map is injective
on homology whenever this ambient endpoint collapse exists. -/
theorem toNeighborhoodRelative_homology_mono (d : Deformation A W) (N : Set X) (hAN : A ⊆ N)
    (hNA : ∀ y ∈ N, d.homotopy (1,y) ∈ A) (k : ℕ) :
    Mono (homologyMap (toNeighborhoodRelative A N hAN) k) :=
  mono_of_mono_fac (relativeRetraction_homology d N hAN hNA k)

end TernaryPoly.BoundaryNeighborhood
