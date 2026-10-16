module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryInterior
public import TernaryPeriodPolynomials.Topology.Covering.BoundaryDeformation

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularBoundaryRestriction
open SymmetricSpaceBordifiedQuotient SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence

/-- The actual boundary neighborhood complementary to a compact support in the open interior. -/
def outsideCompact (K : Compacts interiorOpen) : Set BordifiedOrbit :=
  (openCompactImage interiorOpen K : Set BordifiedOrbit)ᶜ

/-- Compact interior supports have open complementary neighborhoods in the Hausdorff bordification. -/
theorem outsideCompact_open (K : Compacts interiorOpen) : IsOpen (outsideCompact K) :=
  (openCompactImage interiorOpen K).isCompact.isClosed.isOpen_compl

/-- Every actual compact interior support is disjoint from the entire boundary. -/
theorem boundary_subset_outsideCompact (K : Compacts interiorOpen) :
    boundary principalSix ⊆ outsideCompact K := by
  intro x hx hxK
  exact hx (openCompactImage_subset interiorOpen K hxK)

/-- Every open boundary neighborhood has a compact complementary support inside the genuine interior. -/
def neighborhoodCompact (W : Set BordifiedOrbit) (hW : IsOpen W) (hAW : boundary principalSix ⊆ W) :
    Compacts interiorOpen :=
  compactWithinOpen interiorOpen ⟨Wᶜ,hW.isClosed_compl.isCompact⟩ (fun x hx => by
    by_contra hxi
    exact hx (hAW hxi))

/-- The actual image of the compact neighborhood complement is the literal complement. -/
theorem neighborhoodCompact_image (W : Set BordifiedOrbit) (hW : IsOpen W)
    (hAW : boundary principalSix ⊆ W) :
    (openCompactImage interiorOpen (neighborhoodCompact W hW hAW) : Set BordifiedOrbit) = Wᶜ := by
  exact congrArg (fun K : Compacts BordifiedOrbit => (K : Set BordifiedOrbit))
    (openCompactImage_compactWithin interiorOpen ⟨Wᶜ,hW.isClosed_compl.isCompact⟩ _)

/-- The actual complementary-neighborhood parametrization is cofinal and recovers each open neighborhood. -/
theorem outside_neighborhoodCompact (W : Set BordifiedOrbit) (hW : IsOpen W)
    (hAW : boundary principalSix ⊆ W) :
    outsideCompact (neighborhoodCompact W hW hAW) = W := by
  unfold outsideCompact
  rw [neighborhoodCompact_image,compl_compl]

/-- Every prescribed smaller boundary neighborhood supplies a larger genuine compact interior support. -/
theorem compact_le_neighborhoodCompact (K : Compacts interiorOpen) (W : Set BordifiedOrbit)
    (hW : IsOpen W) (hAW : boundary principalSix ⊆ W) (hWK : W ⊆ outsideCompact K) :
    K ≤ neighborhoodCompact W hW hAW := by
  intro x hx hxW
  exact hWK hxW (Set.mem_image_of_mem Subtype.val hx)

/-- Shrinking an open boundary neighborhood is exactly enlargement of its compact interior complement. -/
theorem neighborhoodCompact_mono (N W : Set BordifiedOrbit) (hN : IsOpen N) (hW : IsOpen W)
    (hAN : boundary principalSix ⊆ N) (hAW : boundary principalSix ⊆ W) (hNW : N ⊆ W) :
    neighborhoodCompact W hW hAW ≤ neighborhoodCompact N hN hAN :=
  fun _ hx hn => hx (hNW hn)

/-- Enlarging a compact interior support shrinks its literal complementary boundary neighborhood. -/
theorem outsideCompact_antitone {K L : Compacts interiorOpen} (hKL : K ≤ L) :
    outsideCompact L ⊆ outsideCompact K := Set.compl_subset_compl.mpr (Set.image_mono hKL)

end TernaryPoly.CompactInteriorRelativeBoundary
