module

public import TernaryPeriodPolynomials.Topology.Euclidean.Convex.LocalNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanConvexLocal
open CategoryTheory Limits HomologicalComplex RationalRelativeSingular EuclideanLocalHomology

/-- Every point restriction for a compact convex Euclidean support is the actual homology isomorphism
in every degree, without an interior-point or full-dimensionality hypothesis. -/
theorem compactConvexPointHomology (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (x : EuclideanSpace ℝ (Fin (n+2))) (hx : x ∈ K) :
    QuasiIso (pointMap K x hx) ∧ ∀ k, IsIso (homologyMap (pointMap K x hx) k) := by
  have := pointMap_quasiIso K hK hconv x hx
  exact ⟨this, fun _ => inferInstance⟩

/-- Every compact convex support has actual relative homology concentrated in the Euclidean dimension;
for the empty support every degree vanishes. -/
theorem compactConvexRelativeHomology (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    (∀ k, k ≠ n+2 → IsZero ((relativeChains Kᶜ).homology k)) ∧
      (K = ∅ → ∀ k, IsZero ((relativeChains Kᶜ).homology k)) := by
  refine ⟨fun k hk => supportHomology_isZero_of_ne n k K hK hconv hk, ?_⟩
  rintro rfl k
  exact emptySupportHomology_isZero k

/-- Every nonempty compact convex Euclidean support has a unique actual rational relative class
whose literal identity-pair restriction is the fixed local generator at every point of the support. -/
theorem compactConvexRelativeFundamentalClass (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin (n+2))))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    ∃! c : (relativeChains Kᶜ).homology (n+2),
      ∀ (x : EuclideanSpace ℝ (Fin (n+2))) (hx : x ∈ K),
        homologyMap (relativeMap (ContinuousMap.id _) Kᶜ {x}ᶜ (complement_avoids K x hx)) (n+2) c =
          localGenerator n x :=
  existsUnique_convexGenerator n K hK hconv hne

end TernaryPoly.EuclideanConvexLocal
