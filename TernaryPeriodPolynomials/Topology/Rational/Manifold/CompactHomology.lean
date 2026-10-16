module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactLocal

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex RationalLocalOrientation RationalLocalChartHomology
variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H] [ChartedSpace H X]

/-- Actual homology supported on any compact subset of a Euclidean-charted Hausdorff manifold vanishes above its dimension. No orientation is required. -/
theorem manifold_compact_above (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (K : Set X) (hK : IsCompact K) (k : ℕ) (hk : n+2 < k) :
    IsZero ((supportChains K).homology k) :=
  (manifold_compact_data n e (fun _ => 0) (zero_locallyRepresented (n+2)) K hK).above k hk

/-- Actual top-degree classes supported on a compact subset are detected by their literal restriction to every support point, without an orientability assumption. -/
theorem manifold_compact_detect (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (K : Set X) (hK : IsCompact K) (a b : (supportChains K).homology (n+2))
    (hab : ∀ (x : X) (hx : x ∈ K), homologyMap (supportPointMap K x hx) (n+2) a =
      homologyMap (supportPointMap K x hx) (n+2) b) : a = b :=
  (manifold_compact_data n e (fun _ => 0) (zero_locallyRepresented (n+2)) K hK).detect a b hab

/-- A compactly supported top-degree relative class vanishes precisely when all its actual local values vanish. -/
theorem manifold_compact_eq_zero_iff (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (K : Set X) (hK : IsCompact K) (c : (supportChains K).homology (n+2)) :
    c = 0 ↔ ∀ (x : X) (hx : x ∈ K), homologyMap (supportPointMap K x hx) (n+2) c = 0 := by
  constructor
  · rintro rfl x hx
    exact map_zero _
  · intro hc
    apply manifold_compact_detect n e K hK c 0
    intro x hx
    rw [hc x hx, map_zero]

end TernaryPoly.RationalManifoldCompact
