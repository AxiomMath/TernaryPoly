module

public import TernaryPeriodPolynomials.Topology.Rational.Chart.CompactSupportNaturality
public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.Classes

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalChartCompactSupport
open CategoryTheory Limits HomologicalComplex
open RationalRelativeSingular RationalLocalChartHomology RationalLocalOrientation

variable {X : Type} [TopologicalSpace X] [T2Space X]
variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- Compact support contained in one Euclidean chart has no actual relative homology
strictly above the chart dimension. -/
theorem chart_compact_homology_isZero_above (e : OpenPartialHomeomorph X E) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (k : ℕ) (hk : n+2 < k) :
    IsZero ((relativeChains Kᶜ).homology k) :=
  (EuclideanCompactClasses.compact_homology_isZero_above n (e '' K)
    (image_isCompact e K hK hKs) k hk).of_iso (chartSupportHomologyIso e K hK hKs k)

/-- Actual top-degree classes supported on a compact subset of a chart are detected
by every literal support-to-point restriction in the original space. -/
theorem chart_compact_class_detect (e : OpenPartialHomeomorph X E) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source)
    (c d : (relativeChains Kᶜ).homology (n+2))
    (hcd : ∀ (x : X) (hx : x ∈ K), homologyMap (supportPointMap K x hx) (n+2) c =
      homologyMap (supportPointMap K x hx) (n+2) d) : c = d := by
  apply (ModuleCat.mono_iff_injective (chartSupportHomologyIso e K hK hKs (n+2)).hom).mp inferInstance
  apply EuclideanCompactClasses.compact_class_detect n (e '' K) (image_isCompact e K hK hKs)
  rintro y ⟨x, hx, rfl⟩
  change homologyMap (supportPointMap (e '' K) (e x) ⟨x, hx, rfl⟩) (n+2)
      ((chartSupportHomologyIso e K hK hKs (n+2)).hom c) =
    homologyMap (supportPointMap (e '' K) (e x) ⟨x, hx, rfl⟩) (n+2)
      ((chartSupportHomologyIso e K hK hKs (n+2)).hom d)
  rw [chartSupportHomologyIso_point_apply e K hK hKs x hx (n+2) c,
    chartSupportHomologyIso_point_apply e K hK hKs x hx (n+2) d, hcd x hx]

/-- A compact chart-supported top-degree class vanishes exactly when all its actual
local values vanish; no choice of orientation or generator is needed. -/
theorem chart_compact_class_eq_zero_iff (e : OpenPartialHomeomorph X E) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (c : (relativeChains Kᶜ).homology (n+2)) :
    c = 0 ↔ ∀ (x : X) (hx : x ∈ K), homologyMap (supportPointMap K x hx) (n+2) c = 0 := by
  constructor
  · rintro rfl x hx
    exact map_zero _
  · intro hc
    apply chart_compact_class_detect n e K hK hKs c 0
    intro x hx
    rw [map_zero, hc x hx]

end TernaryPoly.RationalChartCompactSupport
