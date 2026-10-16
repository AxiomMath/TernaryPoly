module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactInduction
public import TernaryPeriodPolynomials.Topology.Rational.Chart.CompactSupportDetection

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalLocalOrientation RationalLocalChartHomology RationalChartCompactSupport
variable {X : Type} [TopologicalSpace X]

/-- The zero family of actual local homology classes has a genuine common relative representative on every neighborhood. -/
theorem zero_locallyRepresented (d : ℕ) : LocallyRepresented d (fun x : X => (0 : (localChains x).homology d)) := by
  intro x
  refine ⟨⊤, Set.univ, trivial, Set.subset_univ _, 0, ?_⟩
  intro y hy hK
  exact map_zero _

variable [T2Space X]

/-- Inside one chart and one actual representing neighborhood, every compact subset has all fundamental-class data. Existence is restriction of the given representative; detection and vanishing come from the genuine chart comparison. -/
theorem chart_represented_data (n : ℕ) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (n+2))))
    (g : ∀ x : X, (localChains x).homology (n+2)) (U : Opens X) (S : Set X) (hUS : (U : Set X) ⊆ S)
    (c : (supportChains S).homology (n+2))
    (hc : ∀ (x : X) (_hxU : x ∈ U) (hxS : x ∈ S), homologyMap (supportPointMap S x hxS) (n+2) c = g x)
    (K : Set X) (hK : IsCompact K) (hKe : K ⊆ e.source) (hKU : K ⊆ U) :
    LocalFundamentalData (n+2) g K := by
  refine ⟨hK, fun k hk => chart_compact_homology_isZero_above n e K hK hKe k hk,
    fun a b hab => chart_compact_class_detect n e K hK hKe a b hab, ?_⟩
  refine ⟨homologyMap (supportRestriction S K (hKU.trans hUS)) (n+2) c, ?_⟩
  intro x hx
  rw [restriction_point_apply]
  exact hc x (hKU hx) (hUS (hKU hx))

/-- Locally represented actual local classes provide fundamental data on every compact subset of a sufficiently small chart neighborhood. -/
theorem locallyRepresented_chart_data {H : Type} [TopologicalSpace H] [ChartedSpace H X]
    (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (g : ∀ x : X, (localChains x).homology (n+2)) (hg : LocallyRepresented (n+2) g) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ K : Set X, IsCompact K → K ⊆ U → LocalFundamentalData (n+2) g K := by
  obtain ⟨U, S, hxU, hUS, c, hc⟩ := hg x
  let f := (chartAt H x).transHomeomorph e
  refine ⟨⟨f.source, f.open_source⟩ ⊓ U, ?_, ?_⟩
  · exact ⟨mem_chart_source H x, hxU⟩
  · intro K hK hKU
    exact chart_represented_data n f g U S hUS c hc K hK
      (fun _ hx => (hKU hx).1) (fun _ hx => (hKU hx).2)

/-- Genuine compact-subset fundamental data on a Hausdorff Euclidean-charted manifold, derived from the actual locally represented local family. -/
theorem manifold_compact_data {H : Type} [TopologicalSpace H] [ChartedSpace H X]
    (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (g : ∀ x : X, (localChains x).homology (n+2)) (hg : LocallyRepresented (n+2) g)
    (K : Set X) (hK : IsCompact K) : LocalFundamentalData (n+2) g K := by
  let : LocallyCompactSpace H := e.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace H X
  exact compact_data_of_local (n+2) g K hK (locallyRepresented_chart_data n e g hg)

end TernaryPoly.RationalManifoldCompact
