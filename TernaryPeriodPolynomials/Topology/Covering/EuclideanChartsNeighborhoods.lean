module

public import TernaryPeriodPolynomials.Topology.Covering.EuclideanChartsGeometry
public import TernaryPeriodPolynomials.Topology.Covering.EuclideanChartsSections

@[expose] public section

noncomputable section
namespace TernaryPoly.CoveringEuclideanCharts
open CategoryTheory TopologicalSpace
open EquivariantSingularSmall
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]

/-- Explicit Euclidean neighborhood data with a genuine continuous section of its actual covering. -/
structure Neighborhood (n : ℕ) (x : B) (W : Opens B) where
  openSet : Opens B
  mem_openSet : x ∈ openSet
  subset : openSet ≤ W
  homeomorph : openSet ≃ₜ EuclideanSpace ℝ (Fin (n+2))
  lift : Section p openSet

variable {H : Type} [TopologicalSpace H] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
include hp e

/-- Every prescribed open neighborhood contains a genuine Euclidean covering chart with
an actual continuous section; the covering and chart choices are discharged here. -/
theorem exists_neighborhood (x : B) (W : Opens B) (hxW : x ∈ W) :
    Nonempty (Neighborhood p n x W) := by
  obtain ⟨U,hxU,⟨s⟩⟩ := exists_local_section (G := G) p x
  obtain ⟨D,hxD,hD,⟨h⟩⟩ := manifold_euclidean_neighborhood n e x (W ⊓ U) ⟨hxW,hxU⟩
  exact ⟨⟨D,hxD,fun _ hy => (hD hy).1,h,Section.restrict p s D (fun _ hy => (hD hy).2)⟩⟩

/-- One actual Euclidean neighborhood and section selected from the proved existence theorem. -/
def neighborhood (x : B) (W : Opens B) (hxW : x ∈ W) : Neighborhood p n x W :=
  Classical.choice (exists_neighborhood (G := G) p n e x W hxW)

/-- The chosen neighborhood section is a literal right inverse of the actual restricted projection. -/
theorem neighborhood_section_rightInverse (x : B) (W : Opens B) (hxW : x ∈ W) :
    (neighborhood (G := G) p n e x W hxW).lift.map ≫
      restrictedProjection p ((neighborhood (G := G) p n e x W hxW).openSet : Set B) = 𝟙 _ :=
  (neighborhood (G := G) p n e x W hxW).lift.right_inv

end TernaryPoly.CoveringEuclideanCharts
