module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryDetection

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory HomologicalComplex RationalRelativeSingular RationalRelativeExcision
open RationalLocalOrientation RationalManifoldCompact BoundaryNeighborhood
variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H]
  (A : Set X) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)

/-- A boundary-relative class with the specified interior orientation restricts to the actual
compact fundamental class on every compact subset of the interior. -/
theorem restriction_eq_interiorFundamentalClass
    (c : (relativeChains A).homology (n+2))
    (hc : ∀ x (hx : x ∉ A), homologyMap (boundaryPointMap A x hx) (n+2) c =
      homologyMap (pointExcisionMap x Aᶜ hx) (n+2) (o.generator ⟨x,hx⟩))
    (K : Set X) (hK : IsCompact K) (hKA : K ⊆ Aᶜ) :
    homologyMap (toNeighborhoodRelative A Kᶜ (fun _ ha hk => hKA hk ha)) (n+2) c =
      interiorFundamentalClass A hA n e o K hK hKA := by
  apply interiorFundamentalClass_unique A hA n e o K hK hKA
  intro x hx
  have hq : toNeighborhoodRelative A Kᶜ (fun _ ha hk => hKA hk ha) ≫
      supportPointMap K x hx = boundaryPointMap A x (hKA hx) := by
    unfold toNeighborhoodRelative supportPointMap boundaryPointMap
    erw [RationalRelativeSingular.relativeMap_comp]
    rfl
  change (homologyMap (toNeighborhoodRelative A Kᶜ _) (n+2) ≫
    homologyMap (supportPointMap K x hx) (n+2)) c = _
  rw [← homologyMap_comp,hq]
  exact hc x (hKA hx)

end TernaryPoly.RationalCompactBoundary
