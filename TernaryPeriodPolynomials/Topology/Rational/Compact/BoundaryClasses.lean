module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactClasses
public import TernaryPeriodPolynomials.Topology.Rational.Chart.CompactSupportRestriction
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionSupport

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalRelativeExcision RationalLocalOrientation
open RationalManifoldCompact RationalChartCompactSupport
variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H]
  (A : Set X) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)

omit [T2Space X] in
include hA in
/-- Compact supports contained in the interior remain compact as subsets of the interior. -/
theorem interiorCompact (K : Set X) (hK : IsCompact K) (hKA : K ⊆ Aᶜ) :
    IsCompact (Subtype.val ⁻¹' K : Set ↥Aᶜ) :=
  (SingularLocalSupport.compactWithinOpen (B := TopCat.of X)
    ⟨Aᶜ,hA.isOpen_compl⟩ ⟨K,hK⟩ hKA).isCompact

/-- The actual interior compact fundamental class viewed in the ambient relative chains
through the literal open excision map. The ambient space may have boundary. -/
def interiorFundamentalClass (K : Set X) (hK : IsCompact K) (hKA : K ⊆ Aᶜ) :
    (relativeChains Kᶜ).homology (n+2) :=
  homologyMap (supportExcisionMap K Aᶜ) (n+2)
    (compactFundamentalClass n e o (Subtype.val ⁻¹' K) (interiorCompact A hA K hK hKA))

/-- Interior compact fundamental classes retain the actual orientation at every support point. -/
theorem interiorFundamentalClass_at_point (K : Set X) (hK : IsCompact K) (hKA : K ⊆ Aᶜ)
    (x : X) (hx : x ∈ K) :
    homologyMap (supportPointMap K x hx) (n+2) (interiorFundamentalClass A hA n e o K hK hKA) =
      homologyMap (pointExcisionMap x Aᶜ (hKA hx)) (n+2) (o.generator ⟨x,hKA hx⟩) := by
  have h := congrArg (fun f => homologyMap f (n+2))
    (supportExcisionMap_point K Aᶜ x hx (hKA hx))
  rw [homologyMap_comp,homologyMap_comp] at h
  change (homologyMap (supportExcisionMap K Aᶜ) (n+2) ≫
    homologyMap (supportPointMap K x hx) (n+2)) _ = _
  rw [h]
  exact congrArg (fun c => homologyMap (pointExcisionMap x Aᶜ (hKA hx)) (n+2) c)
    (compactFundamentalClass_at_point n e o (Subtype.val ⁻¹' K)
      (interiorCompact A hA K hK hKA) ⟨x,hKA hx⟩ hx)

/-- Restriction of the actual ambient compact class agrees with the compact class on the
smaller interior support, using genuine open-excision naturality. -/
theorem interiorFundamentalClass_restriction (K L : Set X) (hK : IsCompact K)
    (hL : IsCompact L) (hKA : K ⊆ Aᶜ) (hLA : L ⊆ Aᶜ) (hLK : L ⊆ K) :
    homologyMap (supportRestriction K L hLK) (n+2) (interiorFundamentalClass A hA n e o K hK hKA) =
      interiorFundamentalClass A hA n e o L hL hLA := by
  have h := congrArg (fun f => homologyMap f (n+2)) (supportExcisionMap_restriction K L Aᶜ hLK)
  rw [homologyMap_comp,homologyMap_comp] at h
  unfold interiorFundamentalClass
  change (homologyMap (supportExcisionMap K Aᶜ) (n+2) ≫
    homologyMap (supportRestriction K L hLK) (n+2)) _ = _
  rw [h]
  exact congrArg (fun c => homologyMap (supportExcisionMap L Aᶜ) (n+2) c)
    (compactFundamentalClass_restriction n e o (Subtype.val ⁻¹' K) (Subtype.val ⁻¹' L)
      (interiorCompact A hA K hK hKA) (interiorCompact A hA L hL hLA) (Set.preimage_mono hLK))

end TernaryPoly.RationalCompactBoundary
