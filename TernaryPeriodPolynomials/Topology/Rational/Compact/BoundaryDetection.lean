module

public import TernaryPeriodPolynomials.Topology.Rational.Compact.BoundaryFundamental

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory HomologicalComplex RationalRelativeSingular RationalRelativeExcision
open RationalLocalOrientation RationalManifoldCompact RationalChartCompactSupport
variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H]
  (A : Set X) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)

/-- Ambient compact classes on an interior support are uniquely determined by the genuine
interior orientation generators, through the actual excision isomorphism. -/
theorem interiorFundamentalClass_unique (K : Set X) (hK : IsCompact K) (hKA : K ⊆ Aᶜ)
    (c : (relativeChains Kᶜ).homology (n+2))
    (hc : ∀ x (hx : x ∈ K), homologyMap (supportPointMap K x hx) (n+2) c =
      homologyMap (pointExcisionMap x Aᶜ (hKA hx)) (n+2) (o.generator ⟨x,hKA hx⟩)) :
    c = interiorFundamentalClass A hA n e o K hK hKA := by
  let iso := supportExcisionIso K hK.isClosed ⟨Aᶜ,hA.isOpen_compl⟩ hKA (n+2)
  have hback : homologyMap (supportExcisionMap K Aᶜ) (n+2) (iso.inv c) = c :=
    iso.inv_hom_id_apply c
  have hi : iso.inv c = compactFundamentalClass n e o (Subtype.val ⁻¹' K)
      (interiorCompact A hA K hK hKA) := by
    apply compactFundamentalClass_unique n e o (Subtype.val ⁻¹' K)
      (interiorCompact A hA K hK hKA)
    intro x hx
    apply (ModuleCat.mono_iff_injective
      (pointLocalHomologyIso x.val ⟨Aᶜ,hA.isOpen_compl⟩ x.property (n+2)).hom).mp inferInstance
    change homologyMap (pointExcisionMap x.val Aᶜ x.property) (n+2)
      (homologyMap (supportPointMap (Subtype.val ⁻¹' K) x hx) (n+2) (iso.inv c)) = _
    have hh := congrArg (fun f => homologyMap f (n+2))
      (supportExcisionMap_point K Aᶜ x.val hx x.property)
    rw [homologyMap_comp,homologyMap_comp] at hh
    change (homologyMap (supportPointMap (Subtype.val ⁻¹' K) x hx) (n+2) ≫
      homologyMap (pointExcisionMap x.val Aᶜ x.property) (n+2)) (iso.inv c) = _
    rw [← hh]
    change homologyMap (supportPointMap K x.val hx) (n+2)
      (homologyMap (supportExcisionMap K Aᶜ) (n+2) (iso.inv c)) = _
    rw [hback]
    exact hc x.val hx
  rw [← hback,hi]
  rfl

end TernaryPoly.RationalCompactBoundary
