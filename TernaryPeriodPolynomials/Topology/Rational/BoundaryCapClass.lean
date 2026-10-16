module

public import TernaryPeriodPolynomials.Topology.Rational.BoundarySupportMap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMap

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalCompactBoundary
open CategoryTheory HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalManifoldCompact RationalLocalOrientation
open SingularLocalCompactCap

variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H]
  (A : Set X) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)

/-- The actual relative fundamental class viewed at the complementary degree used by cap. -/
def boundaryCapClass (c : (relativeChains A).homology (n+2))
    (a b : ℕ) (hab : a+b = n+2) : (supportChains Aᶜ).homology (a+b) :=
  homologyDegreeChange _ (n+2) (a+b) hab.symm (homologyMap (boundaryToSupport A) (n+2) c)

/-- Compact-support restriction of the actual boundary class is open excision of the actual
interior cap fundamental class, including the literal degree transport. -/
theorem boundaryCapClass_restriction
    (c : (relativeChains A).homology (n+2))
    (hc : ∀ x (hx : x ∉ A), homologyMap (boundaryPointMap A x hx) (n+2) c =
      homologyMap (RationalRelativeExcision.pointExcisionMap x Aᶜ hx) (n+2)
        (o.generator ⟨x,hx⟩))
    (K : Set X) (hK : IsCompact K) (hKA : K ⊆ Aᶜ)
    (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportRestriction Aᶜ K hKA) (a+b) (boundaryCapClass A n c a b hab) =
      homologyMap (supportExcisionMap K Aᶜ) (a+b)
        (capFundamentalClass (B := TopCat.of ↥Aᶜ) n e o ⟨Subtype.val ⁻¹' K, interiorCompact A hA K hK hKA⟩ a b hab) := by
  unfold boundaryCapClass
  change (homologyDegreeChange _ (n+2) (a+b) hab.symm ≫
    homologyMap (supportRestriction Aᶜ K hKA) (a+b)) _ = _
  rw [homologyDegreeChange_natural]
  change homologyDegreeChange _ (n+2) (a+b) hab.symm
    (homologyMap (supportRestriction Aᶜ K hKA) (n+2)
      (homologyMap (boundaryToSupport A) (n+2) c)) = _
  rw [boundaryToSupport_fundamental_restriction A hA n e o c hc K hK hKA]
  unfold interiorFundamentalClass capFundamentalClass
  change (homologyMap (supportExcisionMap K Aᶜ) (n+2) ≫
    homologyDegreeChange _ (n+2) (a+b) hab.symm) _ =
      (homologyDegreeChange _ (n+2) (a+b) hab.symm ≫
        homologyMap (supportExcisionMap K Aᶜ) (a+b)) _
  rw [homologyDegreeChange_natural]
  rfl

end TernaryPoly.RationalCompactBoundary
