module

public import TernaryPeriodPolynomials.Topology.Rational.BoundaryCapClass
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapOpenHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalBoundaryCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalRelativeSingular RationalManifoldCompact RationalLocalOrientation RationalCompactBoundary
open SingularLocalCoefficient SingularLocalHomology SingularLocalSupport SingularLocalCompactCap
open EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  [IsCancelSMul G E] {H : Type} [TopologicalSpace H] [T2Space B]
  (A : Set B) (hA : IsClosed A) [ChartedSpace H ↥Aᶜ]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) ↥Aᶜ)

/-- The actual relative cap with a boundary-relative scalar class, expressed in the literal
kernel of restriction to the boundary and the actual absolute local chains. -/
def boundaryCapMap (c : (relativeChains A).homology (n+2))
    (a b : ℕ) (hab : a+b = n+2) :
    (supportCochains p V Aᶜ).homology a ⟶ (localChains p hp.out V).homology b :=
  ModuleCat.ofHom ((supportCapHomology p V Aᶜ a b).flip (boundaryCapClass A n c a b hab))

/-- For each compact support in the interior, the literal relative cap agrees with the
interior compact cap followed by actual local-chain inclusion. -/
theorem boundaryCapMap_support
    (c : (relativeChains A).homology (n+2))
    (hc : ∀ x (hx : x ∉ A), homologyMap (boundaryPointMap A x hx) (n+2) c =
      homologyMap (RationalRelativeExcision.pointExcisionMap x Aᶜ hx) (n+2)
        (o.generator ⟨x,hx⟩))
    (K : Set B) (hK : IsCompact K) (hKA : K ⊆ Aᶜ)
    (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportMap p V K Aᶜ hKA) a ≫ boundaryCapMap p V A n c a b hab =
      homologyMap (supportToOpen p V Aᶜ K) a ≫
        compactCapAt (restrictedProjection p Aᶜ) V n e o
          ⟨Subtype.val ⁻¹' K, interiorCompact A hA K hK hKA⟩ a b hab ≫
            homologyMap (openLocalChainMap p V Aᶜ) b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change supportCapHomology p V Aᶜ a b
    (homologyMap (supportMap p V K Aᶜ hKA) a x) (boundaryCapClass A n c a b hab) =
      homologyMap (openLocalChainMap p V Aᶜ) b
        (supportCapHomology (restrictedProjection p Aᶜ) V (Subtype.val ⁻¹' K) a b
          (homologyMap (supportToOpen p V Aᶜ K) a x)
          (capFundamentalClass (B := TopCat.of ↥Aᶜ) n e o
            ⟨Subtype.val ⁻¹' K, interiorCompact A hA K hK hKA⟩ a b hab))
  rw [supportCapHomology_enlargement,
    boundaryCapClass_restriction A hA n e o c hc K hK hKA a b hab]
  exact (supportCapHomology_toOpen p V Aᶜ K a b x
    (capFundamentalClass (B := TopCat.of ↥Aᶜ) n e o
      ⟨Subtype.val ⁻¹' K, interiorCompact A hA K hK hKA⟩ a b hab)).symm

end TernaryPoly.SingularLocalBoundaryCap
