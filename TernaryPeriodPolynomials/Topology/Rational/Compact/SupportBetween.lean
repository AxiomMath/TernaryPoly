module

public import TernaryPeriodPolynomials.Topology.Rational.OpenOrientationNaturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionSupport

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open RationalLocalOrientation RationalLocalChartHomology RationalRelativeExcision RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- Literal relative-chain pushforward of support through a nested open inclusion. -/
def openSupportMap (D U : Opens X) (hDU : D ≤ U) (K : Set X) :
    supportChains ((Subtype.val : D → X) ⁻¹' K) ⟶ supportChains ((Subtype.val : U → X) ⁻¹' K) :=
  relativeMap (openInclusion D U hDU) _ _ (fun _ h => h)

/-- The actual nested support map retains its scalar chain representative. -/
theorem openSupportMap_projection (D U : Opens X) (hDU : D ≤ U) (K : Set X) :
    cokernel.π (inclusion ((Subtype.val : D → X) ⁻¹' K)ᶜ) ≫ openSupportMap D U hDU K =
      RationalSingularAugmentation.chainMap (openInclusion D U hDU) ≫
        cokernel.π (inclusion ((Subtype.val : U → X) ⁻¹' K)ᶜ) := by
  simp only [openSupportMap,relativeMap,cokernel.map,cokernel.π_desc]

/-- Actual point restriction commutes with nested support pushforward. -/
theorem openSupportMap_point (D U : Opens X) (hDU : D ≤ U) (K : Set X) (x : D) (hx : x.val ∈ K) :
    openSupportMap D U hDU K ≫ supportPointMap ((Subtype.val : U → X) ⁻¹' K) (openInclusion D U hDU x) hx =
      supportPointMap ((Subtype.val : D → X) ⁻¹' K) x hx ≫ openPointMap D U hDU x := by
  unfold openSupportMap supportPointMap openPointMap
  erw [relativeMap_comp,relativeMap_comp]
  rfl

variable [T2Space X] {H : Type} [TopologicalSpace H] [ChartedSpace H X]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) X)
  (D U : Opens X) [ChartedSpace H D] [ChartedSpace H U] (hDU : D ≤ U)

/-- The genuine compact fundamental classes for canonical ambient restrictions agree under
literal nested open inclusion. -/
theorem compactFundamentalClass_between (K : Compacts X) (hKD : (K : Set X) ⊆ D) :
    homologyMap (openSupportMap D U hDU (K : Set X)) (n+2)
      (compactFundamentalClass n e (openOrientation n e o D) ((Subtype.val : D → X) ⁻¹' (K : Set X))
        (SingularLocalSupport.compactWithinOpen (B := TopCat.of X) D K hKD).isCompact) =
    compactFundamentalClass n e (openOrientation n e o U) ((Subtype.val : U → X) ⁻¹' (K : Set X))
      (SingularLocalSupport.compactWithinOpen (B := TopCat.of X) U K (hKD.trans hDU)).isCompact := by
  apply compactFundamentalClass_unique n e (openOrientation n e o U)
  intro x hx
  let y : D := ⟨x.val,hKD hx⟩
  have h := congrArg (fun f => homologyMap f (n+2)) (openSupportMap_point D U hDU (K : Set X) y hx)
  rw [homologyMap_comp,homologyMap_comp] at h
  change (homologyMap (openSupportMap D U hDU (K : Set X)) (n+2) ≫
    homologyMap (supportPointMap ((Subtype.val : U → X) ⁻¹' (K : Set X)) (openInclusion D U hDU y) hx) (n+2)) _ = _
  rw [h]
  change homologyMap (openPointMap D U hDU y) (n+2)
    (homologyMap (supportPointMap ((Subtype.val : D → X) ⁻¹' (K : Set X)) y hx) (n+2) _) = _
  exact (congrArg (fun c => homologyMap (openPointMap D U hDU y) (n+2) c)
    (compactFundamentalClass_at_point n e (openOrientation n e o D)
      ((Subtype.val : D → X) ⁻¹' (K : Set X))
      (SingularLocalSupport.compactWithinOpen (B := TopCat.of X) D K hKD).isCompact y hx)).trans
      (openOrientation_between n e o D U hDU y)

end TernaryPoly.RationalManifoldCompact
