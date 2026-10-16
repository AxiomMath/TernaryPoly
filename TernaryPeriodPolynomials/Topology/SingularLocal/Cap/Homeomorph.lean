module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphCap
public import TernaryPeriodPolynomials.Topology.Euclidean.OrientedCap

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory HomologicalComplex
open SingularLocalConstant SingularLocalCompactCap SingularLocalSupport
open RationalLocalOrientation

variable {X Y : TopCat.{0}} (h : X ≃ₜ Y) (V : ModuleCat.{0} ℚ)

/-- The actual homology transport isomorphism has exactly localSpaceMap as its induced map. -/
theorem homologyIso_hom (b : ℕ) :
    (homologyIso h V b).hom = homologyMap (chainPushforward h V) b := rfl

/-- The compact-cohomology comparison retains the actual pullback on every represented class. -/
theorem compactCohomologyIso_apply (a : ℕ) (K : TopologicalSpace.Compacts Y)
    (φ : (supportCochains (𝟙 Y) (constantRep V) K).homology a) :
    (compactCohomologyIso h V a).hom (compactClassMap (𝟙 Y) (constantRep V) K a φ) =
      compactClassMap (𝟙 X) (constantRep V) (compactOrderIso h K) a
        (homologyMap (supportCochainIso h V K).hom a φ) :=
  congrArg (fun f => f φ) (compactCohomologyIso_classMap h V a K)

variable [T2Space X] {H : Type} [TopologicalSpace H] [ChartedSpace H X]
  (n : ℕ) (eX : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
  (e : X ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) X)

include e

/-- Every space homeomorphic to Euclidean space has actual constant-coefficient compact
cap duality for every genuine orientation and arbitrary rational coefficient module. -/
theorem homeomorphicEuclidean_isIso (a b : ℕ) (hab : a+b = n+2) :
    IsIso (compactCapMap (𝟙 X) (constantRep V) n eX o a b hab) := by
  let oE := Orientation.pullback e.symm (n+2) o
  have hi := EuclideanOrientationScalar.orientedCompactCap_isIso n V oE a b hab
  exact compactCapMap_isIso (X := TopCat.of (EuclideanSpace ℝ (Fin (n+2)))) (Y := X)
    e.symm V n (Homeomorph.refl _) eX oE o
    (pullbackOrientation_compatible e.symm n o) a b hab

/-- The resulting duality isomorphism uses the actual given-orientation compact cap map. -/
def homeomorphicEuclideanIso (a b : ℕ) (hab : a+b = n+2) :
    compactCohomology (𝟙 X) (constantRep V) a ≅
      (coveringLocalChains (𝟙 X) (constantRep V)).homology b := by
  have := homeomorphicEuclidean_isIso V n eX e o a b hab
  exact asIso (compactCapMap (𝟙 X) (constantRep V) n eX o a b hab)

/-- Literal forward-map identity for arbitrary-orientation homeomorphic Euclidean duality. -/
theorem homeomorphicEuclideanIso_hom (a b : ℕ) (hab : a+b = n+2) :
    (homeomorphicEuclideanIso V n eX e o a b hab).hom =
      compactCapMap (𝟙 X) (constantRep V) n eX o a b hab := rfl

end TernaryPoly.SingularLocalCapHomeomorph
