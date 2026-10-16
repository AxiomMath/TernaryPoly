module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.OpenOrientation

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory HomologicalComplex TopologicalSpace
open RationalLocalOrientation RationalLocalChartHomology RationalRelativeExcision RationalRelativeSingular

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- Literal inclusion between two opens in a common ambient space. -/
def openInclusion (D U : Opens X) (hDU : D ≤ U) : C(D,U) :=
  ⟨fun x => ⟨x.val,hDU x.property⟩,continuous_subtype_val.subtype_mk _⟩

/-- The actual point-relative chain map of a nested open inclusion. -/
def openPointMap (D U : Opens X) (hDU : D ≤ U) (x : D) :
    localChains x ⟶ localChains (openInclusion D U hDU x) :=
  relativeMap (openInclusion D U hDU) {x}ᶜ {openInclusion D U hDU x}ᶜ (by
    intro y hy h
    apply hy
    apply Subtype.ext
    exact congrArg (fun u : U => u.val)
      (show openInclusion D U hDU y = openInclusion D U hDU x from h))

omit [T2Space X] in
/-- The literal nested point map composes to the ambient point-excision map. -/
theorem openPointMap_ambient (D U : Opens X) (hDU : D ≤ U) (x : D) :
    openPointMap D U hDU x ≫ pointExcisionMap x.val (U : Set X) (hDU x.property) =
      pointExcisionMap x.val (D : Set X) x.property := by
  rw [pointExcisionMap_eq_relativeMap,pointExcisionMap_eq_relativeMap]
  unfold openPointMap
  erw [relativeMap_comp]
  rfl

variable {H : Type} [TopologicalSpace H] [ChartedSpace H X]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) X)

/-- Canonically restricted actual point orientations agree under literal nested open inclusion. -/
theorem openOrientation_between (D U : Opens X) (hDU : D ≤ U) (x : D) :
    homologyMap (openPointMap D U hDU x) (n+2) ((openOrientation n e o D).generator x) =
      (openOrientation n e o U).generator (openInclusion D U hDU x) := by
  apply (ModuleCat.mono_iff_injective
    (pointLocalHomologyIso x.val U (hDU x.property) (n+2)).hom).mp inferInstance
  change (homologyMap (openPointMap D U hDU x) (n+2) ≫
    homologyMap (pointExcisionMap x.val (U : Set X) (hDU x.property)) (n+2))
      (openOrientationGenerator n o D x) = _
  erw [← homologyMap_comp,openPointMap_ambient,openOrientationGenerator_map]
  exact (openOrientationGenerator_map n o U (openInclusion D U hDU x)).symm

end TernaryPoly.RationalManifoldCompact
