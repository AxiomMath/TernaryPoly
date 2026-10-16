module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapBetweenHomology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapOpen

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory HomologicalComplex TopologicalSpace
open SingularLocalSupport EquivariantSingularSmall RationalManifoldCompact RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (D U : Opens B) [ChartedSpace H D] [ChartedSpace H U] (hDU : D ≤ U)

/-- The degree-adjusted genuine fundamental classes are compatible under nested open inclusion. -/
theorem capFundamentalClass_between (K : Compacts B) (hKD : (K : Set B) ⊆ D)
    (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (openSupportMap D U hDU (K : Set B)) (a+b)
      (capFundamentalClass (B := TopCat.of D) n e (openOrientation n e o D) (compactWithinOpen D K hKD) a b hab) =
    capFundamentalClass (B := TopCat.of U) n e (openOrientation n e o U)
      (compactWithinOpen U K (hKD.trans hDU)) a b hab := by
  unfold capFundamentalClass
  change (homologyDegreeChange _ (n+2) (a+b) hab.symm ≫
    homologyMap (openSupportMap D U hDU (K : Set B)) (a+b)) _ = _
  rw [homologyDegreeChange_natural]
  exact congrArg (fun c => homologyDegreeChange
    (supportChains ((Subtype.val : U → B) ⁻¹' (K : Set B))) (n+2) (a+b) hab.symm c)
    (compactFundamentalClass_between n e o D U hDU K hKD)

variable [IsCancelSMul G E]

/-- Actual fixed-support cap commutes with the direct inclusion between nested open coverings. -/
theorem compactCapAt_between (K : Compacts B) (hKD : (K : Set B) ⊆ D)
    (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportBetweenRestriction p V D U hDU (K : Set B)) a ≫
      compactCapAt (restrictedProjection p D) V n e (openOrientation n e o D)
        (compactWithinOpen D K hKD) a b hab ≫ homologyMap (openLocalChainMapBetween p V D U hDU) b =
    compactCapAt (restrictedProjection p U) V n e (openOrientation n e o U)
      (compactWithinOpen U K (hKD.trans hDU)) a b hab := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (supportCapHomology_between p V D U hDU (K : Set B) a b x
    (capFundamentalClass (B := TopCat.of D) n e (openOrientation n e o D) (compactWithinOpen D K hKD) a b hab)).trans
    (congrArg (fun c => supportCapHomology (restrictedProjection p U) V
      ((Subtype.val : U → B) ⁻¹' (K : Set B)) a b x c)
      (capFundamentalClass_between n e o D U hDU K hKD a b hab))

omit [ChartedSpace H B] in
/-- Cap on the actual open class represented by an ambient support is the corresponding
fixed-support cap after literal support restriction. -/
theorem classInOpen_capMap (oD : Orientation (n+2) D) (K : Compacts B) (hKD : (K : Set B) ⊆ D)
    (a b : ℕ) (hab : a+b = n+2) :
    classInOpen p V D K hKD a ≫ compactCapMap (restrictedProjection p D) V n e oD a b hab =
    homologyMap (supportToOpen p V D (K : Set B)) a ≫
      compactCapAt (restrictedProjection p D) V n e oD (compactWithinOpen D K hKD) a b hab := by
  unfold classInOpen
  erw [Category.assoc,compactCapMap_classMap]
  rfl

/-- The actual compact cap intertwines common-ambient open extension with the literal local-chain
inclusion, for the genuine orientations induced from the common ambient manifold. -/
theorem compactCapMap_between (a b : ℕ) (hab : a+b = n+2) :
    openExtensionBetween p V D U hDU a ≫
      compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) a b hab =
    compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) a b hab ≫
      homologyMap (openLocalChainMapBetween p V D U hDU) b := by
  have aux (K : Compacts B) (hKD : (K : Set B) ⊆ D) :
      classInOpen p V D K hKD a ≫ (openExtensionBetween p V D U hDU a ≫
        compactCapMap (restrictedProjection p U) V n e (openOrientation n e o U) a b hab) =
      classInOpen p V D K hKD a ≫ (compactCapMap (restrictedProjection p D) V n e
        (openOrientation n e o D) a b hab ≫ homologyMap (openLocalChainMapBetween p V D U hDU) b) := by
    rw [← Category.assoc,classInOpen_between,classInOpen_capMap]
    rw [← compactCapAt_between p V n e o D U hDU K hKD a b hab]
    have hs := congrArg (fun f => homologyMap f a) (supportToOpen_between p V D U hDU (K : Set B))
    rw [homologyMap_comp] at hs
    erw [← Category.assoc (homologyMap (supportToOpen p V U (K : Set B)) a)
      (homologyMap (supportBetweenRestriction p V D U hDU (K : Set B)) a),hs]
    rw [← Category.assoc,classInOpen_capMap]
    exact (Category.assoc _ _ _).symm
  apply compactCohomology_hom_ext
  intro K
  apply (cancel_epi (openSupportIso p V D K a).hom).mp
  have h := aux (openCompactImage D K) (openCompactImage_subset D K)
  rw [classInOpen_image] at h
  simpa only [Category.assoc] using h

end TernaryPoly.SingularLocalCompactCap
