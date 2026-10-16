module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapOpenHomology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionBetween
public import TernaryPeriodPolynomials.Topology.Rational.Manifold.OpenOrientation

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open SingularLocalSupport EquivariantSingularSmall RationalManifoldCompact
open RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (D : Opens B) [ChartedSpace H D] (oD : Orientation (n+2) D)

/-- Equality transport of cap degree preserves actual open-support fundamental-class naturality. -/
theorem capFundamentalClass_open (hcompat : OpenOrientationCompatible n o D oD)
    (K : Compacts B) (hKD : (K : Set B) ⊆ D) (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (RationalLocalOrientation.supportExcisionMap (K : Set B) (D : Set B)) (a+b)
      (capFundamentalClass (B := TopCat.of D) n e oD (compactWithinOpen D K hKD) a b hab) =
      capFundamentalClass (B := B) n e o K a b hab := by
  unfold capFundamentalClass
  change (homologyDegreeChange _ (n+2) (a+b) hab.symm ≫
    homologyMap (RationalLocalOrientation.supportExcisionMap (K : Set B) (D : Set B)) (a+b)) _ = _
  rw [homologyDegreeChange_natural]
  change homologyDegreeChange _ (n+2) (a+b) hab.symm
    (homologyMap (RationalLocalOrientation.supportExcisionMap (K : Set B) (D : Set B)) (n+2)
      (compactFundamentalClass n e oD _ _)) = _
  exact congrArg (fun c => homologyDegreeChange (supportChains (K : Set B)) (n+2) (a+b) hab.symm c)
    (compactFundamentalClass_open n e o D oD hcompat K hKD)

variable [IsCancelSMul G E]

/-- Genuine fixed-support cap is natural for oriented open inclusion. -/
theorem compactCapAt_open (hcompat : OpenOrientationCompatible n o D oD)
    (K : Compacts B) (hKD : (K : Set B) ⊆ D) (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportToOpen p V D (K : Set B)) a ≫
      compactCapAt (restrictedProjection p D) V n e oD (compactWithinOpen D K hKD) a b hab ≫
        homologyMap (openLocalChainMap p V D) b = compactCapAt p V n e o K a b hab := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change homologyMap (openLocalChainMap p V D) b
    (supportCapHomology (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' (K : Set B)) a b
      (homologyMap (supportToOpen p V D (K : Set B)) a x)
      (capFundamentalClass (B := TopCat.of D) n e oD (compactWithinOpen D K hKD) a b hab)) =
    supportCapHomology p V (K : Set B) a b x (capFundamentalClass (B := B) n e o K a b hab)
  exact (supportCapHomology_toOpen p V D (K : Set B) a b x
    (capFundamentalClass (B := TopCat.of D) n e oD (compactWithinOpen D K hKD) a b hab)).trans
    (congrArg (fun c => supportCapHomology p V (K : Set B) a b x c)
      (capFundamentalClass_open n e o D oD hcompat K hKD a b hab))

/-- The genuine compact-support cap commutes with open extension for any compatible orientations. -/
theorem compactCapMap_open (hcompat : OpenOrientationCompatible n o D oD)
    (a b : ℕ) (hab : a+b = n+2) :
    openExtension p V D a ≫ compactCapMap p V n e o a b hab =
      compactCapMap (restrictedProjection p D) V n e oD a b hab ≫
        homologyMap (openLocalChainMap p V D) b := by
  have aux (K : Compacts B) (hKD : (K : Set B) ⊆ D) :
      classInOpen p V D K hKD a ≫ (openExtension p V D a ≫ compactCapMap p V n e o a b hab) =
      classInOpen p V D K hKD a ≫
        (compactCapMap (restrictedProjection p D) V n e oD a b hab ≫
          homologyMap (openLocalChainMap p V D) b) := by
    rw [← Category.assoc,classInOpen_extension,compactCapMap_classMap]
    unfold classInOpen
    erw [Category.assoc,← Category.assoc (compactClassMap _ _ _ _) _,compactCapMap_classMap]
    exact (compactCapAt_open p V n e o D oD hcompat K hKD a b hab).symm
  apply compactCohomology_hom_ext
  intro K
  apply (cancel_epi (openSupportIso p V D K a).hom).mp
  have h := aux (openCompactImage D K) (openCompactImage_subset D K)
  rw [classInOpen_image] at h
  simpa only [Category.assoc] using h

/-- The canonical orientation restricted from the ambient manifold gives unconditional
naturality of the actual compact-support cap under open extension. -/
theorem compactCapMap_open_canonical (a b : ℕ) (hab : a+b = n+2) :
    openExtension p V D a ≫ compactCapMap p V n e o a b hab =
      compactCapMap (restrictedProjection p D) V n e (openOrientation n e o D) a b hab ≫
        homologyMap (openLocalChainMap p V D) b :=
  compactCapMap_open p V n e o D (openOrientation n e o D)
    (openOrientation_compatible n e o D) a b hab

end TernaryPoly.SingularLocalCompactCap
