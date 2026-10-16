module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityHomeomorphSupportCap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphCap

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open RationalLocalOrientation RationalManifoldCompact
open SingularLocalCapHomeomorph SingularLocalHomology

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  {p : E ⟶ B} {p' : E' ⟶ B'}
  [hp : Fact (IsQuotientCoveringMap p G)] [hp' : Fact (IsQuotientCoveringMap p' G)]
  [IsCancelSMul G E] [IsCancelSMul G E']
  [T2Space B] [T2Space B']
  {HX HY : Type} [TopologicalSpace HX] [TopologicalSpace HY]
  [ChartedSpace HX B] [ChartedSpace HY B']
  (h : CoverHomeomorph (G := G) p p') (V : Rep.{0} ℚ G) (n : ℕ)
  (eX : HX ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (eY : HY ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
  (oX : Orientation (n+2) B) (oY : Orientation (n+2) B')

/-- At every genuine compact support, cap commutes with actual homeomorphism transport. -/
theorem coveringCompactCapAt_natural (ho : OrientationCompatible h.base n oX oY)
    (K : Compacts B') (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (coveringSupportIso h V K).hom a ≫
      compactCapAt p V n eX oX (compactOrderIso h.base K) a b hab ≫
        homologyMap (coveringChainMap h V) b =
      compactCapAt p' V n eY oY K a b hab := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change homologyMap (coveringChainMap h V) b
    (supportCapHomology p V (h.base ⁻¹' (K : Set B')) a b
      (homologyMap (coveringSupportIso h V K).hom a φ)
      (capFundamentalClass (B := B) n eX oX (compactOrderIso h.base K) a b hab)) =
    supportCapHomology p' V K a b φ
      (capFundamentalClass (B := B') n eY oY K a b hab)
  exact (coveringSupportCapHomology_natural h V (K : Set B') a b φ
    (capFundamentalClass (B := B) n eX oX (compactOrderIso h.base K) a b hab)).trans
    (congrArg (fun c => supportCapHomology p' V (K : Set B') a b φ c)
      (capFundamentalClass_transport h.base n eX eY oX oY ho K a b hab))

/-- The literal compact cap maps commute with actual homeomorphism compact-cohomology
pullback and actual local-homology pushforward. -/
theorem coveringCompactCapMap_natural (ho : OrientationCompatible h.base n oX oY)
    (a b : ℕ) (hab : a+b = n+2) :
    (coveringCompactIso h V a).hom ≫ compactCapMap p V n eX oX a b hab ≫
      (coveringHomologyIso h V b).hom = compactCapMap p' V n eY oY a b hab := by
  apply colimit.hom_ext
  intro K
  change compactClassMap p' V K a ≫ _ =
    compactClassMap p' V K a ≫ _
  erw [← Category.assoc,coveringCompactIso_classMap,Category.assoc,
    ← Category.assoc (compactClassMap _ _ _ _),compactCapMap_classMap,
    compactCapMap_classMap]
  exact coveringCompactCapAt_natural h V n eX eY oX oY ho K a b hab

/-- Actual compact cap isomorphisms transport forward along a compatible homeomorphism. -/
theorem coveringCompactCapMap_isIso (ho : OrientationCompatible h.base n oX oY)
    (a b : ℕ) (hab : a+b = n+2)
    [IsIso (compactCapMap p V n eX oX a b hab)] :
    IsIso (compactCapMap p' V n eY oY a b hab) := by
  rw [← coveringCompactCapMap_natural h V n eX eY oX oY ho a b hab]
  infer_instance

/-- The actual pulled-back orientation gives the literal compact-cap homeomorphism square. -/
theorem coveringCompactCapMap_pullback (a b : ℕ) (hab : a+b = n+2) :
    (coveringCompactIso h V a).hom ≫
      compactCapMap p V n eX (Orientation.pullback h.base (n+2) oY) a b hab ≫
        (coveringHomologyIso h V b).hom = compactCapMap p' V n eY oY a b hab :=
  coveringCompactCapMap_natural h V n eX eY (Orientation.pullback h.base (n+2) oY) oY
    (pullbackOrientation_compatible h.base n oY) a b hab

end TernaryPoly.SingularLocalCompactDuality
