module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphCompactIso
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphSupportCap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphFundamental

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open RationalLocalOrientation RationalManifoldCompact

variable {X Y : TopCat.{0}} [T2Space X] [T2Space Y]
  {HX HY : Type} [TopologicalSpace HX] [TopologicalSpace HY]
  [ChartedSpace HX X] [ChartedSpace HY Y]
  (h : X ≃ₜ Y) (V : ModuleCat.{0} ℚ) (n : ℕ)
  (eX : HX ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (eY : HY ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
  (oX : Orientation (n+2) X) (oY : Orientation (n+2) Y)

/-- Degree transport preserves actual homeomorphism naturality of compact fundamental classes. -/
theorem capFundamentalClass_transport (ho : OrientationCompatible h n oX oY)
    (K : Compacts Y) (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportPullbackIso h (K : Set Y)).hom (a+b)
      (capFundamentalClass (B := X) n eX oX (compactOrderIso h K) a b hab) =
      capFundamentalClass (B := Y) n eY oY K a b hab := by
  unfold capFundamentalClass
  change (homologyDegreeChange _ (n+2) (a+b) hab.symm ≫
    homologyMap (supportPullbackIso h (K : Set Y)).hom (a+b)) _ = _
  rw [homologyDegreeChange_natural]
  change homologyDegreeChange _ (n+2) (a+b) hab.symm
    (homologyMap (supportPullbackIso h (K : Set Y)).hom (n+2)
      (compactFundamentalClass n eX oX (h ⁻¹' (K : Set Y)) _)) = _
  rw [compactFundamentalClass_transport h n eX eY oX oY ho]

/-- At every genuine compact support, cap commutes with actual homeomorphism transport. -/
theorem compactCapAt_natural (ho : OrientationCompatible h n oX oY)
    (K : Compacts Y) (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportCochainIso h V K).hom a ≫
      compactCapAt (𝟙 X) (constantRep V) n eX oX (compactOrderIso h K) a b hab ≫
        homologyMap (chainPushforward h V) b =
      compactCapAt (𝟙 Y) (constantRep V) n eY oY K a b hab := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change homologyMap (chainPushforward h V) b
    (supportCapHomology (𝟙 X) (constantRep V) (h ⁻¹' (K : Set Y)) a b
      (homologyMap (supportCochainIso h V K).hom a φ)
      (capFundamentalClass (B := X) n eX oX (compactOrderIso h K) a b hab)) =
    supportCapHomology (𝟙 Y) (constantRep V) K a b φ
      (capFundamentalClass (B := Y) n eY oY K a b hab)
  exact (supportCapHomology_natural h V (K : Set Y) a b φ
    (capFundamentalClass (B := X) n eX oX (compactOrderIso h K) a b hab)).trans
    (congrArg (fun c => supportCapHomology (𝟙 Y) (constantRep V) (K : Set Y) a b φ c)
      (capFundamentalClass_transport h n eX eY oX oY ho K a b hab))

/-- The literal compact cap maps commute with actual homeomorphism compact-cohomology
pullback and actual local-homology pushforward. -/
theorem compactCapMap_natural (ho : OrientationCompatible h n oX oY)
    (a b : ℕ) (hab : a+b = n+2) :
    (compactCohomologyIso h V a).hom ≫ compactCapMap (𝟙 X) (constantRep V) n eX oX a b hab ≫
      (homologyIso h V b).hom = compactCapMap (𝟙 Y) (constantRep V) n eY oY a b hab := by
  apply colimit.hom_ext
  intro K
  change compactClassMap (𝟙 Y) (constantRep V) K a ≫ _ =
    compactClassMap (𝟙 Y) (constantRep V) K a ≫ _
  erw [← Category.assoc,compactCohomologyIso_classMap,Category.assoc,
    ← Category.assoc (compactClassMap _ _ _ _),compactCapMap_classMap,
    compactCapMap_classMap]
  exact compactCapAt_natural h V n eX eY oX oY ho K a b hab

/-- Actual compact cap isomorphisms transport forward along a compatible homeomorphism. -/
theorem compactCapMap_isIso (ho : OrientationCompatible h n oX oY)
    (a b : ℕ) (hab : a+b = n+2)
    [IsIso (compactCapMap (𝟙 X) (constantRep V) n eX oX a b hab)] :
    IsIso (compactCapMap (𝟙 Y) (constantRep V) n eY oY a b hab) := by
  rw [← compactCapMap_natural h V n eX eY oX oY ho a b hab]
  infer_instance

/-- The actual pulled-back orientation gives unconditional compact fundamental-class transport. -/
theorem compactFundamentalClass_pullback (K : Set Y) (hK : IsCompact K) :
    homologyMap (supportPullbackIso h K).hom (n+2)
      (compactFundamentalClass n eX (Orientation.pullback h (n+2) oY)
        (h ⁻¹' K) (h.isCompact_preimage.mpr hK)) =
      compactFundamentalClass n eY oY K hK :=
  compactFundamentalClass_transport h n eX eY (Orientation.pullback h (n+2) oY) oY
    (pullbackOrientation_compatible h n oY) K hK

/-- The actual pulled-back orientation gives the literal compact-cap homeomorphism square. -/
theorem compactCapMap_pullback (a b : ℕ) (hab : a+b = n+2) :
    (compactCohomologyIso h V a).hom ≫
      compactCapMap (𝟙 X) (constantRep V) n eX (Orientation.pullback h (n+2) oY) a b hab ≫
        (homologyIso h V b).hom = compactCapMap (𝟙 Y) (constantRep V) n eY oY a b hab :=
  compactCapMap_natural h V n eX eY (Orientation.pullback h (n+2) oY) oY
    (pullbackOrientation_compatible h n oY) a b hab

end TernaryPoly.SingularLocalCapHomeomorph
