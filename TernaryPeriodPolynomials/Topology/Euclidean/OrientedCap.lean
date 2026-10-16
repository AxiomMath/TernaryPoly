module

public import TernaryPeriodPolynomials.Topology.Euclidean.OrientationScalar
public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapIsomorphism

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanOrientationScalar
open CategoryTheory HomologicalComplex TopologicalSpace
open RationalLocalOrientation RationalManifoldCompact
open EuclideanLocalHomology EuclideanCompactClasses EuclideanCompactCap
open SingularLocalConstant SingularLocalSupport SingularLocalCompactCap

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))
local notation "X" => TopCat.of E
local instance orientedAction : MulAction Unit X := identityAction X
local instance orientedContinuous : ContinuousConstSMul Unit X := identityContinuousAction X
local instance orientedFree : IsCancelSMul Unit X := identityFreeAction X
local instance orientedCover : Fact (IsQuotientCoveringMap (𝟙 X) Unit) := ⟨identityCover X⟩

/-- An arbitrary genuine Euclidean orientation scales every actual compact fundamental class
by its single nonzero origin coordinate. -/
theorem compactFundamentalClass_orientation (o : Orientation (n+2) E) (K : Set E) (hK : IsCompact K) :
    compactFundamentalClass n (Homeomorph.refl E) o K hK =
      orientationScalar n o • compactFundamentalClass n (Homeomorph.refl E) (euclideanOrientation n) K hK := by
  symm
  apply compactFundamentalClass_unique n (Homeomorph.refl E) o K hK
  intro x hx
  rw [map_smul,compactFundamentalClass_at_point]
  exact (orientation_generator n o x).symm

/-- Degree transport retains the same actual orientation scalar for cap classes. -/
theorem capFundamentalClass_orientation (o : Orientation (n+2) E) (K : Compacts X)
    (a b : ℕ) (hab : a+b = n+2) :
    capFundamentalClass (B := X) n (Homeomorph.refl E) o K a b hab =
      orientationScalar n o • capFundamentalClass (B := X) n (Homeomorph.refl E) (euclideanOrientation n) K a b hab := by
  unfold capFundamentalClass
  rw [compactFundamentalClass_orientation,map_smul]

/-- The genuine compact-support cap map changes by exactly the orientation scalar. -/
theorem compactCapMap_orientation_apply (V : ModuleCat.{0} ℚ) (o : Orientation (n+2) E)
    (a b : ℕ) (hab : a+b = n+2) (c : compactCohomology (𝟙 X) (constantRep V) a) :
    compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) o a b hab c =
      orientationScalar n o • compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) (euclideanOrientation n) a b hab c := by
  obtain ⟨K,x,rfl⟩ := compactClass_exists_rep (𝟙 X) (constantRep V) a c
  rw [compactCapMap_apply,compactCapMap_apply,capFundamentalClass_orientation,map_smul]

/-- Actual Euclidean compact-support cap is an isomorphism for every genuine homological
orientation, every rational module, and every pair of complementary nonnegative degrees. -/
theorem orientedCompactCap_isIso (V : ModuleCat.{0} ℚ) (o : Orientation (n+2) E)
    (a b : ℕ) (hab : a+b = n+2) :
    IsIso (compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) o a b hab) := by
  let e := (compactCapIso n V a b hab).toLinearEquiv ≪≫ₗ
    LinearEquiv.smulOfNeZero ℚ ((coveringLocalChains (𝟙 X) (constantRep V)).homology b)
      (orientationScalar n o) (orientationScalar_ne_zero n o)
  have he : compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) o a b hab = e.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact compactCapMap_orientation_apply n V o a b hab c
  rw [he]
  infer_instance

end TernaryPoly.EuclideanOrientationScalar
