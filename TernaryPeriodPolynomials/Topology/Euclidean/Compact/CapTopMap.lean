module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapCofinality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMap

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalSupport SingularLocalCompactCap SingularLocalCapNormalization
open EuclideanCompactClasses EuclideanLocalHomology
variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))
local notation "X" => TopCat.of E
local instance topEuclideanAction : MulAction Unit X := identityAction X
local instance topEuclideanContinuousAction : ContinuousConstSMul Unit X := identityContinuousAction X
local instance topEuclideanFreeAction : IsCancelSMul Unit X := identityFreeAction X
local instance topEuclideanCoverFact : Fact (IsQuotientCoveringMap (𝟙 X) Unit) := ⟨identityCover X⟩

/-- The actual cap fundamental class in top degree is the fixed compact Euclidean class. -/
theorem top_capFundamentalClass (K : Compacts X) :
    capFundamentalClass n (Homeomorph.refl E) (euclideanOrientation n) K (n+2) 0 (by omega) =
      compactGenerator n K K.isCompact := by
  change RationalManifoldCompact.compactFundamentalClass n (Homeomorph.refl E)
    (euclideanOrientation n) K K.isCompact = _
  exact euclidean_compactFundamentalClass n K K.isCompact

/-- The actual compact-support cap map followed by the actual constant-coefficient augmentation. -/
def topCapEvaluation (V : ModuleCat.{0} ℚ) :
    compactCohomology (𝟙 X) (constantRep V) (n+2) →ₗ[ℚ] V :=
  (compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E) (euclideanOrientation n)
    (n+2) 0 (by omega) ≫ augmentation X V).hom

/-- On every genuine compact-support representative the actual top cap-augmentation
map is the independent literal evaluation on the fixed compact Euclidean generator. -/
theorem topCapEvaluation_class (V : ModuleCat.{0} ℚ) (K : Compacts X)
    (h : (supportCochains (𝟙 X) (constantRep V) (K : Set X)).homology (n+2)) :
    topCapEvaluation n V (compactClassMap (𝟙 X) (constantRep V) K (n+2) h) =
      supportHomologyEvaluation X V K (n+2) h (compactGenerator n K K.isCompact) := by
  change augmentation X V (compactCapMap (𝟙 X) (constantRep V) n (Homeomorph.refl E)
    (euclideanOrientation n) (n+2) 0 _ (compactClassMap (𝟙 X) (constantRep V) K (n+2) h)) = _
  rw [compactCapMap_apply, top_capFundamentalClass]
  exact supportCapHomology_evaluation_classes X V K (n+2) h _

/-- On nonempty compact convex supports, the actual top cap-augmentation is the
proved literal evaluation isomorphism. -/
theorem topCapEvaluation_convex (V : ModuleCat.{0} ℚ) (K : Compacts X)
    (hconv : Convex ℝ (K : Set E)) (hne : (K : Set E).Nonempty)
    (h : (supportCochains (𝟙 X) (constantRep V) (K : Set X)).homology (n+2)) :
    topCapEvaluation n V (compactClassMap (𝟙 X) (constantRep V) K (n+2) h) =
      convexSupportEvaluationEquiv n V K K.isCompact hconv hne h := by
  rw [topCapEvaluation_class, convexSupportEvaluationEquiv_apply]

end TernaryPoly.EuclideanCompactCap
