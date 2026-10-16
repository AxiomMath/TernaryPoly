module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapSupportHomology
public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.Classes

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalSupport SingularLocalCapNormalization
open EuclideanConvexLocal EuclideanLocalHomology EuclideanCompactClasses

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))
local notation "X" => TopCat.of E
local instance convexEuclideanAction : MulAction Unit X := identityAction X
local instance convexEuclideanContinuousAction : ContinuousConstSMul Unit X := identityContinuousAction X
local instance convexEuclideanFreeAction : IsCancelSMul Unit X := identityFreeAction X
local instance convexEuclideanCoverFact : Fact (IsQuotientCoveringMap (𝟙 X) Unit) := ⟨identityCover X⟩

/-- Actual cohomology supported on a compact convex Euclidean set vanishes outside
the top degree, for every rational coefficient module. -/
theorem convexSupportCohomology_isZero (V : ModuleCat.{0} ℚ) (K : Set E)
    (hK : IsCompact K) (hconv : Convex ℝ K) (a : ℕ) (ha : a ≠ n+2) :
    IsZero ((supportCochains (𝟙 X) (constantRep V) K).homology a) :=
  supportCohomology_isZero X V K a (supportHomology_isZero_of_ne n a K hK hconv ha)

/-- The fixed arbitrary-compact and compact-convex generators agree by actual point detection. -/
theorem compactGenerator_eq_convex (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) :
    compactGenerator n K hK = convexGenerator n K hK hconv hne :=
  convexGenerator_unique n K hK hconv hne _
    (compactGenerator_at_point n K hK hne.some hne.some_mem)

/-- The actual point coordinate identifies top relative homology with ℚ. -/
def convexHomologyCoordinate (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) :
    (RationalManifoldCompact.supportChains K).homology (n+2) ≃ₗ[ℚ] ℚ :=
  ((pointHomologyIso K hK hconv hne.some hne.some_mem (n+2)) ≪≫
    localTopAtIso n hne.some).toLinearEquiv

/-- The actual inverse coordinate of one is the fixed compact fundamental generator. -/
theorem convexHomologyCoordinate_generator (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) :
    (convexHomologyCoordinate n K hK hconv hne).symm 1 = compactGenerator n K hK := by
  rw [compactGenerator_eq_convex n K hK hconv hne]
  rfl

/-- Literal evaluation on the fixed compact generator is an isomorphism for every
nonempty compact convex support and arbitrary rational coefficients. -/
def convexSupportEvaluationEquiv (V : ModuleCat.{0} ℚ) (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) :
    (supportCochains (𝟙 X) (constantRep V) K).homology (n+2) ≃ₗ[ℚ] V :=
  supportHomologyEvaluationEquiv X V K (n+2) ≪≫ₗ
    LinearEquiv.arrowCongr (convexHomologyCoordinate n K hK hconv hne) (LinearEquiv.refl ℚ V) ≪≫ₗ
      LinearMap.ringLmapEquivSelf ℚ ℚ V

/-- The convex-support isomorphism is exactly evaluation on the fixed compact generator,
using the independent evaluation pairing. -/
theorem convexSupportEvaluationEquiv_apply (V : ModuleCat.{0} ℚ) (K : Set E) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (h : (supportCochains (𝟙 X) (constantRep V) K).homology (n+2)) :
    convexSupportEvaluationEquiv n V K hK hconv hne h =
      supportHomologyEvaluation X V K (n+2) h (compactGenerator n K hK) := by
  change supportHomologyEvaluationEquiv X V K (n+2) h
    ((convexHomologyCoordinate n K hK hconv hne).symm 1) = _
  rw [convexHomologyCoordinate_generator, supportHomologyEvaluationEquiv_eq]

end TernaryPoly.EuclideanCompactCap
