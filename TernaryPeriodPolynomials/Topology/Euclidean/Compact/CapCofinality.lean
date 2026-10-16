module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapOrientation
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Representatives

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalSupport
variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))
local notation "X" => TopCat.of E
local instance cofinalEuclideanAction : MulAction Unit X := identityAction X
local instance cofinalEuclideanContinuousAction : ContinuousConstSMul Unit X := identityContinuousAction X
local instance cofinalEuclideanFreeAction : IsCancelSMul Unit X := identityFreeAction X
local instance cofinalEuclideanCoverFact : Fact (IsQuotientCoveringMap (𝟙 X) Unit) := ⟨identityCover X⟩

/-- Every actual compact Euclidean support is contained in a nonempty compact convex
closed ball centered at the origin. -/
theorem exists_compact_convex_enlargement (K : Compacts X) :
    ∃ L : Compacts X, K ≤ L ∧ Convex ℝ (L : Set E) ∧ (L : Set E).Nonempty := by
  obtain ⟨r,hr,hKr⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  refine ⟨⟨Metric.closedBall (0 : E) r, isCompact_closedBall _ _⟩, hKr,
    convex_closedBall _ _, ?_⟩
  exact ⟨0, Metric.mem_closedBall_self hr.le⟩

/-- Actual compact-support cohomology of Euclidean space vanishes outside top degree
by genuine representatives and enlargement to compact closed balls. -/
theorem compactCohomology_isZero (V : ModuleCat.{0} ℚ) (a : ℕ) (ha : a ≠ n+2) :
    IsZero (compactCohomology (𝟙 X) (constantRep V) a) := by
  suffices hz : ∀ x : compactCohomology (𝟙 X) (constantRep V) a, x = 0 by
    let : Subsingleton (compactCohomology (𝟙 X) (constantRep V) a) :=
      ⟨fun x y => (hz x).trans (hz y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  intro x
  obtain ⟨K,z,rfl⟩ := compactClass_exists_rep (𝟙 X) (constantRep V) a x
  obtain ⟨L,hKL,hconv,_⟩ := exists_compact_convex_enlargement n K
  apply (compactClass_zero_iff (𝟙 X) (constantRep V) a K z).mpr
  refine ⟨L,hKL,?_⟩
  exact (ModuleCat.subsingleton_of_isZero
    (convexSupportCohomology_isZero n V L L.isCompact hconv a ha)).elim _ _

end TernaryPoly.EuclideanCompactCap
