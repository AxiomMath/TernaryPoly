module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapTopMap

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalSupport
variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))
local notation "X" => TopCat.of E
local instance computationEuclideanAction : MulAction Unit X := identityAction X
local instance computationEuclideanContinuousAction : ContinuousConstSMul Unit X := identityContinuousAction X
local instance computationEuclideanFreeAction : IsCancelSMul Unit X := identityFreeAction X
local instance computationEuclideanCoverFact : Fact (IsQuotientCoveringMap (𝟙 X) Unit) := ⟨identityCover X⟩

/-- Actual compact-support top cap followed by augmentation is surjective: every
coefficient is realized by the fixed-generator evaluation on a compact closed ball. -/
theorem topCapEvaluation_surjective (V : ModuleCat.{0} ℚ) :
    Function.Surjective (topCapEvaluation n V) := by
  obtain ⟨K,_,hconv,hne⟩ := exists_compact_convex_enlargement n ⊥
  intro v
  obtain ⟨h,hh⟩ := (convexSupportEvaluationEquiv n V K K.isCompact hconv hne).surjective v
  exact ⟨compactClassMap (𝟙 X) (constantRep V) K (n+2) h,
    (topCapEvaluation_convex n V K hconv hne h).trans hh⟩

/-- Actual compact-support top cap followed by augmentation is injective: a representative
with zero evaluation dies after enlargement to a compact closed ball. -/
theorem topCapEvaluation_injective (V : ModuleCat.{0} ℚ) :
    Function.Injective (topCapEvaluation n V) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro c hc
  change c = 0
  obtain ⟨K,x,rfl⟩ := compactClass_exists_rep (𝟙 X) (constantRep V) (n+2) c
  obtain ⟨L,hKL,hconv,hne⟩ := exists_compact_convex_enlargement n K
  let y := homologyMap (supportMap (𝟙 X) (constantRep V) (K : Set X) (L : Set X) hKL) (n+2) x
  have hy : compactClassMap (𝟙 X) (constantRep V) L (n+2) y =
      compactClassMap (𝟙 X) (constantRep V) K (n+2) x :=
    congrArg (fun f => f x) (compactClassMap_natural (𝟙 X) (constantRep V) K L hKL (n+2))
  have he : convexSupportEvaluationEquiv n V L L.isCompact hconv hne y = 0 := by
    rw [← topCapEvaluation_convex, hy]
    exact hc
  have hz : y = 0 := (convexSupportEvaluationEquiv n V L L.isCompact hconv hne).injective
    (he.trans (map_zero _).symm)
  exact (compactClass_zero_iff (𝟙 X) (constantRep V) (n+2) K x).mpr ⟨L,hKL,hz⟩

/-- Actual compactly supported top cohomology of Euclidean space is V via the actual
compact-support cap map and actual augmentation, for every rational module V. -/
def compactTopEvaluationEquiv (V : ModuleCat.{0} ℚ) :
    compactCohomology (𝟙 X) (constantRep V) (n+2) ≃ₗ[ℚ] V :=
  LinearEquiv.ofBijective (topCapEvaluation n V)
    ⟨topCapEvaluation_injective n V, topCapEvaluation_surjective n V⟩

/-- The compact top isomorphism uses precisely the actual cap-augmentation map. -/
theorem compactTopEvaluationEquiv_apply (V : ModuleCat.{0} ℚ)
    (c : compactCohomology (𝟙 X) (constantRep V) (n+2)) :
    compactTopEvaluationEquiv n V c = topCapEvaluation n V c := rfl

end TernaryPoly.EuclideanCompactCap
