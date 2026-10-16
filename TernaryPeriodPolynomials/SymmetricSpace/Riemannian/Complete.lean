module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Isometries
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Transitive
public import TernaryPeriodPolynomials.Topology.HomogeneousEMetricComplete

@[expose] public section


/-! Completeness of the actual invariant Riemannian distance on positive forms. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Bundle

attribute [local instance] spaceEMetricSpace

/-- The actual action homeomorphism is an isometry for the intrinsic trace metric. -/
def actionIsometry (g : RealGL) : Space ≃ᵢ Space where
  toEquiv := (actionHomeomorph g).toEquiv
  isometry_toFun S T := riemannianEDist_act g S T

/-- The Riemannian extended distance on the actual covering manifold is complete. -/
theorem space_complete : @CompleteSpace Space spaceEMetricSpace.toUniformSpace := by
  apply HomogeneousEMetricComplete.complete_of_transitive_isometries (X := Space)
  intro S T
  obtain ⟨g, hg⟩ := exists_act_eq S T
  exact ⟨actionIsometry g, hg⟩

end TernaryPoly.SymmetricSpaceRiemannian
