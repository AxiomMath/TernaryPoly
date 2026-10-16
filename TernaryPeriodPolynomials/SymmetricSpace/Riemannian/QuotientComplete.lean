module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Complete
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.PathLift
public import TernaryPeriodPolynomials.Topology.EMetricApproximateLiftComplete

@[expose] public section


/-! Completeness of the intrinsic metric on the actual arithmetic quotient. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Bundle

attribute [local instance] spaceEMetricSpace orbitEMetricSpace

/-- Smooth path lifting transfers completeness to the actual quotient Riemannian metric. -/
theorem orbit_complete : @CompleteSpace OrbitSpace orbitEMetricSpace.toUniformSpace := by
  exact @EMetricApproximateLiftComplete.complete_of_approximate_lifts
    Space OrbitSpace spaceEMetricSpace orbitEMetricSpace space_complete quotientProjection
    quotientProjection_contMDiff.continuous quotientProjection_surjective
    exists_lift_riemannianEDist_lt

end TernaryPoly.SymmetricSpaceRiemannian
