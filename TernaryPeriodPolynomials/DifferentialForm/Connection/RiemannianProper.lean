module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.RiemannianSplit
public import TernaryPeriodPolynomials.DifferentialForm.Connection.MetricProper

@[expose] public section


/-! Properness of the actual intrinsic Riemannian metric on the positive-form cover and quotient. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open Metric Set
open scoped ContDiff Manifold Bundle ENNReal
attribute [local instance] spaceMetricSpace orbitMetricSpace

/-- Homogeneity and actual short paths give compact closed intrinsic balls on the cover. -/
theorem space_proper : @ProperSpace Space spaceMetricSpace.toPseudoMetricSpace := by
  obtain ⟨ε, hε, hc⟩ := PolynomialFormConnection.uniform_compact_radius_of_transitive_isometries
    (X := Space) (fun S T => by
      obtain ⟨g, hg⟩ := exists_act_eq S T
      exact ⟨actionIsometry g, hg⟩)
  exact PolynomialFormConnection.proper_of_uniform_compact_radius_and_split ε hε hc space_dist_split

/-- Compactness descends through approximate distance-realizing quotient lifts. -/
theorem orbit_proper : @ProperSpace OrbitSpace orbitMetricSpace.toPseudoMetricSpace := by
  let : ProperSpace Space := space_proper
  apply ProperSpace.of_isCompact_closedBall_of_le 0
  intro q r hr
  obtain ⟨S, hS⟩ := quotientProjection_surjective q
  have hc := (isCompact_closedBall S (r + 1)).image quotientProjection_contMDiff.continuous
  apply hc.of_isClosed_subset isClosed_closedBall
  intro q' hq'
  have hd : dist (quotientProjection S) q' < r + 1 := by
    rw [hS]
    have h := mem_closedBall.mp hq'
    rw [dist_comm] at h
    linarith
  have he : Manifold.riemannianEDist 𝓘(ℝ, Coordinates) (quotientProjection S) q' <
      ENNReal.ofReal (r + 1) := by
    change edist (quotientProjection S) q' < ENNReal.ofReal (r + 1)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact hd
  obtain ⟨T, hT, hdist⟩ := exists_lift_riemannianEDist_lt S q' (ENNReal.ofReal (r + 1)) he
  refine ⟨T, ?_, hT⟩
  change edist S T < ENNReal.ofReal (r + 1) at hdist
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hdist
  simpa only [mem_closedBall, dist_comm] using hdist.le

end TernaryPoly.SymmetricSpaceRiemannian
