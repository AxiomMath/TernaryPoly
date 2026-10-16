module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.QuotientComplete
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! The actual complete intrinsic Riemannian distances are finite on the connected cover and quotient. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Metric

/-- A connected extended metric space has no infinite-distance pairs. -/
theorem edist_ne_top_of_preconnected {X : Type*} [EMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have h : IsClopen (Metric.eball x ⊤) := ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hu := h.eq_univ ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hu]; trivial
  exact (by simpa only [Metric.mem_eball, edist_comm] using hy : edist x y < ⊤).ne

end TernaryPoly.PolynomialFormConnection

namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Manifold Bundle
attribute [local instance] spaceEMetricSpace orbitEMetricSpace

theorem space_edist_ne_top (S T : Space) : edist S T ≠ ⊤ :=
  PolynomialFormConnection.edist_ne_top_of_preconnected S T

theorem orbit_edist_ne_top (p q : OrbitSpace) : edist p q ≠ ⊤ := by
  let : ConnectedSpace OrbitSpace := quotientProjection_surjective.connectedSpace quotientProjection_contMDiff.continuous
  exact PolynomialFormConnection.edist_ne_top_of_preconnected p q

/-- The finite intrinsic metric on the genuine positive-form manifold, with its original topology. -/
@[instance_reducible] def spaceMetricSpace : MetricSpace Space :=
  EMetricSpace.toMetricSpace space_edist_ne_top

/-- The finite intrinsic metric on the actual quotient, with its original topology. -/
@[instance_reducible] def orbitMetricSpace : MetricSpace OrbitSpace :=
  EMetricSpace.toMetricSpace orbit_edist_ne_top

end TernaryPoly.SymmetricSpaceRiemannian
