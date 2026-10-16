module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.NormalizedPatch

@[expose] public section


/-! Genuine finite smooth partitions subordinate to uniformly controlled normalized patches. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set Metric
open scoped ContDiff Manifold Bundle Topology
attribute [local instance] orbitMetricSpace

/-- All patch bounds are verified in the actual Riemannian tangent norms. -/
structure FiniteNormalizedPartition (K : Set OrbitSpace) where
  centers : Finset OrbitSpace
  radius : centers → ℝ
  radius_pos : ∀ i, 0 < radius i
  bounds : ∀ i v, v ∈ closedBall (normalizedChart i.val i.val) (2 * radius i) →
    v ∈ (normalizedChart i.val).target ∧
      ‖normalizedChartDerivative i.val ((normalizedChart i.val).symm v)‖ < 2 ∧
      ‖normalizedChartInverseDerivative i.val v‖ < 2
  weights : SmoothPartitionOfUnity centers 𝓘(ℝ, Coordinates) OrbitSpace K
  subordinate : weights.IsSubordinate (fun i => normalizedPatch i.val (radius i))

/-- Every compact quotient set has a finite normalized smooth partition. -/
theorem exists_finiteNormalizedPartition {K : Set OrbitSpace} (hK : IsCompact K) :
    Nonempty (FiniteNormalizedPartition K) := by
  classical
  let : ProperSpace OrbitSpace := orbit_proper
  choose r hr hb using exists_normalized_radius
  have hcover : K ⊆ ⋃ q : OrbitSpace, normalizedPatch q (r q) := by
    intro q _
    exact mem_iUnion.mpr ⟨q, mem_normalizedPatch q (hr q)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun q : OrbitSpace => normalizedPatch q (r q))
    (fun q => isOpen_normalizedPatch q (r q)) hcover
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates) hK.isClosed
    (fun i : s => normalizedPatch i.val (r i.val))
    (fun i => isOpen_normalizedPatch i.val (r i.val)) (by
      intro q hq
      obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.mp (hs hq)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hqi⟩)
  exact ⟨⟨s, (fun i => r i.val), (fun i => hr i.val), (fun i => hb i.val), φ, hφ⟩⟩

/-- Every weight is compactly supported and has bounded actual covector norm. -/
theorem FiniteNormalizedPartition.weight_bounds {K : Set OrbitSpace}
    (P : FiniteNormalizedPartition K) (i : P.centers) :
    HasCompactSupport (P.weights i) ∧ ∃ D > 0, ∀ y, ‖scalarDifferential (P.weights i) y‖ ≤ D := by
  apply scalar_bounds_of_normalizedPatch i.val (P.radius i) _ (P.weights i)
    (P.weights i).contMDiff (P.subordinate i)
  intro v hv
  have h := P.bounds i v (closedBall_subset_closedBall (by linarith [P.radius_pos i]) hv)
  exact ⟨h.1, h.2.1.le⟩

end TernaryPoly.SymmetricSpaceRiemannian
