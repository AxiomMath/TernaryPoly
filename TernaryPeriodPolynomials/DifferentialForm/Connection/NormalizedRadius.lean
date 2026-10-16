module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.NormalizedChart

@[expose] public section


/-! Compact convex normalized charts with uniform actual Riemannian derivative bounds. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpaceCharts SymmetricSpaceCovering
open Manifold Bundle Filter Set Metric
open scoped ContDiff Manifold Bundle Topology ENNReal
attribute [local instance] orbitMetricSpace

/-- A closed coordinate ball is contained in the region of two-sided metric control. -/
theorem exists_normalized_radius (q : OrbitSpace) :
    ∃ r > 0, ∀ v ∈ closedBall (normalizedChart q q) (2 * r),
      v ∈ (normalizedChart q).target ∧
        ‖normalizedChartDerivative q ((normalizedChart q).symm v)‖ < 2 ∧
        ‖normalizedChartInverseDerivative q v‖ < 2 := by
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (eventually_normalizedChart_bounds q)
  refine ⟨δ / 4, by positivity, ?_⟩
  intro v hv
  exact hd ((closedBall_subset_ball (by linarith : 2 * (δ / 4) < δ)) hv)

/-- The inverse normalized chart is two-Lipschitz on any convex ball with the proved derivative bound. -/
theorem normalizedChart_symm_lipschitz (q : OrbitSpace) (r : ℝ)
    (h : ∀ v ∈ ball (normalizedChart q q) r,
      v ∈ (normalizedChart q).target ∧ ‖normalizedChartInverseDerivative q v‖ < 2) :
    LipschitzOnWith 2 (normalizedChart q).symm (ball (normalizedChart q q) r) := by
  let : IsRiemannianManifold 𝓘(ℝ, Coordinates) OrbitSpace := ⟨fun _ _ => rfl⟩
  apply PolynomialFormConnection.lipschitzOnWith_of_norm_mfderiv_le (E := Coordinates)
    (F := TangentSpace 𝓘(ℝ, Coordinates) q) isOpen_ball (convex_ball _ _)
  · exact (contMDiffOn_normalizedChart_symm q).of_le (by simp) |>.mono (fun v hv => (h v hv).1)
  · intro v hv w
    have hn := (normalizedChartInverseDerivative q v).le_opNorm w
    have hh := (h v hv).2.le
    have hb : ‖normalizedChartInverseDerivative q v w‖ ≤ 2 * ‖w‖ :=
      hn.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
    change ‖normalizedChartInverseDerivative q v w‖ₑ ≤ (2 : ℝ≥0∞) * ‖w‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hb

/-- Closed normalized balls have genuinely compact inverse images. -/
theorem isCompact_normalizedChart_symm_closedBall (q : OrbitSpace) (r : ℝ)
    (h : closedBall (normalizedChart q q) r ⊆ (normalizedChart q).target) :
    IsCompact ((normalizedChart q).symm '' closedBall (normalizedChart q q) r) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, Coordinates) q) :=
    FiniteDimensional.of_injective (tangentCoordinates q).toLinearMap (tangentCoordinates q).injective
  apply (isCompact_closedBall _ _).image_of_continuousOn
  exact (normalizedChart q).symm.continuousOn.mono h

end TernaryPoly.SymmetricSpaceRiemannian
