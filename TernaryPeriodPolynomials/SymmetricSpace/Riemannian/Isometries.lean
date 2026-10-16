module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Structure
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricSpaceAction
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricProjection
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.MapLength

@[expose] public section


/-! The genuine GL3 actions preserve the intrinsic trace-metric distance. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Bundle ENNReal

/-- The actual normalized congruence derivative preserves tangent length. -/
theorem enorm_mfderiv_act (g : RealGL) (S : Space)
    (v : TangentSpace 𝓘(ℝ, Coordinates) S) :
    ‖mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (act g) S v‖ₑ = ‖v‖ₑ := by
  rw [enorm_eq_iff_norm_eq]
  have h := spaceInner_mfderiv_act g S v v
  change inner ℝ (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (act g) S v)
    (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) (act g) S v) = inner ℝ v v at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The literal covering projection preserves tangent length. -/
theorem enorm_mfderiv_projection (S : Space) (v : TangentSpace 𝓘(ℝ, Coordinates) S) :
    ‖mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S v‖ₑ = ‖v‖ₑ := by
  rw [enorm_eq_iff_norm_eq]
  have h := orbitInner_mfderiv_quotientProjection S v v
  change inner ℝ (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S v)
    (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S v) = inner ℝ v v at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Every actual GL3 action is an isometry for the intrinsic Riemannian extended distance. -/
theorem riemannianEDist_act (g : RealGL) (S T : Space) :
    riemannianEDist 𝓘(ℝ, Coordinates) (act g S) (act g T) =
      riemannianEDist 𝓘(ℝ, Coordinates) S T := by
  apply le_antisymm
  · exact RiemannianMapLength.riemannianEDist_map_le (act g)
      ((contMDiff_act g).of_le (by simp)) (enorm_mfderiv_act g) S T
  · have h := RiemannianMapLength.riemannianEDist_map_le (act g⁻¹)
      ((contMDiff_act g⁻¹).of_le (by simp)) (enorm_mfderiv_act g⁻¹) (act g S) (act g T)
    simpa only [← act_mul, inv_mul_cancel, act_one] using h

/-- The exact quotient projection decreases intrinsic distance. -/
theorem riemannianEDist_projection_le (S T : Space) :
    riemannianEDist 𝓘(ℝ, Coordinates) (quotientProjection S) (quotientProjection T) ≤
      riemannianEDist 𝓘(ℝ, Coordinates) S T :=
  RiemannianMapLength.riemannianEDist_map_le quotientProjection
    (quotientProjection_contMDiff.of_le (by simp)) enorm_mfderiv_projection S T

end TernaryPoly.SymmetricSpaceRiemannian
