module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.BoundedCutoffs
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingScalar
public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Isometries

@[expose] public section


/-! Comparison of the actual quotient scalar differential with its literal covering derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter SmoothDeRhamGluing SmoothCoveringDeRham SymmetricSpacePositive
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
  SymmetricSpaceTraceMetric SymmetricSpaceRiemannian Manifold Bundle
open scoped ContDiff Manifold Bundle SymmetricSpaceRiemannian Topology

/-- In the global covering coordinates, the manifold derivative is the literal coordinate derivative. -/
theorem hasMFDerivAt_scalar_projection (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (S : Space) :
    HasMFDerivAt 𝓘(ℝ, Coordinates) 𝓘(ℝ) (χ ∘ quotientProjection) S
      (fderiv ℝ (liftScalar χ) (coordinateChart S)) := by
  refine ⟨hχ.continuous.continuousAt.comp quotientProjection_contMDiff.continuous.continuousAt, ?_⟩
  simp only [modelWithCornersSelf_coe, Set.range_id]
  change HasFDerivWithinAt (liftScalar χ) (fderiv ℝ (liftScalar χ) (coordinateChart S))
    Set.univ (coordinateChart S)
  have hx : coordinateChart S ∈ liftedDomain (Set.univ : Set OrbitSpace) := ⟨extract_mem S, mem_univ _⟩
  exact ((((liftScalar_smooth hχ.contMDiffOn) _ hx).contDiffAt
    ((liftedDomain_isOpen isOpen_univ).mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt

/-- The two scalar derivative expressions agree on every actual covering tangent vector. -/
theorem scalarDifferential_projection_apply (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) (S : Space)
    (v : TangentSpace 𝓘(ℝ, Coordinates) S) :
    scalarDifferential χ (quotientProjection S)
        (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S v) =
      fderiv ℝ (liftScalar χ) (coordinateChart S) v := by
  have hcomp := (hχ.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt.comp S
    (quotientProjection_contMDiff.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt
  have he := hcomp.mfderiv.symm.trans (hasMFDerivAt_scalar_projection χ hχ S).mfderiv
  exact congrArg (fun L => L v) he

/-- Actual dual Riemannian norm bounds become exact trace-metric bounds in covering coordinates. -/
theorem liftScalar_derivative_metric_bound (χ : OrbitSpace → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ χ) {B : ℝ}
    (hb : ∀ q, ‖scalarDifferential χ q‖ ≤ B) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) :
    |fderiv ℝ (liftScalar χ) x v| ≤ B * Real.sqrt (coordinatePair x v v) := by
  let S := coordinateChart.symm x
  have hS : coordinateChart S = x := coordinateChart.right_inv (coordinateChart_target.symm ▸ hx)
  let vS : TangentSpace 𝓘(ℝ, Coordinates) S := v
  let w : TangentSpace 𝓘(ℝ, Coordinates) (quotientProjection S) :=
    mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S vS
  have hval : scalarDifferential χ (quotientProjection S) w = fderiv ℝ (liftScalar χ) x v :=
    (scalarDifferential_projection_apply χ hχ S vS).trans
      (congrArg (fun y => fderiv ℝ (liftScalar χ) y v) hS)
  have hmetric : orbitInner (quotientProjection S) w w = coordinatePair x v v :=
    (orbitInner_mfderiv_quotientProjection S vS vS).trans
      (congrArg (fun y => coordinatePair y v v) hS)
  have hn : ‖w‖ = Real.sqrt (coordinatePair x v v) :=
    (norm_eq_sqrt_real_inner w).trans (congrArg Real.sqrt hmetric)
  calc
    _ = |scalarDifferential χ (quotientProjection S) w| := congrArg abs hval.symm
    _ ≤ ‖scalarDifferential χ (quotientProjection S)‖ * ‖w‖ := by
      simpa only [Real.norm_eq_abs] using (scalarDifferential χ (quotientProjection S)).le_opNorm w
    _ ≤ B * ‖w‖ := mul_le_mul_of_nonneg_right (hb (quotientProjection S)) (norm_nonneg w)
    _ = _ := congrArg (B * ·) hn

end TernaryPoly.PolynomialFormConnection
