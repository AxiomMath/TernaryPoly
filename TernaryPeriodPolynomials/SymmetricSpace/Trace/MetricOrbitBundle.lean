module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricContinuousBilinear
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldAtlas
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

@[expose] public section

/-! The metric on the literal tangent fibers of the principal-six quotient. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle ContinuousLinearMap
open scoped ContDiff Manifold Matrix.Norms.Elementwise

/-- Tangent fibers use the preferred chart at their own base point. -/
def orbitInner (q : OrbitSpace) :
    TangentSpace 𝓘(ℝ, Coordinates) q →L[ℝ] TangentSpace 𝓘(ℝ, Coordinates) q →L[ℝ] ℝ :=
  coordinateContinuousBilin (chartAt Coordinates q q)

@[simp] theorem orbitInner_apply (q : OrbitSpace) (v w : TangentSpace 𝓘(ℝ, Coordinates) q) :
    orbitInner q v w = coordinatePair (chartAt Coordinates q q) v w := rfl

theorem orbit_chart_self_positive (q : OrbitSpace) :
    chartAt Coordinates q q ∈ positiveCoordinates :=
  quotientChart_target_subset q.out ((chartAt Coordinates q).map_source
    (mem_chart_source Coordinates q))

/-- A genuine Riemannian metric in the fixed topology of the actual tangent bundle. -/
def orbitRiemannianMetric : RiemannianMetric (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) where
  inner := orbitInner
  symm q := coordinatePair_comm (chartAt Coordinates q q)
  pos q := coordinatePair_pos (chartAt Coordinates q q) (orbit_chart_self_positive q)
  continuousAt q := ((orbitInner q).continuous.clm_apply continuous_id).continuousAt
  isVonNBounded q := coordinatePair_isVonNBounded (chartAt Coordinates q q)
    (orbit_chart_self_positive q)

end TernaryPoly.SymmetricSpaceTraceMetric
