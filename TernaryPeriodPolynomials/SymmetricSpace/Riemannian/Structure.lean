module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricOrbitSmooth
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricSpaceBundle
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Algebra.Module.TransferInstance

@[expose] public section

/-! The actual metric structures, preserving the preexisting manifold topologies. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Bundle

scoped instance spaceRiemannianBundle :
    RiemannianBundle (TangentSpace 𝓘(ℝ, Coordinates) : Space → Type) :=
  ⟨spaceContMDiffRiemannianMetric.toRiemannianMetric⟩

scoped instance orbitRiemannianBundle :
    RiemannianBundle (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) :=
  ⟨orbitContMDiffRiemannianMetric.toRiemannianMetric⟩

/-- The actual covering scalar product is smooth. -/
theorem space_smooth_metric : IsContMDiffRiemannianBundle 𝓘(ℝ, Coordinates) ∞ Coordinates
    (TangentSpace 𝓘(ℝ, Coordinates) : Space → Type) := by infer_instance

/-- The actual quotient scalar product is smooth. -/
theorem orbit_smooth_metric : IsContMDiffRiemannianBundle 𝓘(ℝ, Coordinates) ∞ Coordinates
    (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) := by infer_instance

scoped instance spaceContinuousMetric : IsContinuousRiemannianBundle Coordinates
    (TangentSpace 𝓘(ℝ, Coordinates) : Space → Type) :=
  ⟨⟨spaceInner, contMDiff_spaceInner.continuous, fun _ _ _ => rfl⟩⟩

scoped instance orbitContinuousMetric : IsContinuousRiemannianBundle Coordinates
    (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) :=
  ⟨⟨orbitInner, contMDiff_orbitInner.continuous, fun _ _ _ => rfl⟩⟩

/-- Its intrinsic extended distance induces the original positive-form topology. -/
@[instance_reducible] def spaceEMetricSpace : EMetricSpace Space := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, Coordinates) Space

/-- Its intrinsic extended distance induces the original quotient topology. -/
@[instance_reducible] def orbitEMetricSpace : EMetricSpace OrbitSpace := by
  let : LocallyCompactSpace OrbitSpace := ChartedSpace.locallyCompactSpace Coordinates OrbitSpace
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ, Coordinates) OrbitSpace

end TernaryPoly.SymmetricSpaceRiemannian
