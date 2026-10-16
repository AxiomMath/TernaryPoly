module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricCoordinateSmooth
public import TernaryPeriodPolynomials.Analysis.PositiveBilinearFinite
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public section


/-! The actual positive metric as a smooth family of continuous bilinear forms. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix SymmetricSpaceCharts
open scoped ContDiff Matrix.Norms.Elementwise

/-- Continuity is in the exact original five-dimensional norm. -/
def coordinateContinuousBilin (x : Coordinates) : Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ :=
  ((LinearMap.toContinuousLinearMap.toLinearMap).comp (coordinateBilin x)).toContinuousLinearMap

@[simp] theorem coordinateContinuousBilin_apply (x v w : Coordinates) :
    coordinateContinuousBilin x v w = coordinatePair x v w := rfl

/-- Finite-dimensional bilinear smoothness follows from actual joint scalar smoothness. -/
theorem contDiffOn_coordinateContinuousBilin :
    ContDiffOn ℝ ∞ coordinateContinuousBilin positiveCoordinates := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  change ContDiffOn ℝ ∞ (fun x => coordinatePair x v w) positiveCoordinates
  have h : ContDiff ℝ ∞ (fun x : Coordinates => (x, (v, w))) :=
    contDiff_id.prodMk contDiff_const
  have hh := contDiffOn_coordinatePair.comp h.contDiffOn
    (show Set.MapsTo (fun x : Coordinates => (x, (v, w))) positiveCoordinates
      {p : Coordinates × Coordinates × Coordinates | p.1 ∈ positiveCoordinates} from
      fun _ hx => hx)
  exact hh

/-- The metric controls the preexisting coordinate topology pointwise. -/
theorem coordinatePair_lower_bound (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Coordinates, c * ‖v‖ ^ 2 ≤ coordinatePair x v v :=
  PositiveBilinearFinite.exists_pos_lower_bound (coordinateContinuousBilin x)
    (coordinatePair_pos x hx)

/-- Its unit ball is bounded without changing the ambient norm or topology. -/
theorem coordinatePair_isVonNBounded (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    Bornology.IsVonNBounded ℝ {v : Coordinates | coordinatePair x v v < 1} :=
  PositiveBilinearFinite.isVonNBounded_unitBall (coordinateContinuousBilin x)
    (coordinatePair_pos x hx)

end TernaryPoly.SymmetricSpaceTraceMetric
