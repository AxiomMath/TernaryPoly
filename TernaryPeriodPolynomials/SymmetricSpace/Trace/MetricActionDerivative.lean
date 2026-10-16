module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricNormalizeDerivative
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsAction

@[expose] public section


/-! Differentiate the genuine projective GL3 action in its coordinates. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix SymmetricSpacePositive SymmetricSpaceCharts
open scoped ContDiff Matrix.Norms.Elementwise Topology

/-- The actual linear congruence map, with the ambient coordinate norm. -/
def congruenceCLM (g : RealGL) : Mat →L[ℝ] Mat :=
  (show Mat →ₗ[ℝ] Mat from
    { toFun := conjugate g
      map_add' := fun U V => by simp [conjugate, mul_add, add_mul]
      map_smul' := fun c U => by simp [conjugate] }).toContinuousLinearMap

@[simp] theorem congruenceCLM_apply (g : RealGL) (U : Mat) :
    congruenceCLM g U = conjugate g U := rfl

/-- Reconstruction after coordinate action is the literal normalized congruence. -/
theorem reconstruct_coordinateAction (g : RealGL) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    reconstruct (coordinateAction g x) = normalize (conjugate g (reconstruct x)) := by
  rw [coordinateAction_formula]
  have h := normalize_mem _ (conjugate_positive g (reconstruct x) hx)
  exact reconstruct_extract _ (Matrix.isHermitian_iff_isSymm.mp h.1.isHermitian) h.2

/-- The derivative of the actual reconstructed action includes the radial term. -/
theorem hasFDerivAt_reconstruct_coordinateAction (g : RealGL) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) :
    HasFDerivAt (fun y => reconstruct (coordinateAction g y))
      ((normalizationDerivative (conjugate g (reconstruct x))).comp
        ((congruenceCLM g).comp tangentCLM)) x := by
  have hn := hasFDerivAt_normalize (conjugate g (reconstruct x))
    (ne_of_gt (conjugate_positive g (reconstruct x) hx).trace_pos)
  have hc := (congruenceCLM g).hasFDerivAt.comp x (hasFDerivAt_reconstruct x)
  apply (hn.comp x hc).congr_of_eventuallyEq
  filter_upwards [isOpen_positiveCoordinates.mem_nhds hx] with y hy
  exact reconstruct_coordinateAction g y hy

/-- The actual coordinate derivative, inserted in trace-zero matrices. -/
theorem tangent_fderiv_coordinateAction (g : RealGL) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    tangentMatrix (fderiv ℝ (coordinateAction g) x v) =
      normalizationDerivative (conjugate g (reconstruct x)) (conjugate g (tangentMatrix v)) := by
  have hd := ((contDiffOn_coordinateAction g).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have h := (hasFDerivAt_reconstruct (coordinateAction g x)).comp x hd.hasFDerivAt
  have he := h.unique (hasFDerivAt_reconstruct_coordinateAction g x hx)
  exact congrArg (fun L : Coordinates →L[ℝ] Mat => L v) he

end TernaryPoly.SymmetricSpaceTraceMetric
