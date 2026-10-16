module

public import TernaryPeriodPolynomials.SymmetricSpace.ChartOrientationAction

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceChartOrientation
open SymmetricSpacePositive (RealGL conjugate)
open SymmetricSpaceCharts (Coordinates reconstruct positiveCoordinates coordinateAction)

/-- The actual homogeneous action has positive determinant on both components of GL3(R). -/
theorem chart_homogeneous_det_pos (g : RealGL) :
    0 < (ProjectiveChartOrientation.homogeneous
      (chartA g.val) (chartB g.val) (chartC g.val) (chartD g.val)).det := by
  rw [chart_homogeneous_det,show (4 : ℕ)=2*2 from rfl,pow_mul]
  exact sq_pos_of_ne_zero (pow_ne_zero 2 g.det_ne_zero)

/-- The projective Jacobian is the genuine derivative of the actual coordinate action. -/
theorem hasFDerivAt_coordinateAction (g : RealGL) (x : Coordinates)
    (hx : x∈positiveCoordinates) :
    HasFDerivAt (coordinateAction g)
      (ProjectiveChartOrientation.matrixCLM (ProjectiveChartOrientation.jacobian
        (chartA g.val) (chartB g.val) (chartC g.val) (chartD g.val) x)) x := by
  rw [coordinateAction_eq_projective]
  exact ProjectiveChartOrientation.hasFDerivAt_projective _ _ _ _ x
    (ne_of_gt (chart_denominator_pos g x hx))

/-- Exact determinant of the actual derivative in the literal five-coordinate chart. -/
theorem coordinateAction_fderiv_det (g : RealGL) (x : Coordinates)
    (hx : x∈positiveCoordinates) :
    LinearMap.det (fderiv ℝ (coordinateAction g) x).toLinearMap =
      (conjugate g (reconstruct x)).trace⁻¹ ^ 6 * g.val.det ^ 4 := by
  rw [coordinateAction_eq_projective,ProjectiveChartOrientation.fderiv_det _ _ _ _ x
    (ne_of_gt (chart_denominator_pos g x hx)),chart_denominator_eq,chart_homogeneous_det]
  rfl

/-- Every actual GL3(R) coordinate action has positive derivative determinant on the domain. -/
theorem coordinateAction_fderiv_det_pos (g : RealGL) (x : Coordinates)
    (hx : x∈positiveCoordinates) :
    0 < LinearMap.det (fderiv ℝ (coordinateAction g) x).toLinearMap := by
  rw [coordinateAction_eq_projective]
  exact ProjectiveChartOrientation.fderiv_det_pos _ _ _ _ x
    (chart_denominator_pos g x hx) (chart_homogeneous_det_pos g)

end TernaryPoly.SymmetricSpaceChartOrientation
