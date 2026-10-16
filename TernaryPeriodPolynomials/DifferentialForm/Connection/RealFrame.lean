module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.RealGeometry

@[expose] public section


/-! Determinant-normalized real frames act transitively on the genuine coordinate domain. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem coordinateForm_injective_on {x y : Coordinates} (hx : x ∈ positiveCoordinates)
    (hy : y ∈ positiveCoordinates) (h : coordinateForm x = coordinateForm y) : x = y := by
  rw [← matrixChart_coordinateForm x hx, h, matrixChart_coordinateForm y hy]

/-- The frame has determinant square one because the actual Q has determinant one. -/
theorem exists_normalized_real_frame (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    ∃ g : RealGL, g.val.det ^ 2 = 1 ∧ coordinateAction g (coordinateChart basepoint) = x := by
  obtain ⟨g,hg⟩ := exists_positive_frame (coordinateForm x) (coordinateForm_positive x hx)
  have hd : g.val.det ^ 2 = 1 := by
    have h := coordinateForm_det x hx
    rw [hg, Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, star_trivial] at h
    simpa only [pow_two] using h
  refine ⟨g,hd,coordinateForm_injective_on (coordinateAction_mem g _ (extract_mem basepoint)) hx ?_⟩
  rw [coordinateForm_real g hd (coordinateChart basepoint) (extract_mem basepoint), coordinateForm_basepoint]
  simpa only [conjugate, mul_one] using hg.symm

end TernaryPoly.PolynomialFormConnection
