module

public import TernaryPeriodPolynomials.SymmetricSpace.ChartOrientationMatrix
public import TernaryPeriodPolynomials.SymmetricSpace.ChartsAction
public import TernaryPeriodPolynomials.SymmetricSpace.ProjectiveChartDerivative

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceChartOrientation
open Matrix
open SymmetricSpacePositive (RealGL conjugate normalize)
open SymmetricSpaceCharts (Coordinates extract reconstruct positiveCoordinates coordinateAction)

/-- The affine numerator is precisely the five selected entries of the actual conjugate. -/
theorem chart_numerator_eq (g : RealGL) (x : Coordinates) :
    ProjectiveChartOrientation.numerator (chartA g.val) (chartB g.val) x =
      extract (conjugate g (reconstruct x)) := by
  ext i
  rw [←homogeneousMatrix_affineLift_inl,homogeneousMatrix_mulVec,traceCoordinates_inl]
  simp only [SymmetricSpaceOrientation.congruence_apply,fromTraceCoordinates_affineLift,
    conjugate,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]

/-- The homogeneous denominator is the actual trace used for normalization. -/
theorem chart_denominator_eq (g : RealGL) (x : Coordinates) :
    ProjectiveChartOrientation.denominator (chartC g.val) (chartD g.val) x =
      (conjugate g (reconstruct x)).trace := by
  rw [←homogeneousMatrix_affineLift_inr,homogeneousMatrix_mulVec,traceCoordinates_inr]
  simp only [SymmetricSpaceOrientation.congruence_apply,fromTraceCoordinates_affineLift,
    conjugate,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Entry extraction commutes literally with real scalar multiplication. -/
theorem extract_smul (r : ℝ) (S : SymmetricSpacePositive.Mat) :
    extract (r • S)=r • extract S := by
  ext i
  fin_cases i <;> rfl

/-- The entire coordinate action equals the actual affine-projective formula. -/
theorem coordinateAction_eq_projective (g : RealGL) :
    coordinateAction g = ProjectiveChartOrientation.projective
      (chartA g.val) (chartB g.val) (chartC g.val) (chartD g.val) := by
  funext x
  rw [SymmetricSpaceCharts.coordinateAction_formula,ProjectiveChartOrientation.projective,
    chart_denominator_eq,chart_numerator_eq,SymmetricSpacePositive.normalize,extract_smul]

/-- Positive forms give a positive affine denominator for either determinant-sign component. -/
theorem chart_denominator_pos (g : RealGL) (x : Coordinates) (hx : x∈positiveCoordinates) :
    0 < ProjectiveChartOrientation.denominator (chartC g.val) (chartD g.val) x := by
  rw [chart_denominator_eq]
  exact (SymmetricSpacePositive.conjugate_positive g (reconstruct x) hx).trace_pos

end TernaryPoly.SymmetricSpaceChartOrientation
