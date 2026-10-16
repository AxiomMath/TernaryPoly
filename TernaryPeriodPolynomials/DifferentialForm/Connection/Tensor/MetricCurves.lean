module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricAffine

@[expose] public section


/-! Affine comparison curves with exactly the first derivatives of the genuine metrics. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts
open scoped Matrix.Norms.Elementwise

def metricCoefficientCurve (n : ℕ) (x u : Coordinates) (t : ℝ) :
    Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ :=
  (coordinateCoefficientMetric n x).bilinearComp (affineOperator (connectionMatrix n x u) t)
    (affineOperator (connectionMatrix n x u) t)

@[simp] theorem metricCoefficientCurve_zero (n : ℕ) (x u : Coordinates) :
    metricCoefficientCurve n x u 0 = coordinateCoefficientMetric n x := by
  apply ContinuousLinearMap.ext
  intro p
  apply ContinuousLinearMap.ext
  intro q
  simp only [metricCoefficientCurve, affineOperator_zero, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply]

theorem hasDerivAt_metricCoefficientCurve (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) :
    HasDerivAt (metricCoefficientCurve n x u) (fderiv ℝ (coordinateCoefficientMetric n) x u) 0 := by
  convert! hasDerivAt_bilinear_affine (coordinateCoefficientMetric n x) (connectionMatrix n x u) using 1
  apply ContinuousLinearMap.ext
  intro p
  apply ContinuousLinearMap.ext
  intro q
  exact metricDerivative_apply n x hx u p q

def metricInverseCurve (x u : Coordinates) (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 + t • (-tangentConnectionMatrix x u)) * inverseGram x *
    (1 + t • (-tangentConnectionMatrix x u)).transpose

@[simp] theorem metricInverseCurve_zero (x u : Coordinates) : metricInverseCurve x u 0 = inverseGram x := by
  simp only [metricInverseCurve, zero_smul, add_zero, one_mul, Matrix.transpose_one, mul_one]

theorem hasDerivAt_metricInverseCurve (x : Coordinates) (hx : x ∈ positiveCoordinates) (u : Coordinates) :
    HasDerivAt (metricInverseCurve x u) (fderiv ℝ inverseGram x u) 0 := by
  have h := hasDerivAt_finite_matrix_product
    (hasDerivAt_finite_matrix_product (hasDerivAt_matrix_affine_identity 5 (-tangentConnectionMatrix x u))
      (hasDerivAt_const (0 : ℝ) (inverseGram x)))
    (hasDerivAt_finite_matrix_transpose (hasDerivAt_matrix_affine_identity 5 (-tangentConnectionMatrix x u)))
  convert! h using 1
  simp only [zero_smul, add_zero, mul_zero, one_mul, Matrix.transpose_one, mul_one,
    inverseGramDerivative x hx u, Matrix.transpose_neg, neg_mul, mul_neg, neg_add_rev]
  abel

end TernaryPoly.PolynomialFormConnection
