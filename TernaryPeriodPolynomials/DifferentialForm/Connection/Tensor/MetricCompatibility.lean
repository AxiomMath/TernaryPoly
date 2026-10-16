module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricFrame

@[expose] public section


/-! Actual metric compatibility of the full polynomial-valued tensor connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts SmoothCoveringDeRham
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_tensorFrame_pairing (n k : ℕ) (x u : Coordinates) (a b : FormValue n k) :
    HasDerivAt (fun t : ℝ => formPairing n k x (tensorFrameCurve n k x u a t) (tensorFrameCurve n k x u b t))
      (formPairing n k x (coefficientFormMap (connectionMatrix n x u) k a - tangentFormAction n k x u a) b +
        formPairing n k x a (coefficientFormMap (connectionMatrix n x u) k b - tangentFormAction n k x u b)) 0 := by
  have h := hasDerivAt_fixed_bilinear (V := FormValue n k) (formContinuousBilin n k x)
    (w := tensorFrameCurve n k x u a) (z := tensorFrameCurve n k x u b)
    (by convert! hasDerivAt_tensorFrameCurve n k x u a using 1)
    (by convert! hasDerivAt_tensorFrameCurve n k x u b using 1)
  simpa only [tensorFrameCurve_zero, formContinuousBilin_apply] using h

/-- Constant coordinate forms see exactly the actual coefficient and cotangent connection terms. -/
theorem hasDerivAt_formPairing_connection_constants (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) (a b : FormValue n k) :
    HasDerivAt (fun t : ℝ => formPairing n k (x + t • u) a b)
      (formPairing n k x (coefficientFormMap (connectionMatrix n x u) k a - tangentFormAction n k x u a) b +
        formPairing n k x a (coefficientFormMap (connectionMatrix n x u) k b - tangentFormAction n k x u b)) 0 := by
  let F := fun z : (Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) × Matrix (Fin 5) (Fin 5) ℝ =>
    metricDataPairing n k z.1 z.2 a b
  have hd := (contDiff_metricDataPairing n k a b).differentiable (by simp) |>.differentiableAt
    (x := (coordinateCoefficientMetric n x, inverseGram x))
  have ha := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_coordinateMetric_operator n x hx u).prodMk (hasDerivAt_inverseGram_operator x hx u))
    (by simp only [zero_smul, add_zero])
  have hb := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_metricCoefficientCurve n x hx u).prodMk (hasDerivAt_metricInverseCurve x hx u))
    (by simp only [metricCoefficientCurve_zero, metricInverseCurve_zero])
  have hm := hasDerivAt_tensorFrame_pairing n k x u a b
  have hm' : HasDerivAt (fun t : ℝ => F (metricCoefficientCurve n x u t, metricInverseCurve x u t))
      (formPairing n k x (coefficientFormMap (connectionMatrix n x u) k a - tangentFormAction n k x u a) b +
        formPairing n k x a (coefficientFormMap (connectionMatrix n x u) k b - tangentFormAction n k x u b)) 0 := by
    convert! hm using 1
    funext t
    exact metricDataPairing_tensorFrameCurve n k x u a b t
  have he := hb.unique hm'
  rw [he] at ha
  exact ha

end TernaryPoly.PolynomialFormConnection
