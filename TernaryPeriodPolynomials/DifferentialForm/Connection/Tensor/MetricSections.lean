module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricCompatibility

@[expose] public section



/-! Full metric compatibility of actual varying polynomial-valued alternating forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts SmoothCoveringDeRham
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_formSection_line (n k : ℕ) (w : Coordinates → FormValue n k) (x u : Coordinates)
    (hw : DifferentiableAt ℝ w x) :
    HasDerivAt (fun t : ℝ => w (x + t • u)) (fderiv ℝ w x u) 0 := by
  have h := HasFDerivAt.comp_hasDerivAt_of_eq (E := FormValue n k) (F := Coordinates)
    (l := w) (l' := fderiv ℝ w x) 0 hw.hasFDerivAt (hasDerivAt_coordinateLine x u)
    (by simp only [zero_smul, add_zero])
  convert! h using 1

theorem hasDerivAt_formMetric_operator (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) :
    HasDerivAt (fun t : ℝ => formContinuousBilin n k (x + t • u))
      (fderiv ℝ (formContinuousBilin n k) x u) 0 := by
  have hd := ((((contDiffOn_formContinuousBilin n k) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have h := HasFDerivAt.comp_hasDerivAt_of_eq
    (E := FormValue n k →L[ℝ] FormValue n k →L[ℝ] ℝ) (F := Coordinates)
    (l := formContinuousBilin n k) (l' := fderiv ℝ (formContinuousBilin n k) x)
    0 hd.hasFDerivAt (hasDerivAt_coordinateLine x u) (by simp only [zero_smul, add_zero])
  convert! h using 1

theorem formMetricDerivative_apply (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) (a b : FormValue n k) :
    fderiv ℝ (formContinuousBilin n k) x u a b =
      formPairing n k x (coefficientFormMap (connectionMatrix n x u) k a - tangentFormAction n k x u a) b +
        formPairing n k x a (coefficientFormMap (connectionMatrix n x u) k b - tangentFormAction n k x u b) := by
  have h := ((hasDerivAt_formMetric_operator n k x hx u).clm_apply
    (hasDerivAt_const (0 : ℝ) a)).clm_apply (hasDerivAt_const (0 : ℝ) b)
  have h' : HasDerivAt (fun t : ℝ => formPairing n k (x + t • u) a b)
      (fderiv ℝ (formContinuousBilin n k) x u a b) 0 := by
    simpa only [PolynomialFormCoordinates.clm_map_zero, _root_.zero_apply, add_zero,
      formContinuousBilin_apply] using h
  exact h'.unique (hasDerivAt_formPairing_connection_constants n k x hx u a b)

/-- Metric compatibility includes derivatives of both actual tensor sections. -/
theorem hasDerivAt_formPairing_connection (n k : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) (w z : Coordinates → FormValue n k)
    (hw : DifferentiableAt ℝ w x) (hz : DifferentiableAt ℝ z x) :
    HasDerivAt (fun t : ℝ => formPairing n k (x + t • u) (w (x + t • u)) (z (x + t • u)))
      (formPairing n k x (covariantFormDerivative n k w x u) (z x) +
        formPairing n k x (w x) (covariantFormDerivative n k z x u)) 0 := by
  have h := hasDerivAt_variable_bilinear (V := FormValue n k)
    (B := fun t : ℝ => formContinuousBilin n k (x + t • u))
    (w := fun t : ℝ => w (x + t • u)) (z := fun t : ℝ => z (x + t • u))
    (by convert! hasDerivAt_formMetric_operator n k x hx u using 1)
    (by convert! hasDerivAt_formSection_line n k w x u hw using 1)
    (by convert! hasDerivAt_formSection_line n k z x u hz using 1)
  convert! h using 1
  simp only [zero_smul, add_zero]
  rw [formMetricDerivative_apply n k x hx u (w x) (z x)]
  change formContinuousBilin n k x (covariantFormDerivative n k w x u) (z x) +
      formContinuousBilin n k x (w x) (covariantFormDerivative n k z x u) = _
  simp only [covariantFormDerivative, PolynomialFormCoordinates.clm_map_add,
    PolynomialFormCoordinates.clm_map_sub, _root_.add_apply, _root_.sub_apply]
  change _ = formContinuousBilin n k x
      (coefficientFormMap (connectionMatrix n x u) k (w x) - tangentFormAction n k x u (w x)) (z x) +
    formContinuousBilin n k x (w x)
      (coefficientFormMap (connectionMatrix n x u) k (z x) - tangentFormAction n k x u (z x)) +
    formContinuousBilin n k x (fderiv ℝ w x u) (z x) + formContinuousBilin n k x (w x) (fderiv ℝ z x u)
  simp only [PolynomialFormCoordinates.clm_map_sub, _root_.sub_apply]
  ring

end TernaryPoly.PolynomialFormConnection
