module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Parallel

@[expose] public section


/-! The tangent metric expressed in the actual logarithmic differential. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem normalize_coordinateForm (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    normalize (coordinateForm x) = reconstruct x := by
  rw [coordinateForm, determinantNormalize,
    normalize_smul _ (Real.rpow_pos_of_pos hx.det_pos _).ne',
    normalize_of_trace_one _ (reconstruct_trace x)]

/-- The trace-one tangent matrix is the genuine differential of the inverse normalization. -/
theorem tangentMatrix_eq_normalized_formDerivative (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) : tangentMatrix u = normalizationDerivative (coordinateForm x) (formDerivative x u) := by
  have hn := (hasFDerivAt_normalize (coordinateForm x) (coordinateForm_positive x hx).trace_pos.ne').comp_hasDerivAt_of_eq
    0 (hasDerivAt_coordinateForm_line x hx u) (by simp only [zero_smul, add_zero])
  have he : (fun t : ℝ => reconstruct (x + t • u)) =ᶠ[nhds 0]
      (fun t : ℝ => normalize (coordinateForm (x + t • u))) := by
    filter_upwards [eventually_coordinateLine_positive x hx u] with t ht
    exact (normalize_coordinateForm (x + t • u) ht).symm
  have hh := hn.congr_of_eventuallyEq he
  exact (hasDerivAt_reconstruct_line x u).unique hh

theorem tangentPair_normalizationDerivative (Q : Mat) (hQ : Q.PosDef) (U V : Mat) :
    tangentPair (normalize Q) (normalizationDerivative Q U) (normalizationDerivative Q V) = tangentPair Q U V := by
  obtain ⟨S, hS⟩ := hQ.isUnit
  rw [normalizationDerivative_apply, normalizationDerivative_apply]
  change tangentPair (Q.trace⁻¹ • Q) (Q.trace⁻¹ • (U + (-Q.trace⁻¹ * U.trace) • Q))
    (Q.trace⁻¹ • (V + (-Q.trace⁻¹ * V.trace) • Q)) = _
  rw [← hS]
  rw [tangentPair_scale S _ _ _ (inv_ne_zero (by rw [hS]; exact hQ.trace_pos.ne')),
    tangentPair_add_radial]

/-- The tangent metric is exactly trace of the two true logarithmic tangents. -/
theorem coordinatePair_logarithmic (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    coordinatePair x u v = (logarithmicForm x u * logarithmicForm x v).trace := by
  rw [coordinatePair, ← normalize_coordinateForm x hx,
    tangentMatrix_eq_normalized_formDerivative x hx u, tangentMatrix_eq_normalized_formDerivative x hx v,
    tangentPair_normalizationDerivative _ (coordinateForm_positive x hx)]
  rw [tangentPair_formula]
  have hu : ((coordinateForm x)⁻¹ * formDerivative x u).trace = 0 := by
    rw [Matrix.trace_mul_comm]
    exact logarithmicForm_trace x hx u
  rw [hu, zero_mul, zero_div, sub_zero]
  simpa only [logarithmicForm, mul_assoc] using
    Matrix.trace_mul_comm (coordinateForm x)⁻¹
      (formDerivative x u * (coordinateForm x)⁻¹ * formDerivative x v)

end TernaryPoly.PolynomialFormConnection
