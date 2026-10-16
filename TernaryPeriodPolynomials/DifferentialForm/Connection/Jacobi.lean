module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Exterior

@[expose] public section

/-! Jacobi differentiation and tracelessness of the genuine normalized logarithmic form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- Direct differentiation of the determinant gives its adjugate pairing. -/
theorem hasDerivAt_det_adjugate (A : ℝ → Mat) (R : Mat) (hA : HasDerivAt A R 0) :
    HasDerivAt (fun t => (A t).det) ((A 0).adjugate * R).trace 0 := by
  have h (i j : Fin 3) : HasDerivAt (fun t => A t i j) (R i j) 0 :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j
  have hd := ((((((h 0 0).mul (h 1 1)).mul (h 2 2)).sub
    (((h 0 0).mul (h 1 2)).mul (h 2 1))).sub
    (((h 0 1).mul (h 1 0)).mul (h 2 2))).add
    (((h 0 1).mul (h 1 2)).mul (h 2 0))).add
    (((h 0 2).mul (h 1 0)).mul (h 2 1))
  have he := hd.sub (((h 0 2).mul (h 1 1)).mul (h 2 0))
  convert! he using 1
  · funext t
    exact Matrix.det_fin_three (A t)
  · simp [Matrix.adjugate_fin_three, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    ring

/-- At determinant one, the adjugate is the genuine matrix inverse. -/
theorem inverse_eq_adjugate_of_det_one (Q : Mat) (hQ : Q.det = 1) : Q⁻¹ = Q.adjugate := by
  rw [Matrix.inv_def, hQ]
  simp

/-- Jacobi's formula in precisely the determinant-one locus used by the coefficient metric. -/
theorem hasDerivAt_det_one (A : ℝ → Mat) (R : Mat) (hA : HasDerivAt A R 0) (h0 : (A 0).det = 1) :
    HasDerivAt (fun t => (A t).det) ((A 0)⁻¹ * R).trace 0 := by
  rw [inverse_eq_adjugate_of_det_one _ h0]
  exact hasDerivAt_det_adjugate A R hA

theorem coordinateForm_det (x : Coordinates) (hx : x ∈ positiveCoordinates) : (coordinateForm x).det = 1 :=
  determinantNormalize_det (reconstruct x) hx

/-- The actual normalized logarithmic differential is trace-free everywhere. -/
theorem logarithmicForm_trace (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    (logarithmicForm x v).trace = 0 := by
  have h0 : (coordinateForm (x + (0 : ℝ) • v)).det = 1 := by
    simpa only [zero_smul, add_zero] using coordinateForm_det x hx
  have hd := hasDerivAt_det_one _ _ (hasDerivAt_coordinateForm_line x hx v) h0
  have he : (fun _ : ℝ => (1 : ℝ)) =ᶠ[nhds 0]
      (fun t : ℝ => (coordinateForm (x + t • v)).det) := by
    filter_upwards [eventually_coordinateLine_positive x hx v] with t ht
    exact (coordinateForm_det (x + t • v) ht).symm
  have hc := hd.congr_of_eventuallyEq he
  have hz := hc.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  rw [logarithmicForm, Matrix.trace_mul_comm]
  simpa only [zero_smul, add_zero] using hz

/-- The trace of the actual derivative of C(v) vanishes as well. -/
theorem logarithmicDerivative_trace (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    (logarithmicDerivative x u v).trace = 0 := by
  have hd := (((contDiffOn_logarithmicForm v x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hl := hasDerivAt_matrixField_line _ x u hd
  have ht := traceCLM.hasFDerivAt.comp_hasDerivAt 0 hl
  have he : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds 0]
      (fun t : ℝ => (logarithmicForm (x + t • u) v).trace) := by
    filter_upwards [eventually_coordinateLine_positive x hx u] with t hu
    exact (logarithmicForm_trace (x + t • u) hu v).symm
  have hc := ht.congr_of_eventuallyEq he
  exact hc.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))

end TernaryPoly.PolynomialFormConnection
