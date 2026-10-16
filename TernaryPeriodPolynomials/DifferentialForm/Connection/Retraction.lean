module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tangent.Correction
public import TernaryPeriodPolynomials.DifferentialForm.Connection.Deck

@[expose] public section


/-! The actual inverse coordinate differential on the determinant-one symmetric locus. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- The inverse chart on positive determinant-one symmetric matrices. -/
def matrixChart (Q : Mat) : Coordinates := extract (normalize Q)

theorem matrixChart_coordinateForm (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    matrixChart (coordinateForm x) = x := by
  rw [matrixChart, coordinateForm, determinantNormalize,
    normalize_smul _ (Real.rpow_pos_of_pos hx.det_pos _).ne',
    normalize_of_trace_one _ (reconstruct_trace x), extract_reconstruct]

theorem determinantNormalize_smul_of_det_pos (r : ℝ) (hr : 0 < r) (S : Mat) (hS : 0 < S.det) :
    determinantNormalize (r • S) = determinantNormalize S := by
  unfold determinantNormalize
  rw [Matrix.det_smul, Fintype.card_fin, Real.mul_rpow (pow_nonneg hr.le 3) hS.le,
    ← Real.rpow_natCast_mul hr.le 3 (-(1/3 : ℝ))]
  norm_num only [Nat.cast_ofNat, show (3 : ℝ)*(-(1/3 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  rw [smul_smul]
  congr 1
  field_simp [hr.ne']

theorem coordinateForm_matrixChart (Q : Mat) (hQs : Q.transpose = Q) (hQt : 0 < Q.trace)
    (hQd : 0 < Q.det) : coordinateForm (matrixChart Q) = determinantNormalize Q := by
  have hns : (normalize Q).IsSymm := (show Q.IsSymm from hQs).smul Q.trace⁻¹
  have hnt : (normalize Q).trace = 1 := by
    change (Q.trace⁻¹ • Q).trace = 1
    rw [Matrix.trace_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hQt.ne'
  rw [coordinateForm, matrixChart, reconstruct_extract (normalize Q) hns hnt]
  exact determinantNormalize_smul_of_det_pos Q.trace⁻¹ (inv_pos.mpr hQt) Q hQd

theorem hasDerivAt_matrixAffine (Q W : Mat) : HasDerivAt (fun t : ℝ => Q + t • W) W 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  convert! (hasDerivAt_const (0 : ℝ) (Q i j)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (W i j)) using 1
  simp

/-- The matrix chart is genuinely differentiated using the trace-normalization derivative. -/
theorem hasDerivAt_matrixChart_affine (Q W : Mat) (hQt : Q.trace ≠ 0) :
    HasDerivAt (fun t : ℝ => matrixChart (Q + t • W)) (extract (normalizationDerivative Q W)) 0 := by
  have h := (hasFDerivAt_normalize Q hQt).comp_hasDerivAt_of_eq 0 (hasDerivAt_matrixAffine Q W)
    (by simp only [zero_smul, add_zero])
  apply hasDerivAt_extract
  convert! h using 1

/-- Determinant normalization has derivative the identity on its genuine trace-free tangent. -/
theorem hasDerivAt_determinantNormalize_tangent (Q W : Mat) (hQ : Q.det = 1)
    (hW : (W * Q⁻¹).trace = 0) :
    HasDerivAt (fun t : ℝ => determinantNormalize (Q + t • W)) W 0 := by
  have hd := hasDerivAt_det_one _ W (hasDerivAt_matrixAffine Q W)
    (by simpa only [zero_smul, add_zero] using hQ)
  have hWi : (Q⁻¹ * W).trace = 0 := by rw [Matrix.trace_mul_comm]; exact hW
  have hd' : HasDerivAt (fun t : ℝ => (Q + t • W).det) 0 0 := by
    simpa only [zero_smul, add_zero, hWi] using hd
  have hp := hd'.rpow_const (p := -(1/3 : ℝ)) (Or.inl (by simp [hQ]))
  have hp' : HasDerivAt (fun t : ℝ => (Q + t • W).det ^ (-(1/3 : ℝ))) 0 0 := by
    simpa only [zero_mul] using hp
  have h := hp'.smul (hasDerivAt_matrixAffine Q W)
  convert! h using 1
  simp [hQ]

/-- The positive determinant and trace conditions needed for the literal retraction hold near zero. -/
theorem eventually_matrixAffine_positive_det_trace (Q W : Mat) (hQd : 0 < Q.det) (hQt : 0 < Q.trace) :
    ∀ᶠ t : ℝ in nhds 0, 0 < (Q + t • W).det ∧ 0 < (Q + t • W).trace := by
  have hd := (hasDerivAt_det_adjugate _ W (hasDerivAt_matrixAffine Q W)).continuousAt
  have ht := (traceCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_matrixAffine Q W)).continuousAt
  have hdp := continuousAt_const.eventually_lt hd (by simpa using hQd)
  have htp := continuousAt_const.eventually_lt ht (by simpa using hQt)
  exact hdp.and htp

/-- The inverse coordinate differential recovers every genuine symmetric determinant-one tangent. -/
theorem formDerivative_matrixChart_tangent (x : Coordinates) (hx : x ∈ positiveCoordinates) (W : Mat)
    (hWs : W.transpose = W) (hWt : (W * (coordinateForm x)⁻¹).trace = 0) :
    formDerivative x (extract (normalizationDerivative (coordinateForm x) W)) = W := by
  have hQ := coordinateForm_positive x hx
  have hK := hasDerivAt_matrixChart_affine (coordinateForm x) W hQ.trace_pos.ne'
  have h := (coordinateForm_differentiable x hx).hasFDerivAt.comp_hasDerivAt_of_eq 0 hK
    (by simpa only [zero_smul, add_zero] using (matrixChart_coordinateForm x hx).symm)
  have he : (fun t : ℝ => determinantNormalize (coordinateForm x + t • W)) =ᶠ[nhds 0]
      (fun t : ℝ => coordinateForm (matrixChart (coordinateForm x + t • W))) := by
    filter_upwards [eventually_matrixAffine_positive_det_trace (coordinateForm x) W hQ.det_pos hQ.trace_pos]
      with t ht
    exact (coordinateForm_matrixChart _
      (by simp only [Matrix.transpose_add, Matrix.transpose_smul, coordinateForm_symmetric, hWs]) ht.2 ht.1).symm
  have hh := h.congr_of_eventuallyEq he
  exact hh.unique (hasDerivAt_determinantNormalize_tangent (coordinateForm x) W (coordinateForm_det x hx) hWt)

end TernaryPoly.PolynomialFormConnection
