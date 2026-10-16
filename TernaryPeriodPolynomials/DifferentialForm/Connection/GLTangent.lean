module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Exterior

@[expose] public section

/-! The actual GL orbit tangent and the factor between it and the metric frame. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric PolynomialFormMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem basepoint_scalar : basepoint.val = (1/3 : ℝ) • (1 : Mat) := by
  rw [basepoint_matrix]
  ext i j
  simp [Matrix.diagonal, Matrix.one_apply]

theorem hasDerivAt_matrix_transpose {A : ℝ → Mat} {R : Mat} {t : ℝ} (hA : HasDerivAt A R t) :
    HasDerivAt (fun s => (A s).transpose) R.transpose t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA j) i

theorem hasDerivAt_extract {A : ℝ → Mat} {R : Mat} {t : ℝ} (hA : HasDerivAt A R t) :
    HasDerivAt (fun s => extract (A s)) (extract R) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA 0) 0
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA 0) 1
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA 0) 2
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA 1) 1
  · exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA 1) 2

theorem hasDerivAt_conjugate_basepoint (g : ℝ → RealGL) (h0 : g 0 = 1)
    (A : Mat) (hA : HasDerivAt (fun t => (g t).val) A 0) (hAs : A.transpose = A) :
    HasDerivAt (fun t => conjugate (g t) basepoint.val) ((2/3 : ℝ) • A) 0 := by
  have hp := hasDerivAt_matrix_product
    (hasDerivAt_matrix_product hA (hasDerivAt_const (0 : ℝ) basepoint.val))
    (hasDerivAt_matrix_transpose hA)
  convert! hp using 1
  simp only [h0, GeneralLinearGroup.coe_one, Matrix.transpose_one, mul_zero, add_zero,
    one_mul, mul_one, hAs, basepoint_scalar, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  module

theorem hasDerivAt_normalized_conjugate_basepoint (g : ℝ → RealGL) (h0 : g 0 = 1)
    (A : Mat) (hA : HasDerivAt (fun t => (g t).val) A 0) (hAs : A.transpose = A) (hAt : A.trace = 0) :
    HasDerivAt (fun t => normalize (conjugate (g t) basepoint.val)) ((2/3 : ℝ) • A) 0 := by
  have hn := (hasFDerivAt_normalize basepoint.val (by rw [basepoint.property.2]; norm_num)).comp_hasDerivAt_of_eq
    0 (hasDerivAt_conjugate_basepoint g h0 A hA hAs) (by simp [conjugate, h0])
  convert! hn using 1
  change (2/3 : ℝ) • A = normalizationDerivative basepoint.val ((2/3 : ℝ) • A)
  rw [normalizationDerivative_apply]
  simp only [ basepoint.property.2, inv_one, Matrix.trace_smul,
    hAt, smul_eq_mul, mul_zero, zero_smul, add_zero, one_smul]

/-- A symmetric trace-zero GL generator A gives the genuine chart tangent 2 A/3. -/
theorem hasDerivAt_coordinateAction_basepoint (g : ℝ → RealGL) (h0 : g 0 = 1)
    (A : Mat) (hA : HasDerivAt (fun t => (g t).val) A 0) (hAs : A.transpose = A) (hAt : A.trace = 0) :
    HasDerivAt (fun t => coordinateAction (g t) (coordinateChart basepoint))
      ((2/3 : ℝ) • extract A) 0 := by
  have h := hasDerivAt_extract (hasDerivAt_normalized_conjugate_basepoint g h0 A hA hAs hAt)
  convert! h using 1
  · funext t
    rw [coordinateAction_formula, reconstruct_basepoint]
  · ext i
    fin_cases i <;> rfl

/-- Therefore the actual GL tangent is twice the metric base frame. -/
theorem hasDerivAt_coordinateAction_baseFrame (g : ℝ → RealGL) (h0 : g 0 = 1) (i : Fin 5)
    (hA : HasDerivAt (fun t => (g t).val) (tangentFrame i) 0) :
    HasDerivAt (fun t => coordinateAction (g t) (coordinateChart basepoint)) ((2 : ℝ) • baseFrame i) 0 := by
  have h := hasDerivAt_coordinateAction_basepoint g h0 (tangentFrame i) hA
    (tangentFrame_mem i).1 (tangentFrame_mem i).2
  convert h using 1
  simp [baseFrame, smul_smul, div_eq_mul_inv]

/-- In the genuine GL tangent direction, the connection is the full infinitesimal action. -/
theorem symmetricPart_GL_tangent (n : ℕ) (i : Fin 5) :
    symmetricPart n (coordinateChart basepoint) ((2 : ℝ) • baseFrame i) =
      infinitesimalCLM n (tangentFrame i) := by
  apply ContinuousLinearMap.ext
  intro p
  change (1/2 : ℝ) • coefficientInfinitesimal n
    (logarithmicForm (coordinateChart basepoint) ((2 : ℝ) • baseFrame i)) p =
    coefficientInfinitesimal n (tangentFrame i) p
  rw [logarithmicForm_smul, logarithmicForm_baseFrame, coefficientInfinitesimal_smul]
  module

end TernaryPoly.PolynomialFormConnection
