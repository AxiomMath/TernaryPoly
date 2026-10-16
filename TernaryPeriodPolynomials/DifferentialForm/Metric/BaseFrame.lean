module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Naturality

@[expose] public section

/-! The exact B=tr tangent frame at the normalized identity, in genuine chart coordinates. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceTraceMetric
open SymmetricSpaceCovering SymmetricSpaceRiemannian PolynomialCoefficientMetric SL3PolynomialCoercivity
open scoped Matrix.Norms.Elementwise

/-- At S=I/3 the logarithmic tangent A corresponds to the chart tangent A/3. -/
def baseFrame (i : Fin 5) : Coordinates := (1/3 : ℝ) • extract (tangentFrame i)

theorem tangentMatrix_baseFrame (i : Fin 5) :
    tangentMatrix (baseFrame i) = (1/3 : ℝ) • tangentFrame i := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [baseFrame, tangentMatrix, extract, tangentFrame, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem basepoint_matrix : basepoint.val = Matrix.diagonal (fun _ : Fin 3 => (1/3 : ℝ)) := by
  ext i j
  simp [basepoint, SymmetricSpacePositive.normalize, Matrix.trace, Matrix.diagonal, Matrix.one_apply]

theorem basepoint_matrix_inverse : basepoint.val⁻¹ = (3 : ℝ) • (1 : SymmetricSpacePositive.Mat) := by
  apply Matrix.inv_eq_left_inv
  rw [basepoint_matrix]
  ext i j
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.one_apply]

theorem reconstruct_basepoint : reconstruct (coordinateChart basepoint) = basepoint.val :=
  reconstruct_extract basepoint.val (Matrix.isHermitian_iff_isSymm.mp basepoint.property.1.isHermitian)
    basepoint.property.2

/-- No factor is suppressed: the true chart tangent metric is exactly tr(A B) on this frame. -/
theorem baseFrame_pair (i j : Fin 5) :
    coordinatePair (coordinateChart basepoint) (baseFrame i) (baseFrame j) =
      Matrix.trace (tangentFrame i * tangentFrame j) := by
  rw [coordinatePair, reconstruct_basepoint, tangentPair, basepoint_matrix_inverse,
    tangentMatrix_baseFrame, tangentMatrix_baseFrame]
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul]
  norm_num
  rw [tracePair_formula, (tangentFrame_mem i).2, (tangentFrame_mem j).2]
  ring

theorem baseFrame_orthogonal (i j : Fin 5) :
    coordinatePair (coordinateChart basepoint) (baseFrame i) (baseFrame j) =
      Matrix.diagonal (fun i => (tangentWeight i)⁻¹) i j := by
  rw [baseFrame_pair]
  have h := tangentFrame_orthogonal i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    apply mul_left_cancel₀ (tangentWeight_pos i).ne'
    simpa [(tangentWeight_pos i).ne'] using h
  · simp only [ite_eq_right hij] at h
    rw [Matrix.diagonal_apply_ne _ hij]
    exact (mul_eq_zero.mp h).resolve_left (tangentWeight_pos i).ne'

/-- Linear coordinate change with columns the B=tr tangent frame. -/
def baseFrameMap : Coordinates →L[ℝ] Coordinates :=
  (Matrix.toLin' (fun i j : Fin 5 => baseFrame j i)).toContinuousLinearMap

@[simp] theorem baseFrameMap_single (i : Fin 5) : baseFrameMap (Pi.single i 1) = baseFrame i := by
  ext j
  change (∑ l : Fin 5, baseFrame l j * (Pi.single i (1 : ℝ) : Coordinates) l) = baseFrame i j
  simp [Pi.single_apply]

theorem baseFrame_gram :
    (LinearMap.toMatrix' baseFrameMap.toLinearMap).transpose * coordinateGram (coordinateChart basepoint) *
      LinearMap.toMatrix' baseFrameMap.toLinearMap = Matrix.diagonal (fun i => (tangentWeight i)⁻¹) := by
  have h := LinearMap.BilinForm.toMatrix'_comp (coordinateBilin (coordinateChart basepoint))
    baseFrameMap.toLinearMap baseFrameMap.toLinearMap
  unfold coordinateGram
  rw [← h]
  ext i j
  change coordinatePair (coordinateChart basepoint)
    (baseFrameMap (Pi.single i 1)) (baseFrameMap (Pi.single j 1)) = _
  rw [baseFrameMap_single, baseFrameMap_single, baseFrame_orthogonal]

end TernaryPoly.PolynomialFormMetric
