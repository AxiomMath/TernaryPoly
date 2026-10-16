module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.ContractionAlgebra

@[expose] public section


/-! Genuine metric contraction by the symmetric coefficient one-form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric SymmetricSpaceRiemannian
open SmoothCoveringDeRham ContinuousAlternatingMap
open scoped ContDiff Matrix.Norms.Elementwise

/-- The two tangent slots of metric contraction, before inverse-Gram summation. -/
def contractionBilinear (n k : ℕ) (x : Coordinates) (a : FormValue n (k + 1)) :
    Coordinates →ₗ[ℝ] Coordinates →ₗ[ℝ] FormValue n k where
  toFun u :=
    { toFun v := coefficientFormMap (symmetricPart n x u) k (a.curryLeft v)
      map_add' v w := by
        rw [map_add, map_add]
      map_smul' c v := by
        rw [map_smul, map_smul]
        rfl }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply ContinuousAlternatingMap.ext
    intro z
    change symmetricPart n x (u + v) (a (vecCons w z)) =
      symmetricPart n x u (a (vecCons w z)) + symmetricPart n x v (a (vecCons w z))
    rw [symmetricPart_add]
    rfl
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    apply ContinuousAlternatingMap.ext
    intro z
    change symmetricPart n x (c • u) (a (vecCons v z)) = c • symmetricPart n x u (a (vecCons v z))
    rw [symmetricPart_smul]
    rfl

/-- The actual contraction uses the inverse of the tangent metric. -/
def symmetricContraction (n k : ℕ) (x : Coordinates) (a : FormValue n (k + 1)) : FormValue n k :=
  bilinearContraction (contractionBilinear n k x a) (inverseGram x) (fun i => Pi.single i 1) (fun i => Pi.single i 1)

theorem symmetricContraction_apply (n k : ℕ) (x : Coordinates) (a : FormValue n (k + 1))
    (v : Fin k → Coordinates) :
    symmetricContraction n k x a v = ∑ i : Fin 5, ∑ j : Fin 5,
      inverseGram x i j • symmetricPart n x (Pi.single i 1) (a (vecCons (Pi.single j 1) v)) := by
  simp only [symmetricContraction, bilinearContraction, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply]
  rfl

theorem baseFrame_matrixAction :
    matrixAction (LinearMap.toMatrix' baseFrameMap.toLinearMap).transpose
      (fun i : Fin 5 => (Pi.single i 1 : Coordinates)) = baseFrame := by
  funext i
  ext j
  simp [matrixAction, LinearMap.toMatrix'_apply, baseFrameMap_single, Pi.single_apply]

/-- The inverse-Gram contraction is exactly the weighted orthogonal-frame contraction at the basepoint. -/
theorem symmetricContraction_basepoint_frame (n k : ℕ) (a : FormValue n (k + 1)) :
    symmetricContraction n k (coordinateChart basepoint) a = ∑ i : Fin 5, tangentWeight i •
      coefficientFormMap (symmetricPart n (coordinateChart basepoint) (baseFrame i)) k (a.curryLeft (baseFrame i)) := by
  have hG : (Matrix.diagonal (fun i => (tangentWeight i)⁻¹)).PosDef :=
    Matrix.PosDef.diagonal (fun i => inv_pos.mpr (tangentWeight_pos i))
  have hi := inverse_congruence _ _ _ hG baseFrame_gram
  rw [inverse_diagonal_pos tangentWeight tangentWeight_pos] at hi
  have hc := bilinearContraction_action (contractionBilinear n k (coordinateChart basepoint) a)
    (Matrix.diagonal tangentWeight) (LinearMap.toMatrix' baseFrameMap.toLinearMap).transpose
    (fun i : Fin 5 => (Pi.single i 1 : Coordinates)) (fun i : Fin 5 => (Pi.single i 1 : Coordinates))
  rw [baseFrame_matrixAction, Matrix.transpose_transpose, hi] at hc
  rw [symmetricContraction, inverseGram, ← hc]
  apply ContinuousAlternatingMap.ext
  intro z
  simp only [bilinearContraction, ContinuousAlternatingMap.sum_apply]
  change (∑ i : Fin 5, ∑ j : Fin 5, Matrix.diagonal tangentWeight i j •
      symmetricPart n (coordinateChart basepoint) (baseFrame i) (a (vecCons (baseFrame j) z))) =
    ∑ i : Fin 5, tangentWeight i •
      symmetricPart n (coordinateChart basepoint) (baseFrame i) (a (vecCons (baseFrame i) z))
  simp [Matrix.diagonal_apply]

end TernaryPoly.PolynomialFormGeometricEnergy
