module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.InverseGram

@[expose] public section

/-! Smooth concrete metric contraction and changes of tangent and coefficient frames. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCharts SmoothCoveringDeRham
open scoped ContDiff Matrix.Norms.Elementwise

/-- The literal normalized tensor contraction, with arbitrary coefficient and inverse tangent metrics. -/
def metricDataPairing (n k : ℕ) (B : Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ)
    (H : Matrix (Fin 5) (Fin 5) ℝ) (a b : FormValue n k) : ℝ :=
  (k.factorial : ℝ)⁻¹ * matrixContraction ((ContinuousLinearMap.coeLM ℝ).comp B.toLinearMap) (tensorMatrix k H) (formCoordinates a) (formCoordinates b)

@[simp] theorem metricDataPairing_actual (n k : ℕ) (x : Coordinates) (a b : FormValue n k) :
    metricDataPairing n k (coordinateCoefficientMetric n x) (inverseGram x) a b = formPairing n k x a b := rfl

theorem contDiff_metricDataPairing (n k : ℕ) (a b : FormValue n k) :
    ContDiff ℝ ∞ (fun z : (Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) × Matrix (Fin 5) (Fin 5) ℝ =>
      metricDataPairing n k z.1 z.2 a b) := by
  unfold metricDataPairing matrixContraction tensorMatrix
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro I _
  apply ContDiff.sum
  intro J _
  apply ContDiff.mul
  · apply contDiff_prod
    intro r _
    exact (contDiff_apply_apply ℝ ℝ (I r) (J r)).comp contDiff_snd
  · exact (contDiff_fst.clm_apply contDiff_const).clm_apply contDiff_const

theorem metricDataPairing_pullback (n k : ℕ) (B : Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ)
    (H : Matrix (Fin 5) (Fin 5) ℝ) (L : Coordinates →L[ℝ] Coordinates) (a b : FormValue n k) :
    metricDataPairing n k B H (a.compContinuousLinearMap L) (b.compContinuousLinearMap L) =
      metricDataPairing n k B
        (LinearMap.toMatrix' L.toLinearMap * H * (LinearMap.toMatrix' L.toLinearMap).transpose) a b := by
  exact congrArg ((k.factorial : ℝ)⁻¹ * ·) (contraction_pullback ((ContinuousLinearMap.coeLM ℝ).comp B.toLinearMap) H L a b)

theorem metricDataPairing_coefficient (n k : ℕ)
    (B : Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) (H : Matrix (Fin 5) (Fin 5) ℝ)
    (P : Coefficients n →L[ℝ] Coefficients n) (a b : FormValue n k) :
    metricDataPairing n k (B.bilinearComp P P) H a b =
      metricDataPairing n k B H (coefficientFormMap P k a) (coefficientFormMap P k b) := rfl

end TernaryPoly.PolynomialFormConnection
