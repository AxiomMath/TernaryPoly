module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.Algebra

@[expose] public section


/-! Actual derivative rules for tensor coefficient composition and insertion. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormGeometricEnergy
open SymmetricSpaceCharts SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem fderiv_formCLM (n k l : ℕ) (L : FormValue n k →L[ℝ] FormValue n l)
    (w : Coordinates → FormValue n k) (x u : Coordinates) (hw : DifferentiableAt ℝ w x) :
    fderiv ℝ (fun y => L (w y)) x u = L (fderiv ℝ w x u) := by
  have hL : HasFDerivAt L L (w x) := L.hasFDerivAt
  have h := HasFDerivAt.comp (𝕜 := ℝ) (E := Coordinates) (F := FormValue n k) (G := FormValue n l)
    (f := w) (g := L) x hL hw.hasFDerivAt
  exact congrArg (fun A => A u) h.fderiv

/-- Insertion differentiates with the actual tangent correction in its inserted slot. -/
theorem covariantFormDerivative_insertion (n k : ℕ) (w : Coordinates → FormValue n (k + 1))
    (x u v : Coordinates) (hw : DifferentiableAt ℝ w x) :
    covariantFormDerivative n k (fun y => insertion n k v (w y)) x u =
      insertion n k v (covariantFormDerivative n (k + 1) w x u) +
        insertion n k (tangentConnection x u v) (w x) := by
  simp only [covariantFormDerivative, fderiv_formCLM n (k + 1) k (insertion n k v) w x u hw,
    PolynomialFormCoordinates.clm_map_add, PolynomialFormCoordinates.clm_map_sub,
    ← coefficientFormMap_insertion, tangentFormAction_insertion]
  abel

theorem fderiv_coefficientFormMap_apply (n k : ℕ) (L : Coordinates → Coefficients n →L[ℝ] Coefficients n)
    (w : Coordinates → FormValue n k) (x u : Coordinates) (hL : DifferentiableAt ℝ L x)
    (hw : DifferentiableAt ℝ w x) :
    fderiv ℝ (fun y => coefficientFormMap (L y) k (w y)) x u =
      coefficientFormMap (L x) k (fderiv ℝ w x u) + coefficientFormMap (fderiv ℝ L x u) k (w x) := by
  let B := ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ Coordinates (Coefficients n) (Coefficients n)
    (Fin k)
  have h := ContinuousLinearMap.fderiv_of_bilinear (𝕜 := ℝ)
    (E := Coefficients n →L[ℝ] Coefficients n) (F := FormValue n k) (G := FormValue n k) (G' := Coordinates)
    (by convert! B using 1) (f := L) (g := w) (x := x)
    (by convert! hL using 1) (by convert! hw using 1)
  have he := congrArg (fun A => A u) h
  convert! he using 1

end TernaryPoly.PolynomialFormConnection
