module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Symbol
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FormalAdjoint

@[expose] public section


/-! Identification of the genuine exterior derivative with the proved coordinate operator. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration

/-- Scalar components in a genuine finite basis of the alternating-form fiber. -/
def components (n k : ℕ) (w : Coordinates → FormValue n k) (i : Index n k) (x : Coordinates) : ℝ :=
  coordinates n k (w x) i

/-- The actual derivative coefficient matrices are constant in this fixed affine coordinate frame. -/
def differentialCoefficients (n k : ℕ) (j : Index n (k + 1)) (i : Index n k)
    (d : Fin 5) (_x : Coordinates) : ℝ := symbolMatrix n k d j i

/-- Differentiating actual scalar components equals taking components of the actual derivative. -/
theorem fderiv_components (n k : ℕ) (w : Coordinates → FormValue n k) {x : Coordinates}
    (hw : DifferentiableAt ℝ w x) (i : Index n k) (v : Coordinates) :
    fderiv ℝ (components n k w i) x v = coordinates n k (fderiv ℝ w x v) i := by
  let L : FormValue n k →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (coordinates n k).toContinuousLinearMap
  have hL : HasFDerivAt L L (w x) := L.hasFDerivAt
  have h := HasFDerivAt.comp (𝕜 := ℝ) (E := Coordinates) (F := FormValue n k) (G := ℝ)
    (f := w) (g := L) x hL hw.hasFDerivAt
  change HasFDerivAt (components n k w i) (L.comp (fderiv ℝ w x)) x at h
  rw [h.fderiv]
  rfl

/-- The finite first-order formula proved integrable earlier is the literal exterior derivative. -/
theorem extDeriv_eq_matrixFirstOrder (n k : ℕ) (w : Coordinates → FormValue n k)
    {x : Coordinates} (hw : DifferentiableAt ℝ w x) (j : Index n (k + 1)) :
    components n (k + 1) (extDeriv w) j x =
      matrixFirstOrder (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k)
        (fun _ _ _ _ => 0) (components n k w) j x := by
  change (coordinates n (k + 1) (extDeriv w x)) j = _
  rw [coordinates_extDeriv]
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, matrixFirstOrder, firstOrder,
    differentialCoefficients, zero_mul, add_zero]
  simp_rw [fderiv_components n k w hw]
  exact Finset.sum_comm

end TernaryPoly.PolynomialFormCoordinates
