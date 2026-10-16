module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Basis

@[expose] public section


/-! Explicit standard operator norms for the true finite form coordinate maps. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric

instance inverseCoordinateOperatorNorm (n k : ℕ) :
    NormedAddCommGroup ((Index n k → ℝ) →L[ℝ] FormValue n k) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Index n k → ℝ) (F := FormValue n k)

instance coordinateOperatorNorm (n k : ℕ) :
    NormedAddCommGroup (FormValue n k →L[ℝ] (Index n k → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := FormValue n k) (F := Index n k → ℝ)

end TernaryPoly.PolynomialFormCoordinates
