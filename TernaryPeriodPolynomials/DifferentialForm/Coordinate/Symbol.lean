module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Basis
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

@[expose] public section



/-! Exact constant coordinate symbols for the actual exterior derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts ContinuousAlternatingMap

/-- Wedge with a fixed coordinate covector, defined by the exact Mathlib alternation map. -/
def symbol (n k : ℕ) (d : Fin 5) : FormValue n k →L[ℝ] FormValue n (k + 1) :=
  (alternatizeUncurryFinCLM ℝ Coordinates (Coefficients n) (n := k)).comp
    (ContinuousLinearMap.smulRightL ℝ Coordinates (FormValue n k) (ContinuousLinearMap.proj d))

/-- Every continuous linear derivative decomposes in the five actual coordinate directions. -/
theorem derivative_decomposition (n k : ℕ) (T : Coordinates →L[ℝ] FormValue n k) :
    T = ∑ d : Fin 5, (ContinuousLinearMap.proj d).smulRight (T (Pi.single d 1)) := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ d : Fin 5, v d • Pi.single d 1 := by ext d; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [_root_.map_sum, map_smul, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- This is an identity for the literal exterior derivative, not a new differential. -/
theorem extDeriv_symbol (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) :
    extDeriv w x = ∑ d : Fin 5, symbol n k d (fderiv ℝ w x (Pi.single d 1)) := by
  change (alternatizeUncurryFinCLM ℝ Coordinates (Coefficients n) (n := k)) (fderiv ℝ w x) = _
  conv_lhs => rw [derivative_decomposition n k (fderiv ℝ w x)]
  rw [clm_map_sum]
  rfl

/-- Constant scalar coefficient matrices in the chosen genuine finite form bases. -/
def symbolMatrix (n k : ℕ) (d : Fin 5) : Matrix (Index n (k + 1)) (Index n k) ℝ :=
  LinearMap.toMatrix' (((coordinates n (k + 1)).toContinuousLinearMap.comp
    ((symbol n k d).comp (coordinates n k).symm.toContinuousLinearMap)).toLinearMap)

/-- The constant symbol matrix represents the actual wedge operator. -/
theorem symbolMatrix_apply (n k : ℕ) (d : Fin 5) (a : FormValue n k) :
    (symbolMatrix n k d).mulVec (coordinates n k a) = coordinates n (k + 1) (symbol n k d a) := by
  rw [symbolMatrix, LinearMap.toMatrix'_mulVec]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- The matrix expression equals the actual exterior derivative in every degree. -/
theorem coordinates_extDeriv (n k : ℕ) (w : Coordinates → FormValue n k) (x : Coordinates) :
    coordinates n (k + 1) (extDeriv w x) =
      ∑ d : Fin 5, (symbolMatrix n k d).mulVec
        (coordinates n k (fderiv ℝ w x (Pi.single d 1))) := by
  rw [extDeriv_symbol, coordinates_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact (symbolMatrix_apply n k d _).symm

end TernaryPoly.PolynomialFormCoordinates
