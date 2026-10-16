module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneOpenProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneFirstProjection (matrix : RealGL3) : RealPlaneGroup :=
  realPlaneOpenProjection
    (matrix * GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine)

theorem realPlaneFirstProjection_pivot (matrix : RealGL3) :
    (matrix * GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine).val 2 2 = matrix.val 2 0 := by
  simp [rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

theorem realPlaneFirstProjection_equivariant (element : RealPlaneGroup) (matrix : RealGL3)
    (pivot : matrix.val 2 0 ≠ 0) :
    realPlaneFirstProjection (realPlaneMatrix element * matrix) = element * realPlaneFirstProjection matrix := by
  unfold realPlaneFirstProjection
  rw [mul_assoc]
  apply realPlaneOpenProjection_equivariant
  rwa [realPlaneFirstProjection_pivot]

theorem goodLineFirstChart_matrix (real : ℝ × ℝ) (block : BinaryRealGL) :
    (standardGoodLineRealArgument real * planeLevi block 1 *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine).val =
    !![0, block.val 1 1, block.val 1 0;
      0, block.val 0 1, block.val 0 0;
      1, real.2 * block.val 0 1 + real.1 * block.val 1 1,
        real.2 * block.val 0 0 + real.1 * block.val 1 0] := by
  simp only [GeneralLinearGroup.coe_mul, standardGoodLineRealArgument_val]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeLevi, planeBlock, rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

theorem goodLineFirstProjection_matrix (real : ℝ × ℝ) (block : BinaryRealGL)
    (pivot : real.2 * block.val 0 0 + real.1 * block.val 1 0 ≠ 0) :
    let denominator := real.2 * block.val 0 0 + real.1 * block.val 1 0
    (realPlaneMatrix (realPlaneFirstProjection (standardGoodLineRealArgument real * planeLevi block 1))).val =
      !![-block.val 1 0 / denominator, real.2 * block.val.det / denominator, block.val 1 0 / denominator;
        -block.val 0 0 / denominator, -real.1 * block.val.det / denominator, block.val 0 0 / denominator;
        0, 0, 1] := by
  have nonzero : (standardGoodLineRealArgument real * planeLevi block 1 *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine).val 2 2 ≠ 0 := by
    rw [goodLineFirstChart_matrix]
    exact pivot
  have first : block.val 1 1 - block.val 1 0 *
      (real.2 * block.val 0 1 + real.1 * block.val 1 1) /
        (real.2 * block.val 0 0 + real.1 * block.val 1 0) =
      real.2 * block.val.det / (real.2 * block.val 0 0 + real.1 * block.val 1 0) := by
    apply (eq_div_iff pivot).mpr
    rw [sub_mul, div_mul_cancel₀ _ pivot, Matrix.det_fin_two]
    ring
  have second : block.val 0 1 - block.val 0 0 *
      (real.2 * block.val 0 1 + real.1 * block.val 1 1) /
        (real.2 * block.val 0 0 + real.1 * block.val 1 0) =
      -real.1 * block.val.det / (real.2 * block.val 0 0 + real.1 * block.val 1 0) := by
    apply (eq_div_iff pivot).mpr
    rw [sub_mul, div_mul_cancel₀ _ pivot, Matrix.det_fin_two]
    ring
  rw [realPlaneFirstProjection, realPlaneOpenProjection_matrix _ nonzero, goodLineFirstChart_matrix]
  dsimp only
  funext row column
  fin_cases row <;> fin_cases column
  · change (0 : ℝ) - block.val 1 0 * 1 /
        (real.2 * block.val 0 0 + real.1 * block.val 1 0) =
      -block.val 1 0 / (real.2 * block.val 0 0 + real.1 * block.val 1 0)
    ring
  · exact first
  · rfl
  · change (0 : ℝ) - block.val 0 0 * 1 /
        (real.2 * block.val 0 0 + real.1 * block.val 1 0) =
      -block.val 0 0 / (real.2 * block.val 0 0 + real.1 * block.val 1 0)
    ring
  · exact second
  · rfl
  · rfl
  · rfl
  · rfl

theorem goodLineFirstProjection_base (real : ℝ × ℝ) (pivot : real.2 ≠ 0) :
    (realPlaneMatrix (realPlaneFirstProjection (standardGoodLineRealArgument real))).val =
      !![0, 1, 0; -(1 : ℝ) / real.2, -real.1 / real.2, 1 / real.2; 0, 0, 1] := by
  have block : planeLevi (1 : BinaryRealGL) 1 = (1 : RealGL3) := (planeLeviHom ℝ).map_one
  have nonzero : real.2 * (1 : BinaryRealMatrix) 0 0 + real.1 * (1 : BinaryRealMatrix) 1 0 ≠ 0 := by
    simpa using pivot
  simpa [block, pivot] using goodLineFirstProjection_matrix real 1 nonzero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
