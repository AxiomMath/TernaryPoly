module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFirstProjection_binary (real : ℝ × ℝ) (pivot : real.2 ≠ 0) :
    (realPlaneFirstProjection (standardGoodLineRealArgument real)).right.val =
      !![0, 1; -(1 : ℝ) / real.2, -real.1 / real.2] := by
  funext row column
  rw [← realPlaneMatrix_binary_entry, goodLineFirstProjection_base real pivot]
  fin_cases row <;> fin_cases column <;> rfl

theorem goodLineFirstProjection_radical (real : ℝ × ℝ) (pivot : real.2 ≠ 0) :
    (realPlaneFirstProjection (standardGoodLineRealArgument real)).left =
      Multiplicative.ofAdd ![0, 1 / real.2] := by
  apply Multiplicative.toAdd.injective
  funext row
  rw [← realPlaneMatrix_radical_entry, goodLineFirstProjection_base real pivot]
  fin_cases row <;> rfl

def goodLineFirstTransition (first second : ℝ × ℝ) : RealPlaneGroup :=
  ⟨Multiplicative.ofAdd ![1 - first.2 / second.2, 0],
    invertibleMatrix !![first.2 / second.2, first.2 * second.1 / second.2 - first.1; 0, 1]⟩

theorem goodLineFirstTransition_matrix (first second : ℝ × ℝ)
    (first_pivot : first.2 ≠ 0) (second_pivot : second.2 ≠ 0) :
    (realPlaneMatrix (goodLineFirstTransition first second)).val =
      !![first.2 / second.2, first.2 * second.1 / second.2 - first.1, 1 - first.2 / second.2;
        0, 1, 0; 0, 0, 1] := by
  have determinant : (!![first.2 / second.2,
      first.2 * second.1 / second.2 - first.1; 0, 1] : BinaryRealMatrix).det ≠ 0 := by
    simpa [Matrix.det_fin_two] using div_ne_zero first_pivot second_pivot
  have block := invertibleMatrix_val _ determinant
  rw [realPlaneMatrix_apply]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [goodLineFirstTransition, realPlaneRadicalMatrix, planeUnipotent, planeLevi,
      planeBlock, Matrix.mul_apply, Fin.sum_univ_three, block]

theorem goodLineFirstProjection_transition (first second : ℝ × ℝ)
    (first_pivot : first.2 ≠ 0) (second_pivot : second.2 ≠ 0) :
    (realPlaneFirstProjection (standardGoodLineRealArgument first))⁻¹ *
        realPlaneFirstProjection (standardGoodLineRealArgument second) =
      goodLineFirstTransition first second := by
  apply (inv_mul_eq_iff_eq_mul).mpr
  apply realPlaneMatrix_injective
  apply Units.ext
  rw [map_mul, GeneralLinearGroup.coe_mul, goodLineFirstProjection_base first first_pivot,
    goodLineFirstProjection_base second second_pivot,
    goodLineFirstTransition_matrix first second first_pivot second_pivot]
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
