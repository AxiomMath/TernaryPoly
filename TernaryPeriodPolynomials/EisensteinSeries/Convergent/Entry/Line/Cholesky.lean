module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Iwasawa

@[expose] public section


/-!
# Explicit Cholesky factor in the line parabolic

For a symmetric `3 × 3` matrix `P` with `0 < P₂₂`, `0 < P₁₁P₂₂ - P₁₂²`, `0 < det P`, the explicit upper triangular
factor `cholLine P = [[a, bᵀ], [0, C]]` (`C` upper triangular, `a > 0`, `det C > 0`) satisfies
`cholLine P · (cholLine P)ᵀ = P` (`cholLine_mul_transpose`); it is a continuous function of `P` on this open set
(its entries are given by square roots and quotients with positive denominators).  It is the frame in which the form
identity is applied to the points of a Gram simplex.

Formalized by Claude Sonnet 5.5.
-/

open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

section Cholesky

variable (P : Mat3)

/-- The entries of the explicit upper triangular Cholesky factor of a positive definite `P = Q Qᵀ`
(`Q = [[a, bᵀ], [0, C]]` with `C` upper triangular). -/
def cholC11 : ℝ := Real.sqrt (P 2 2)
def cholC00 : ℝ := Real.sqrt ((P 1 1 * P 2 2 - P 1 2 ^ 2) / P 2 2)
def cholA : ℝ := Real.sqrt (P.det / (P 1 1 * P 2 2 - P 1 2 ^ 2))
def cholB1 : ℝ := P 0 2 / cholC11 P
def cholC01 : ℝ := P 1 2 / cholC11 P
def cholB0 : ℝ := (P 0 1 - P 0 2 / cholC11 P * (P 1 2 / cholC11 P)) / cholC00 P

/-- The Cholesky factor of a positive definite matrix, in the line parabolic. -/
def cholLine : Mat3 :=
  !![cholA P, cholB0 P, cholB1 P; 0, cholC00 P, cholC01 P; 0, 0, cholC11 P]


theorem upper_gram_of_params (P : Mat3) (a b0 b1 c00 c01 c11 : ℝ) (hsym : ∀ i j, P j i = P i j)
    (h1 : c11 ^ 2 = P 2 2) (h2 : c01 * c11 = P 1 2) (h3 : b1 * c11 = P 0 2)
    (h4 : c00 ^ 2 + c01 ^ 2 = P 1 1) (h5 : b0 * c00 + b1 * c01 = P 0 1)
    (h6 : a ^ 2 + b0 ^ 2 + b1 ^ 2 = P 0 0) :
    !![a, b0, b1; 0, c00, c01; 0, 0, c11] * (!![a, b0, b1; 0, c00, c01; 0, 0, c11])ᵀ = P := by
  have e10 := hsym 1 0
  have e20 := hsym 2 0
  have e21 := hsym 2 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first | linear_combination h6 | linear_combination h5 | linear_combination h3 |
    linear_combination h4 | linear_combination h2 | linear_combination h1 |
    linear_combination h5 + e10 | linear_combination h3 + e20 | linear_combination h2 + e21

theorem cholLine_mul_transpose (hP : Pᵀ = P) (hs : 0 < P 2 2) (hD : 0 < P 1 1 * P 2 2 - P 1 2 ^ 2)
    (hdet : 0 < P.det) : cholLine P * (cholLine P)ᵀ = P := by
  have hsym : ∀ i j, P j i = P i j := fun i j => by
    simpa using congrFun (congrFun hP i) j
  have hDs : 0 < (P 1 1 * P 2 2 - P 1 2 ^ 2) / P 2 2 := div_pos hD hs
  have hα : 0 < P.det / (P 1 1 * P 2 2 - P 1 2 ^ 2) := div_pos hdet hD
  have c11pos : 0 < cholC11 P := Real.sqrt_pos.mpr hs
  have c00pos : 0 < cholC00 P := Real.sqrt_pos.mpr hDs
  have c11sq : cholC11 P ^ 2 = P 2 2 := Real.sq_sqrt hs.le
  have c00sq : cholC00 P ^ 2 = (P 1 1 * P 2 2 - P 1 2 ^ 2) / P 2 2 := Real.sq_sqrt hDs.le
  have asq : cholA P ^ 2 = P.det / (P 1 1 * P 2 2 - P 1 2 ^ 2) := Real.sq_sqrt hα.le
  have hdetP := Matrix.det_fin_three P
  have e10 := hsym 0 1
  have e20 := hsym 0 2
  have e21 := hsym 1 2
  have c11ne := c11pos.ne'
  have c00ne := c00pos.ne'
  have hsne := hs.ne'
  have hDne := hD.ne'
  refine upper_gram_of_params P _ _ _ _ _ _ hsym c11sq ?_ ?_ ?_ ?_ ?_
  · unfold cholC01; exact div_mul_cancel₀ _ c11ne
  · unfold cholB1; exact div_mul_cancel₀ _ c11ne
  · have hc01 : cholC01 P ^ 2 = P 1 2 ^ 2 / P 2 2 := by
      unfold cholC01; rw [div_pow, c11sq]
    rw [c00sq, hc01]
    field_simp
    ring
  · have hb0c : cholB0 P * cholC00 P = P 0 1 - P 0 2 / cholC11 P * (P 1 2 / cholC11 P) := by
      unfold cholB0; exact div_mul_cancel₀ _ c00ne
    unfold cholB1 cholC01
    linear_combination hb0c
  · have hb0 : cholB0 P ^ 2 = (P 0 1 - P 0 2 / cholC11 P * (P 1 2 / cholC11 P)) ^ 2 / cholC00 P ^ 2 := by
      unfold cholB0; rw [div_pow]
    have hb1 : cholB1 P ^ 2 = P 0 2 ^ 2 / P 2 2 := by
      unfold cholB1; rw [div_pow, c11sq]
    rw [asq, hb0, hb1, c00sq, hdetP, e10, e20, e21]
    have e : (P 0 1 - P 0 2 / cholC11 P * (P 1 2 / cholC11 P)) = (P 0 1 * P 2 2 - P 0 2 * P 1 2) / P 2 2 := by
      field_simp
      rw [c11sq]
      ring
    rw [e]
    field_simp
    ring

theorem cholLine_eq : cholLine P = lineParabolic (cholA P) ![cholB0 P, cholB1 P]
    !![cholC00 P, cholC01 P; 0, cholC11 P] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cholLine, lineParabolic]

theorem cholA_pos (hD : 0 < P 1 1 * P 2 2 - P 1 2 ^ 2) (hdet : 0 < P.det) : 0 < cholA P :=
  Real.sqrt_pos.mpr (div_pos hdet hD)

theorem cholC00_pos (hs : 0 < P 2 2) (hD : 0 < P 1 1 * P 2 2 - P 1 2 ^ 2) : 0 < cholC00 P :=
  Real.sqrt_pos.mpr (div_pos hD hs)

theorem cholC11_pos (hs : 0 < P 2 2) : 0 < cholC11 P := Real.sqrt_pos.mpr hs

end Cholesky

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
