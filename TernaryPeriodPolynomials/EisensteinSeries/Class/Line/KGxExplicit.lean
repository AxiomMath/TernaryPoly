module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KGx
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Normalization

@[expose] public section


/-!
# The frame matrix `g_x` and the line chart of its Gram matrix

Paper: Appendix C.5.

For the face point `x = (u₁, u₂, ξ, η)` (`η > 0`), `g_x = rt (planePinv (ptOf x))` is the upper triangular matrix
`[[1, -√η u₂, (ξ u₂ - u₁)/√η], [0, √η, -ξ/√η], [0, 0, 1/√η]]` (`gx_eq`), and the line chart of the Gram matrix
`g_x g_xᵀ` is `(-u₂, -u₁, -ξ, η)` in its first four coordinates (`lineChart_gx_*`): the line coordinates of
the face point `x` are `w = (-u₂, -u₁)`, `τ = -ξ + iη = -conj(ξ + iη)`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization (lineChart)

section Explicit

theorem gx_eq (x : Face) :
    gx x = !![1, -(Real.sqrt (x 3) * x 1), (x 2 * x 1 - x 0) / Real.sqrt (x 3);
      0, Real.sqrt (x 3), -(x 2) / Real.sqrt (x 3); 0, 0, 1 / Real.sqrt (x 3)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gx, rt, planePinv, ptOf, Fin.rev]

theorem gx_gram_entries {x : Face} (hx : x ∈ faceSet) :
    (gx x * (gx x).transpose) 0 1 = -(x 3 * x 1) - x 2 * (x 2 * x 1 - x 0) / x 3 ∧
    (gx x * (gx x).transpose) 0 2 = (x 2 * x 1 - x 0) / x 3 ∧
    (gx x * (gx x).transpose) 1 1 = x 3 + x 2 ^ 2 / x 3 ∧
    (gx x * (gx x).transpose) 1 2 = -(x 2) / x 3 ∧
    (gx x * (gx x).transpose) 2 2 = 1 / x 3 := by
  have hy : (0 : ℝ) < x 3 := hx
  have hs0 : Real.sqrt (x 3) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hs : Real.sqrt (x 3) ^ 2 = x 3 := Real.sq_sqrt hy.le
  rw [gx_eq x]
  set s := Real.sqrt (x 3) with hsdef
  have hxs : x 3 = s ^ 2 := hs.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
    rw [hxs]; field_simp; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
    rw [hxs]; field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
    rw [hxs]; field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
    rw [hxs]; field_simp
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
    rw [hxs]; field_simp

theorem gram_symm (g : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (g * g.transpose) i j = (g * g.transpose) j i := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]

theorem lineChart_c0 (G : Matrix (Fin 3) (Fin 3) ℝ) : lineChart G 0 =
    (G 0 1 * G 2 2 - G 0 2 * G 2 1) / (G 1 1 * G 2 2 - G 1 2 * G 2 1) := rfl

theorem lineChart_c1 (G : Matrix (Fin 3) (Fin 3) ℝ) : lineChart G 1 =
    (G 0 2 * G 1 1 - G 0 1 * G 1 2) / (G 1 1 * G 2 2 - G 1 2 * G 2 1) := rfl

theorem lineChart_c2 (G : Matrix (Fin 3) (Fin 3) ℝ) : lineChart G 2 = G 1 2 / G 2 2 := rfl

theorem lineChart_c3 (G : Matrix (Fin 3) (Fin 3) ℝ) : lineChart G 3 =
    Real.sqrt (G 1 1 * G 2 2 - G 1 2 * G 2 1) / G 2 2 := rfl

theorem lineChart_gx_det {x : Face} (hx : x ∈ faceSet) :
    (gx x * (gx x).transpose) 1 1 * (gx x * (gx x).transpose) 2 2 -
      (gx x * (gx x).transpose) 1 2 * (gx x * (gx x).transpose) 2 1 = 1 := by
  have hy : (0 : ℝ) < x 3 := hx
  obtain ⟨-, -, h11, h12, h22⟩ := gx_gram_entries hx
  have h21 : (gx x * (gx x).transpose) 2 1 = -(x 2) / x 3 := by rw [gram_symm]; exact h12
  rw [h11, h22, h12, h21]
  field_simp
  ring

theorem lineChart_gx_values {x : Face} (hx : x ∈ faceSet) :
    lineChart (gx x * (gx x).transpose) 0 = -(x 1) ∧ lineChart (gx x * (gx x).transpose) 1 = -(x 0) ∧
    lineChart (gx x * (gx x).transpose) 2 = -(x 2) ∧ lineChart (gx x * (gx x).transpose) 3 = x 3 := by
  have hy : (0 : ℝ) < x 3 := hx
  obtain ⟨h01, h02, h11, h12, h22⟩ := gx_gram_entries hx
  have h21 : (gx x * (gx x).transpose) 2 1 = -(x 2) / x 3 := by rw [gram_symm]; exact h12
  have hD := lineChart_gx_det hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lineChart_c0, hD, div_one, h01, h22, h02, h21]
    field_simp; ring
  · rw [lineChart_c1, hD, div_one, h01, h02, h11, h12]
    field_simp; ring
  · rw [lineChart_c2, h12, h22]
    field_simp
  · rw [lineChart_c3, hD, Real.sqrt_one, h22]
    field_simp

end Explicit

end TernaryPeriodPolynomials.Argument.EisensteinClass
