module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KEntry

@[expose] public section


/-!
# Derivatives of the Gram chart along curves of Gram matrices

Paper: Appendix C.5.

The chart `gramChart` of the frame computation is smooth near any Gram matrix
(`contDiffAt_gramChart_comp`), so two curves of matrices with the same value (a Gram matrix) and the same derivative
at `0` have the same chart derivative (`hasDerivAt_gramChart_curve`). With the product rule for matrix curves
(`hasDerivAt_mat_mul`, `hasDerivAt_conj`) this identifies the chart tangent of a Lie algebra element with the
derivative of the chart along any curve in the group with that velocity.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed (gramChart gramCurve chartTangent)

section Smooth

theorem gramChart_apply2 (G : Matrix (Fin 3) (Fin 3) ℝ) :
    gramChart G 2 = (G 0 1 - G 0 2 * G 1 2 / G 2 2) / (G 1 1 - G 1 2 * G 1 2 / G 2 2) := by
  show (gramPlaneTau G).re = _
  rw [gramPlaneTau_re]
  simp [gramSchur]

theorem gramChart_apply3 (G : Matrix (Fin 3) (Fin 3) ℝ) :
    gramChart G 3 = Real.sqrt ((G 0 0 - G 0 2 * G 0 2 / G 2 2) * (G 1 1 - G 1 2 * G 1 2 / G 2 2) -
      (G 0 1 - G 0 2 * G 1 2 / G 2 2) * (G 1 0 - G 1 2 * G 0 2 / G 2 2)) /
      (G 1 1 - G 1 2 * G 1 2 / G 2 2) := by
  show (gramPlaneTau G).im = _
  rw [gramPlaneTau_im, Matrix.det_fin_two]
  simp [gramSchur]

theorem contDiffAt_gramChart_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : X → Matrix (Fin 3) (Fin 3) ℝ} {x : X}
    (hF : ∀ i j, ContDiffAt ℝ ⊤ (fun y => F y i j) x) (hs : 0 < F x 2 2)
    (hc : 0 < F x 1 1 - F x 1 2 * F x 1 2 / F x 2 2)
    (hd : 0 < (F x 0 0 - F x 0 2 * F x 0 2 / F x 2 2) * (F x 1 1 - F x 1 2 * F x 1 2 / F x 2 2) -
      (F x 0 1 - F x 0 2 * F x 1 2 / F x 2 2) * (F x 1 0 - F x 1 2 * F x 0 2 / F x 2 2)) :
    ContDiffAt ℝ ⊤ (fun y => gramChart (F y)) x := by
  have h22 : ContDiffAt ℝ ⊤ (fun y => F y 2 2) x := hF 2 2
  have hsq : ContDiffAt ℝ ⊤ (fun y => Real.sqrt (F y 2 2)) x := h22.sqrt hs.ne'
  have hS11 : ContDiffAt ℝ ⊤ (fun y => F y 1 1 - F y 1 2 * F y 1 2 / F y 2 2) x :=
    (hF 1 1).sub (((hF 1 2).mul (hF 1 2)).div h22 hs.ne')
  have hS00 : ContDiffAt ℝ ⊤ (fun y => F y 0 0 - F y 0 2 * F y 0 2 / F y 2 2) x :=
    (hF 0 0).sub (((hF 0 2).mul (hF 0 2)).div h22 hs.ne')
  have hS01 : ContDiffAt ℝ ⊤ (fun y => F y 0 1 - F y 0 2 * F y 1 2 / F y 2 2) x :=
    (hF 0 1).sub (((hF 0 2).mul (hF 1 2)).div h22 hs.ne')
  have hS10 : ContDiffAt ℝ ⊤ (fun y => F y 1 0 - F y 1 2 * F y 0 2 / F y 2 2) x :=
    (hF 1 0).sub (((hF 1 2).mul (hF 0 2)).div h22 hs.ne')
  have hdet := (hS00.mul hS11).sub (hS01.mul hS10)
  rw [contDiffAt_pi]
  intro k
  fin_cases k
  · exact (hF 0 2).div h22 hs.ne'
  · exact (hF 1 2).div h22 hs.ne'
  · simp only [Fin.reduceFinMk, gramChart_apply2]
    exact hS01.div hS11 hc.ne'
  · simp only [Fin.reduceFinMk, gramChart_apply3]
    exact (hdet.sqrt hd.ne').div hS11 hc.ne'
  · exact hsq

end Smooth

section Curves

theorem hasDerivAt_mat_mul {A B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {A' B' : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, HasDerivAt (fun ε => A ε i j) (A' i j) 0)
    (hB : ∀ i j, HasDerivAt (fun ε => B ε i j) (B' i j) 0) (i j : Fin 3) :
    HasDerivAt (fun ε => (A ε * B ε) i j) ((A' * B 0 + A 0 * B') i j) 0 := by
  have key := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (hA i l).mul (hB l j))
  have e : (A' * B 0 + A 0 * B') i j = ∑ l, (A' i l * B 0 l j + A 0 i l * B' l j) := by
    simp only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib]
  rw [e]
  simpa [Matrix.mul_apply] using key

theorem hasDerivAt_conj {G : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hG : ∀ i j, HasDerivAt (fun ε => G ε i j) (S i j) 0) (g : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    HasDerivAt (fun ε => (g * G ε * g.transpose) i j) ((g * S * g.transpose) i j) 0 := by
  have hc : ∀ i j, HasDerivAt (fun _ : ℝ => g i j) ((0 : Matrix (Fin 3) (Fin 3) ℝ) i j) 0 :=
    fun i j => by simpa using hasDerivAt_const (0 : ℝ) (g i j)
  have h1 : ∀ i j, HasDerivAt (fun ε => (g * G ε) i j)
      (((0 : Matrix (Fin 3) (Fin 3) ℝ) * G 0 + g * S) i j) 0 :=
    fun i j => hasDerivAt_mat_mul (A := fun _ => g) (B := G) hc hG i j
  have hct : ∀ i j, HasDerivAt (fun _ : ℝ => g.transpose i j) ((0 : Matrix (Fin 3) (Fin 3) ℝ) i j) 0 :=
    fun i j => by simpa using hasDerivAt_const (0 : ℝ) (g.transpose i j)
  have h2 := hasDerivAt_mat_mul (A := fun ε => g * G ε) (B := fun _ => g.transpose) h1 hct i j
  simpa [Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero] using h2

theorem hasDerivAt_gram_V (g V : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    HasDerivAt (fun ε => gramCurve g V ε i j) ((g * (V + V.transpose) * g.transpose) i j) 0 := by
  have hA : ∀ i j, HasDerivAt (fun ε : ℝ => (1 + ε • V) i j) (V i j) 0 := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (V i j)).const_add ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
  have hB : ∀ i j, HasDerivAt (fun ε : ℝ => ((1 + ε • V).transpose) i j) (V.transpose i j) 0 := by
    intro i j
    simpa using hA j i
  have hG := fun i j => hasDerivAt_mat_mul (A := fun ε => 1 + ε • V) (B := fun ε => (1 + ε • V).transpose)
    hA hB i j
  have hG' : ∀ i j, HasDerivAt (fun ε : ℝ => ((1 + ε • V) * (1 + ε • V).transpose) i j)
      ((V + V.transpose) i j) 0 := by
    intro i j
    simpa using hG i j
  have := hasDerivAt_conj hG' g i j
  simpa [gramCurve, Matrix.mul_assoc] using this

end Curves

end TernaryPeriodPolynomials.Argument.EisensteinClass
