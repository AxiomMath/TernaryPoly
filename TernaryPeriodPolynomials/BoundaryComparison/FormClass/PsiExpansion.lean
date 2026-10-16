module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.FinalK
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KAnalysis

@[expose] public section


/-!
# The coefficient `(i, j, m)` of the summand at a general point `y ∈ Ω`: continuity of the action derivative

Formalized by Claude Sonnet 5.5.

`continuous_fderiv_planeAct_qMat`: for `y ∈ Ω` the derivative `∂_i (planeAct (qMat w))_a (y)` is continuous in `w`.
-/

open scoped MatrixGroups ContDiff
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem continuous_matToFun_qMat : Continuous fun w : Fin 2 → ℝ => matToFun (qMat w) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  fin_cases a <;> fin_cases b <;> simp [matToFun, qMat] <;> fun_prop

theorem continuous_fderiv_planeAct_qMat {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i a : Fin 5) :
    Continuous fun w : Fin 2 → ℝ => fderiv ℝ (planeAct (qMat w)) y (Pi.single i 1) a := by
  set F : (Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ) → (Fin 5 → ℝ) := fun z => planeAct (matOfFun z.1) z.2 with hF
  have hcd : ∀ w, ContDiffAt ℝ ⊤ F (matToFun (qMat w), y) := fun w => contDiffAt_planeAct_pair (det_qMat w) hy
  have hfd : ∀ w, fderiv ℝ (planeAct (qMat w)) y =
      (fderiv ℝ F (matToFun (qMat w), y)).comp (ContinuousLinearMap.inr ℝ (Fin 3 → Fin 3 → ℝ) (Fin 5 → ℝ)) := by
    intro w
    have h1 : HasFDerivAt F (fderiv ℝ F (matToFun (qMat w), y)) (matToFun (qMat w), y) :=
      ((hcd w).differentiableAt (by simp)).hasFDerivAt
    have h2 := h1.comp y (hasFDerivAt_prodMk_right (matToFun (qMat w)) y)
    exact h2.fderiv
  simp_rw [hfd]
  have hcont : Continuous fun w : Fin 2 → ℝ => fderiv ℝ F (matToFun (qMat w), y) := by
    rw [continuous_iff_continuousAt]
    intro w
    have h1 : ContDiffAt ℝ 0 (fderiv ℝ F) (matToFun (qMat w), y) := (hcd w).fderiv_right (m := 0) (by simp)
    exact h1.continuousAt.comp (f := fun w' : Fin 2 → ℝ => (matToFun (qMat w'), y))
      ((continuous_matToFun_qMat.prodMk continuous_const).continuousAt)
  have : Continuous fun L : ((Fin 3 → Fin 3 → ℝ) × (Fin 5 → ℝ)) →L[ℝ] (Fin 5 → ℝ) =>
      (L.comp (ContinuousLinearMap.inr ℝ (Fin 3 → Fin 3 → ℝ) (Fin 5 → ℝ))) (Pi.single i 1) a :=
    (continuous_apply a).comp
      ((ContinuousLinearMap.apply ℝ (Fin 5 → ℝ) ((0 : Fin 3 → Fin 3 → ℝ), (Pi.single i 1 : Fin 5 → ℝ))).continuous)
  exact this.comp hcont

end TernaryPeriodPolynomials.Argument.FormClassK
