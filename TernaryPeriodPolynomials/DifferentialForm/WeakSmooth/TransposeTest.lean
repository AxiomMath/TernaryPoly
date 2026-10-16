module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularDerivative
public import TernaryPeriodPolynomials.Analysis.Compact.Matrix.FormalAdjoint

@[expose] public section


/-! Actual compact scalar test realization of a constant-coefficient transpose differential. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set CompactCoordinateIntegration
open scoped Distributions
variable {E I J K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [Fintype J] [Fintype K] [DecidableEq J]

/-- The compact test representing the transpose of a constant matrix of directional derivatives. -/
def scalarMatrixTransposeTest (Ω : TopologicalSpace.Opens E) (v : K → E) (A : J → I → K → ℝ)
    (j : J) (φ : 𝓓(Ω, ℝ)) (i : I) : 𝓓(Ω, ℝ) :=
  ∑ d, -(A j i d) • TestFunction.lineDerivCLM ℝ (v d) φ

omit [Fintype I] [Fintype J] [DecidableEq J] in
@[simp] theorem scalarMatrixTransposeTest_apply (Ω : TopologicalSpace.Opens E) (v : K → E)
    (A : J → I → K → ℝ) (j : J) (φ : 𝓓(Ω, ℝ)) (i : I) (x : E) :
    scalarMatrixTransposeTest Ω v A j φ i x = ∑ d, -(A j i d) * fderiv ℝ φ x (v d) := by
  simp [scalarMatrixTransposeTest,
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]

omit [Fintype I] in
/-- The genuine matrix transpose divergence on a single scalar test is exactly a finite sum of
actual compact test derivatives. -/
theorem scalarMatrixTransposeTest_eq (Ω : TopologicalSpace.Opens E) (v : K → E)
    (A : J → I → K → ℝ) (j : J) (φ : 𝓓(Ω, ℝ)) (i : I) (x : E) :
    matrixTranspose v (fun j i d _ => A j i d) (fun _ _ _ _ => 0)
      (fun l y => if l = j then φ y else 0) i x = scalarMatrixTransposeTest Ω v A j φ i x := by
  unfold matrixTranspose
  rw [Finset.sum_eq_single j]
  · rw [scalarMatrixTransposeTest_apply]
    apply Finset.sum_congr rfl
    intro d _
    simp only [transposeOrder, ite_true, zero_mul, zero_sub]
    rw [fderiv_const_mul (φ.contDiff.differentiable (by simp) x) (A j i d)]
    simp
  · intro l _ hlj
    apply Finset.sum_eq_zero
    intro d _
    simp [transposeOrder, hlj]
  · simp

end TernaryPoly.PolynomialFormWeakSmooth
