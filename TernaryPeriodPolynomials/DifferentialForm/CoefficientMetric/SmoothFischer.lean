module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Fischer
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section


/-! Polynomial dependence of the intrinsic Fischer pairing on the matrix entries. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity MvPolynomial
open scoped ContDiff Matrix.Norms.Elementwise

theorem factorialPairing_X_right (p q : Poly) (i : Fin 3) :
    factorialPairing p (X i * q) = factorialPairing (pderiv i p) q := by
  rw [factorialPairing_symmetric, factorialPairing_X_mul, factorialPairing_symmetric]

theorem matrixPairing_mul_X (Q : Mat) (p q : Poly) (i : Fin 3) :
    matrixPairing Q p (q * X i) = ∑ j : Fin 3, Q i j * matrixPairing Q (pderiv j p) q := by
  unfold matrixPairing
  rw [map_mul, realSubstitute_X, realLinearForm, Finset.mul_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h : realSubstitute Q q * (C (Q i j) * X j) = Q i j • (X j * realSubstitute Q q) := by
    rw [smul_eq_C_mul]
    ring
  rw [h, map_smul, smul_eq_mul, factorialPairing_X_right]

theorem contDiff_matrixPairing (p q : Poly) : ContDiff ℝ ∞ (fun Q : Mat => matrixPairing Q p q) := by
  induction q using MvPolynomial.induction_on generalizing p with
  | C r => simpa [matrixPairing] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Mat => factorialPairing p (C r)))
  | add q r hq hr =>
    have h := (hq p).add (hr p)
    simpa [matrixPairing] using h
  | mul_X q i hq =>
    simp_rw [matrixPairing_mul_X]
    apply ContDiff.sum
    intro j hj
    exact (contDiff_apply_apply ℝ ℝ i j).mul (hq (pderiv j p))

def matrixBilinear (n : ℕ) (Q : Mat) : Coefficients n →ₗ[ℝ] Coefficients n →ₗ[ℝ] ℝ where
  toFun p :=
    { toFun := fun q => matrixPairing Q p.val q.val
      map_add' := by intros; simp [matrixPairing]
      map_smul' := by intros; simp [matrixPairing] }
  map_add' := by intros; ext q; simp [matrixPairing]
  map_smul' := by intros; ext q; simp [matrixPairing]

instance coefficientDualNormedAddCommGroup (n : ℕ) : NormedAddCommGroup (Coefficients n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance coefficientDualNormedSpace (n : ℕ) : NormedSpace ℝ (Coefficients n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def matrixContinuousBilin (n : ℕ) (Q : Mat) : Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ :=
  ((LinearMap.toContinuousLinearMap.toLinearMap).comp (matrixBilinear n Q)).toContinuousLinearMap

@[simp] theorem matrixContinuousBilin_apply (n : ℕ) (Q : Mat) (p q : Coefficients n) :
    matrixContinuousBilin n Q p q = matrixPairing Q p.val q.val := rfl

theorem contDiff_matrixContinuousBilin (n : ℕ) : ContDiff ℝ ∞ (matrixContinuousBilin n) := by
  rw [contDiff_clm_apply_iff]
  intro p
  rw [contDiff_clm_apply_iff]
  intro q
  exact contDiff_matrixPairing p.val q.val

end TernaryPoly.PolynomialCoefficientMetric
