module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Representation
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricFrames

@[expose] public section


/-! The intrinsic Fischer pairing determined by a positive matrix, independent of frames. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientMetric
open SL3PolynomialCoercivity SymmetricSpacePositive

@[simp] theorem realSubstitute_apply_apply (A B : Mat) (p : Poly) :
    realSubstitute A (realSubstitute B p) = realSubstitute (B*A) p :=
  congrArg (fun F : Poly →ₐ[ℝ] Poly => F p) (realSubstitute_comp A B)

def matrixPairing (Q : Mat) (p q : Poly) : ℝ := factorialPairing p (realSubstitute Q q)

theorem matrixPairing_frame (g : Mat) (p q : Poly) :
    matrixPairing (g*g.transpose) p q = factorialPairing (realSubstitute g p) (realSubstitute g q) := by
  rw [realSubstitute_transpose_adjoint, realSubstitute_apply_apply]
  rfl

theorem realSubstitute_injective (g : RealGL) : Function.Injective (realSubstitute g) := by
  intro p q h
  have h' := congrArg (realSubstitute (g⁻¹ : RealGL)) h
  simpa [realSubstitute_apply_apply, realSubstitute_one] using h'

theorem matrixPairing_symmetric (Q : Mat) (hQ : Q.transpose = Q) (p q : Poly) :
    matrixPairing Q p q = matrixPairing Q q p := by
  rw [matrixPairing, factorialPairing_symmetric, realSubstitute_transpose_adjoint, hQ]
  rfl

theorem matrixPairing_positive (Q : Mat) (hQ : Q.PosDef) (p : Poly) (hp : p ≠ 0) :
    0 < matrixPairing Q p p := by
  obtain ⟨g, hg⟩ := SymmetricSpaceTraceMetric.exists_positive_frame Q hQ
  have hstar : star (g : Mat) = (g : Mat).transpose := by ext i j; rfl
  rw [hstar] at hg
  rw [hg, matrixPairing_frame]
  apply lt_of_le_of_ne (factorialPairing_self_nonneg _)
  intro hz
  have hzero := (factorialPairing_self_eq_zero _).mp hz.symm
  exact hp (realSubstitute_injective g (by simpa using hzero))

theorem matrixPairing_congruence (g : RealGL) (Q : Mat) (p q : Poly) :
    matrixPairing ((g : Mat)*Q*(g : Mat).transpose)
      (realSubstitute (g⁻¹ : RealGL) p) (realSubstitute (g⁻¹ : RealGL) q) = matrixPairing Q p q := by
  unfold matrixPairing
  rw [realSubstitute_transpose_adjoint, realSubstitute_apply_apply, realSubstitute_apply_apply]
  have hc : (↑g⁻¹ : Mat) * ((g : Mat)*Q*(g : Mat).transpose) * (↑g⁻¹ : Mat).transpose = Q := by
    calc
      _ = ((↑g⁻¹ : Mat) * (g : Mat)) * Q * ((g : Mat).transpose * (↑g⁻¹ : Mat).transpose) := by simp [mul_assoc]
      _ = Q := by rw [← Matrix.transpose_mul]; simp
  simpa only [mul_assoc] using congrArg (fun A : Mat => factorialPairing p (realSubstitute A q)) hc

end TernaryPoly.PolynomialCoefficientMetric
