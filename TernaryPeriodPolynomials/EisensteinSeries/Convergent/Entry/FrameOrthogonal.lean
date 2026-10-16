module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Normalization

@[expose] public section


/-!
# Right-`SO(3)` covariance of the frame coefficients (R5 of the ML4b reduction)

For `k` orthogonal, `g k` and `g` define the same point (`(gk)(gk)ᵀ = g gᵀ`), the tangent `dL_{gk} V` is
`dL_g (k V kᵀ)`, and `ρ(gk)⁻¹ = ρ(kᵀ) ρ(g)⁻¹`; hence the invariant-frame coefficient of any polynomial-valued
two-form satisfies `ω̃(g k)(V, W) = ρ(kᵀ) ω̃(g)(k V kᵀ, k W kᵀ)`, in the plane chart (`frameCoefficient`) and in
the line chart (`lineFrameCoefficient`). Step R5 of K's reduction of the form identity of Appendix C.5
(`ar:sec:real`) to the base point.

Written by Claude Opus 5.5.
-/

open MvPolynomial Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

private theorem orth_transpose_mul {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : k * k.transpose = 1) :
    k.transpose * k = 1 := mul_eq_one_comm.mp hk

private theorem one_add_conj {k V : Matrix (Fin 3) (Fin 3) ℝ} (hk : k * k.transpose = 1) (ε : ℝ) :
    1 + ε • (k * V * k.transpose) = k * (1 + ε • V) * k.transpose := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hk, Matrix.mul_smul, Matrix.smul_mul]

/-- `g k (1 + εV)` and `g (1 + ε kVkᵀ)` have the same Gram matrix. -/
theorem gramCurve_mul_orthogonal (g k V : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1)
    (ε : ℝ) : gramCurve (g * k) V ε = gramCurve g (k * V * k.transpose) ε := by
  have hk' := orth_transpose_mul hk
  unfold gramCurve
  rw [one_add_conj hk, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_mul]
  have e : g * (k * (1 + ε • V) * k.transpose) * (k * ((1 + ε • V).transpose * k.transpose)) *
      g.transpose = g * k * (1 + ε • V) * (k.transpose * k) * (1 + ε • V).transpose * k.transpose *
        g.transpose := by
    simp only [Matrix.mul_assoc]
  rw [e, hk', Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem gram_mul_orthogonal (g k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    (g * k) * (g * k).transpose = g * g.transpose := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k, hk, Matrix.one_mul]

private theorem inv_mul_orth (g k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    (g * k)⁻¹ = k.transpose * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hk]

/-- **R5 (plane chart).** -/
theorem frameCoefficient_orthogonal (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (g k V W : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    frameCoefficient ω (g * k) V W =
      SeedC3.rho k.transpose (frameCoefficient ω g (k * V * k.transpose) (k * W * k.transpose)) := by
  have hv : frameValue ω (g * k) V W = frameValue ω g (k * V * k.transpose) (k * W * k.transpose) := by
    unfold frameValue chartTangent
    simp only [gramCurve_mul_orthogonal g k _ hk, gram_mul_orthogonal g k hk]
  rw [frameCoefficient, frameCoefficient, hv, inv_mul_orth g k hk,
    rho_mul]

/-- **R5 (line chart).** -/
theorem lineFrameCoefficient_orthogonal (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (g k V W : Matrix (Fin 3) (Fin 3) ℝ) (hk : k * k.transpose = 1) :
    lineFrameCoefficient ω (g * k) V W =
      SeedC3.rho k.transpose
        (lineFrameCoefficient ω g (k * V * k.transpose) (k * W * k.transpose)) := by
  unfold lineFrameCoefficient lineTangent
  simp only [gramCurve_mul_orthogonal g k _ hk, gram_mul_orthogonal g k hk]
  rw [inv_mul_orth g k hk, rho_mul]

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
