module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Seed

@[expose] public section


/-!
# The normalization of the real entry by the line seed

Appendix C.5 (`ar:sec:real`) of the paper
normalizes the real entry relative to the line seed
`σ_h = h(τ)(τZ - Y)ⁿ (τ dv₁ + dv₂) ∧ dτ`, where `dv₁, dv₂` are the covectors dual to the line-radical
coordinates: the scalar `c_∞` is `I_n` divided by `(-1)ⁿ(2i)^{-k}`, "its corresponding value at
`τ = i`".

Line-face coordinates: a point `g SO(3)` with Gram matrix `G = g gᵀ` is written `n m SO(3)` with
`n = [[1, w], [0, 1]]` in the line radical and `m = diag(λ, C)`; then `G_{1,{2,3}} = w C Cᵀ` and
`G_{{2,3},{2,3}} = C Cᵀ`, so `w = G_{1,{2,3}} (G_{{2,3},{2,3}})⁻¹` and `τ = C i` is read from `C Cᵀ` by
the same formula as in the plane chart (`lineChart`).

This module proves that the frame coefficient of `σ_h` at `g = 1` on the tangents `v₂ = E₁₃` and
`x₀ = E₂₃`, read at `X = Z = 0, Y = 1`, is `(-1)ⁿ(2i)^{-k}` for the lowest-weight vector
`h(τ) = (τ + i)^{-k}` (`lineSeed_frameCoefficient_one_eval`), and hence that the `c_∞ = -2πi/(n+1)` of `real_constant_term_entry` is the quotient of the real intertwining integral
of the plane seed's frame coefficient by this line-seed value (`real_entry_ratio`).

Written by Claude Opus 5.5.
-/

open MvPolynomial MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization

open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed

/-- Line-face coordinates `(w₁, w₂, Re τ, Im τ, λ)` of the point with Gram matrix `G`:
`w = G_{1,{2,3}} B⁻¹` for `B = G_{{2,3},{2,3}}`, `τ = B₁₂/B₂₂ + i √(det B)/B₂₂`,
`λ = √(G₁₁ - w · G_{1,{2,3}})`. -/
def lineChart (G : Matrix (Fin 3) (Fin 3) ℝ) : Fin 5 → ℝ :=
  ![(G 0 1 * G 2 2 - G 0 2 * G 2 1) / (G 1 1 * G 2 2 - G 1 2 * G 2 1),
    (G 0 2 * G 1 1 - G 0 1 * G 1 2) / (G 1 1 * G 2 2 - G 1 2 * G 2 1),
    G 1 2 / G 2 2,
    Real.sqrt (G 1 1 * G 2 2 - G 1 2 * G 2 1) / G 2 2,
    Real.sqrt (G 0 0 - ((G 0 1 * G 2 2 - G 0 2 * G 2 1) * G 0 1 +
      (G 0 2 * G 1 1 - G 0 1 * G 1 2) * G 0 2) / (G 1 1 * G 2 2 - G 1 2 * G 2 1))]

/-- The line-face coordinates of `dL_g V`. -/
def lineTangent (g V : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 5) : ℝ :=
  deriv (fun ε => lineChart (gramCurve g V ε) a) 0

/-- `τ = Re τ + i Im τ` in line-face coordinates. -/
def lineTau (p : Fin 5 → ℝ) : ℂ := (p 2 : ℂ) + Complex.I * (p 3 : ℂ)

/-- The line seed `σ_h = h(τ)(τZ - Y)ⁿ (τ dw₁ + dw₂) ∧ dτ` as a coefficient matrix in line-face
coordinates. -/
def lineSeedForm (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) : MvPolynomial (Fin 3) ℂ :=
  C (h (lineTau p) * ((![lineTau p, 1, 0, 0, 0] : Fin 5 → ℂ) i * seedDTau j -
      (![lineTau p, 1, 0, 0, 0] : Fin 5 → ℂ) j * seedDTau i)) *
    (C (lineTau p) * X 2 - X 1) ^ n

/-- The frame coefficient `ρ(g)⁻¹ σ(dL_g V, dL_g W)` in line-face coordinates. -/
def lineFrameCoefficient (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (g V W : Matrix (Fin 3) (Fin 3) ℝ) : MvPolynomial (Fin 3) ℂ :=
  SeedC3.rho g⁻¹ (∑ a : Fin 5, ∑ b : Fin 5,
    C ((lineTangent g V a * lineTangent g W b : ℝ) : ℂ) * ω (lineChart (g * g.transpose)) a b)

private theorem curve_v2 (ε : ℝ) :
    gramCurve 1 (Matrix.single 0 2 1) ε = !![1 + ε ^ 2, 0, ε; 0, 1, 0; ε, 0, 1] := by
  rw [gramCurve, one_add_eps_v2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, sq]

private theorem curve_x0 (ε : ℝ) :
    gramCurve 1 (Matrix.single 1 2 1) ε = !![1, 0, 0; 0, 1 + ε ^ 2, ε; 0, ε, 1] := by
  rw [gramCurve, one_add_eps_x0_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, sq]

private theorem lineChart_v2 (ε : ℝ) :
    lineChart (gramCurve 1 (Matrix.single 0 2 1) ε) = ![0, ε, 0, 1, 1] := by
  rw [curve_v2]
  funext a
  fin_cases a <;> simp [lineChart, sq]

private theorem lineChart_x0 (ε : ℝ) :
    lineChart (gramCurve 1 (Matrix.single 1 2 1) ε) = ![0, 0, ε, 1, 1] := by
  rw [curve_x0]
  funext a
  fin_cases a <;> simp [lineChart, sq]

private theorem lineTangent_v2 (a : Fin 5) :
    lineTangent 1 (Matrix.single 0 2 1) a = (![0, 1, 0, 0, 0] : Fin 5 → ℝ) a := by
  rw [lineTangent]
  simp only [lineChart_v2]
  fin_cases a <;> simp

private theorem lineTangent_x0 (a : Fin 5) :
    lineTangent 1 (Matrix.single 1 2 1) a = (![0, 0, 1, 0, 0] : Fin 5 → ℝ) a := by
  rw [lineTangent]
  simp only [lineChart_x0]
  fin_cases a <;> simp

private theorem lineChart_one :
    lineChart ((1 : Matrix (Fin 3) (Fin 3) ℝ) * (1 : Matrix (Fin 3) (Fin 3) ℝ).transpose) =
      ![0, 0, 0, 1, 1] := by
  rw [Matrix.transpose_one, mul_one]
  funext a
  fin_cases a <;> simp [lineChart]

/-- **The line seed at the base point.** `ρ(1)⁻¹ σ_h(dL_1 v₂, dL_1 x₀) = h(i)(iZ - Y)ⁿ`. -/
theorem lineSeed_frameCoefficient_one (n : ℕ) (h : ℂ → ℂ) :
    lineFrameCoefficient (lineSeedForm n h) 1 (Matrix.single 0 2 1) (Matrix.single 1 2 1) =
      C (h Complex.I) * (C Complex.I * X 2 - X 1) ^ n := by
  rw [lineFrameCoefficient, inv_one, rho_one, lineChart_one]
  simp only [lineTangent_v2, lineTangent_x0, Fin.sum_univ_five, lineSeedForm, lineTau, seedDTau,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  simp

/-- The `Y`-coordinate of the line seed at the base point is `(-1)ⁿ(2i)^{-k}` for the lowest-weight
vector, the normalizing value of `ar:eq:realintegral`. -/
theorem lineSeed_frameCoefficient_one_eval (n : ℕ) :
    eval ![0, 1, 0] (lineFrameCoefficient (lineSeedForm n (lowestWeightVector n)) 1
        (Matrix.single 0 2 1) (Matrix.single 1 2 1)) =
      (-1) ^ n * (2 * Complex.I) ^ (-((n : ℤ) + 3)) := by
  rw [lineSeed_frameCoefficient_one]
  simp [lowestWeightVector, two_mul]
  ring

/-- **`c_∞` as a ratio of seed frame coefficients.** The real intertwining integral of the plane
seed's frame coefficient at `w₀⁻¹u(s,t)`, divided by the line seed's frame coefficient at the base
point (both on `(v₂, x₀)`, read at `X = Z = 0, Y = 1`), is `c_∞ = -2πi/(n+1)`. -/
theorem real_entry_ratio (n : ℕ) :
    (∫ st : ℝ × ℝ, eval ![0, 1, 0]
        (frameCoefficient (seedForm n (lowestWeightVector n)) (entryFrame st.1 st.2)
          (Matrix.single 0 2 1) (Matrix.single 1 2 1))) /
      eval ![0, 1, 0] (lineFrameCoefficient (lineSeedForm n (lowestWeightVector n)) 1
        (Matrix.single 0 2 1) (Matrix.single 1 2 1)) =
      -2 * Real.pi * Complex.I / ((n : ℂ) + 1) := by
  rw [← entryIntegral_eq_integral_seed_frameCoefficient, lineSeed_frameCoefficient_one_eval]
  exact (real_constant_term_entry n).2.2.1

end TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization
