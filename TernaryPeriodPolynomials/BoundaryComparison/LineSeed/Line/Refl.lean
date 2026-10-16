module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Cusp
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ReflectionForm

@[expose] public section


/-!
# The finite reflection of the line face and of the line coefficients (LS10, part 1)

The reflection `r = diag(1; -1, 1) ∈ GL₃(ℤ)` (determinant `-1`; it is the block `diag(1, J)` with
`J = diag(-1, 1)`) acts on the line face by the reflection `reflFCLM` of `SeedC3`,
`(w₁, w₂, x, y) ↦ (-w₁, w₂, -x, y)`, i.e. `τ ↦ -\bar τ`, and on `E_n` by `ρ(r) q(X, Y, Z) = -q(X, -Y, Z)`
(`lreflCoef`, `toPoly_lreflCoef`).  The key identity is
`ρ(r) \overline{P_τ}ⁿ = (-1)^{n+1} P_{-\bar τ}ⁿ` (`rho_lrefl_conjPpoly_pow`), which gives the sign `(-1)ⁿ` of
`r^* σ_h = (-1)ⁿ ρ(r) \overline{σ_{h^*}}` (`LineReflForm`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial ComplexConjugate
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi

/-- The matrix `diag(1, -1, 1)` of the line reflection. -/
def lrMat : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, -1, 1]

theorem lrMat_mul_self : lrMat * lrMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lrMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_lrMat : lrMat.det = -1 := by
  simp [lrMat, Matrix.det_diagonal, Fin.prod_univ_three]

theorem lrMat_inv : lrMat⁻¹ = lrMat := Matrix.inv_eq_right_inv lrMat_mul_self

/-- The line reflection `diag(1, -1, 1)` as an element of `GL₃(ℝ)`. -/
def lrGL : GL (Fin 3) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero lrMat (by rw [det_lrMat]; norm_num)

/-- `ρ(r)` on `E_n` for the line reflection. -/
def lreflCoef (n : ℕ) : Coef n →ₗ[ℂ] Coef n := GeneralEisenstein.realCoefficient n lrGL

theorem toPoly_lreflCoef (n : ℕ) (q : Coef n) :
    Coef.toPoly (lreflCoef n q) =
      C (-1 : ℂ) * bind₁ (![X 0, -X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) (Coef.toPoly q) := by
  refine (realCoefficient_coe n lrGL q).trans ?_
  unfold rho
  have h1 : ((lrGL : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = lrMat := rfl
  rw [h1, det_lrMat, lrMat_inv]
  congr 2
  · simp
  · congr 2
    funext i
    fin_cases i <;> simp [lrMat, Fin.sum_univ_three]

/-- `ρ(r)` on `E_n` as a continuous real-linear map. -/
def lreflCoefCLM (n : ℕ) : Coef n →L[ℝ] Coef n :=
  LinearMap.toContinuousLinearMap ((lreflCoef n).restrictScalars ℝ)

theorem conjCLM_comp_lreflCoefCLM (n : ℕ) :
    (conjCLM n).comp (lreflCoefCLM n) = (lreflCoefCLM n).comp (conjCLM n) := by
  ext q
  apply Coef.toPoly_injective
  change Coef.toPoly (Coef.conjCoef (lreflCoef n q)) = Coef.toPoly (lreflCoef n (Coef.conjCoef q))
  rw [Coef.toPoly_conjCoef, toPoly_lreflCoef, toPoly_lreflCoef, Coef.toPoly_conjCoef, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_bind₁]
  have e : (fun i => MvPolynomial.map (starRingEnd ℂ)
      ((![X 0, -X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) i)) =
      (![X 0, -X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ) := by
    funext i
    fin_cases i <;> simp
  rw [e]
  simp

/-- `r` carries `\overline{P_τ}` to `-P_{-\bar τ}` under the substitution `Y ↦ -Y`. -/
theorem bind_lrefl_conjPpoly (t : ℂ) :
    bind₁ (![X 0, -X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        (MvPolynomial.map (starRingEnd ℂ) (Ppoly t)) = -Ppoly (-conj t) := by
  unfold Ppoly
  simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, bind₁_C_right, bind₁_X_right]
  simp [map_neg]
  ring

/-- `ρ(r) \overline{P_τ}ⁿ = (-1)^{n+1} P_{-\bar τ}ⁿ`. -/
theorem rho_lrefl_conjPpoly_pow (t : ℂ) (n : ℕ) :
    C (-1 : ℂ) * bind₁ (![X 0, -X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) ℂ)
        (MvPolynomial.map (starRingEnd ℂ) (Ppoly t ^ n)) =
      C ((-1 : ℂ) ^ (n + 1)) * Ppoly (-conj t) ^ n := by
  rw [map_pow, map_pow, bind_lrefl_conjPpoly, neg_pow, pow_succ, map_mul, map_pow, map_neg, map_one]
  ring

end TernaryPeriodPolynomials.Argument.LineSeed
