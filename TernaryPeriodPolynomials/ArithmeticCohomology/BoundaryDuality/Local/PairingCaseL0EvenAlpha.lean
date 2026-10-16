module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BadIdentPlaneFrame

@[expose] public section


/-!
# The cusp-exchanging map `α` of `Γ₁'(3)` is a multiplicative involution

`BadIdentPlaneFrame.alpha` is the map `γ ↦ δ γ^{-T} δ⁻¹` of `Γ₁'(3)` which exchanges the two cusps,
defined through the inverse transpose of `GL₂(ℤ)` and the injective homomorphism `κ`.  The
identification of the dual plane of the bad line with the good plane only uses its values; to
transport crossed homomorphisms along it one needs that it is multiplicative (`alpha_mul`, from the
multiplicativity of the inverse transpose and the injectivity of `κ`) and an involution
(`alpha_alpha`).

The involution property reduces, by the injectivity of `κ`, to the uniqueness of the inverse
transpose: both `(α γ)^{-T}` and `κ γ` are the transposed inverse of `α γ`, which is a matrix
identity between `[[κ₀₀, κ₀₁/3], [3 κ₁₀, κ₁₁]]` and `[[a, 3b], [c/3, d]]`ᵀ using that `3 ∣ c` and
`3 ∣ κ₀₁`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (GL2Z)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (invT mul_invT_transpose)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (alpha kap_alpha alpha_dvd unkapMat)

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

/-- The inverse transpose of `GL₂(ℤ)` is multiplicative. -/
theorem invT_mul (a b : GL2Z) : invT (a * b) = invT a * invT b := by
  apply Units.ext
  change (((a * b)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).transpose =
    ((a⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).transpose *
      ((b⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ).transpose
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

/-- **`α` is multiplicative.** -/
theorem alpha_mul (g h : binaryArithmeticLevel) : alpha (g * h) = alpha g * alpha h := by
  apply kap_injective
  rw [map_mul, kap_alpha, kap_alpha, kap_alpha]
  exact invT_mul g.1 h.1

/-- The matrix identity behind `alpha_alpha`: `[[κ₀₀, κ₀₁/3], [3 κ₁₀, κ₁₁]] · κ(M)ᵀ = 1` when
`M κᵀ = 1`, `3 ∣ M₁₀` and `3 ∣ κ₀₁`. -/
theorem unkapMat_mul_kapMat_transpose (M K : Matrix (Fin 2) (Fin 2) ℤ) (hMK : M * Kᵀ = 1)
    (h3c : (3 : ℤ) ∣ M 1 0) (h3k : (3 : ℤ) ∣ K 0 1) :
    unkapMat K * (kapMat M)ᵀ = 1 := by
  obtain ⟨c', hc'⟩ := h3c
  obtain ⟨k', hk'⟩ := h3k
  have d1 : M 1 0 / 3 = c' := by omega
  have d2 : K 0 1 / 3 = k' := by omega
  have e00 := congrFun (congrFun hMK 0) 0
  have e01 := congrFun (congrFun hMK 0) 1
  have e10 := congrFun (congrFun hMK 1) 0
  have e11 := congrFun (congrFun hMK 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, Fin.isValue, one_ne_zero, zero_ne_one,
    not_false_eq_true] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unkapMat, kapMat, Matrix.mul_apply, Fin.sum_univ_two, d1, d2]
  · linear_combination e00 - (M 0 1) * hk'
  · apply mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0)
    linear_combination e10 - (K 0 0) * hc' - (M 1 1) * hk'
  · linear_combination 3 * e01
  · linear_combination e11 - K 1 0 * hc'

/-- **`α` is an involution.** -/
theorem alpha_alpha (γ : binaryArithmeticLevel) : alpha (alpha γ) = γ := by
  apply kap_injective
  rw [kap_alpha]
  have hmat : ((alpha γ).val : Matrix (Fin 2) (Fin 2) ℤ) =
      unkapMat ((invT γ.1 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  have key : ((alpha γ).val : Matrix (Fin 2) (Fin 2) ℤ) *
      ((kap γ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1 := by
    rw [hmat, kap_val]
    exact unkapMat_mul_kapMat_transpose _ _ (mul_invT_transpose γ.1) (level_dvd γ) (alpha_dvd γ)
  have e1 := mul_invT_transpose (alpha γ).1
  have hu : ∀ Y₁ Y₂ : Matrix (Fin 2) (Fin 2) ℤ, ((alpha γ).1 : Matrix (Fin 2) (Fin 2) ℤ) * Y₁ = 1 →
      ((alpha γ).1 : Matrix (Fin 2) (Fin 2) ℤ) * Y₂ = 1 → Y₁ = Y₂ := by
    intro Y₁ Y₂ h₁ h₂
    have step : ∀ Y : Matrix (Fin 2) (Fin 2) ℤ,
        ((alpha γ).1 : Matrix (Fin 2) (Fin 2) ℤ) * Y = 1 →
          Y = (((alpha γ).1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) := by
      intro Y h
      calc Y = (((alpha γ).1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((alpha γ).1 : Matrix (Fin 2) (Fin 2) ℤ) * Y) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              Matrix.one_mul]
        _ = (((alpha γ).1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [h, Matrix.mul_one]
    exact (step Y₁ h₁).trans (step Y₂ h₂).symm
  apply Units.ext
  exact Matrix.transpose_inj.mp (hu _ _ e1 key)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
