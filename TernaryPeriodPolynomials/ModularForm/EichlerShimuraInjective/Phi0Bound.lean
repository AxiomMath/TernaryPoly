module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.SlashAlgebra

@[expose] public section


/-!
# Bound for the translated combined primitive

`Phi0_bound`: `‖Φ₀(z; (z̄,1))‖ ≤ K (1+T)^{n+1}` on `z = x + iT` when the primitives are bounded.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral Filter Topology
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

theorem norm_cc_le (n j : ℕ) : ‖cc n j‖ ≤ ((n + 1).choose j : ℝ) := by
  unfold cc
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  simp

/-- Bound for the `v`-free part of the combined Eichler integral at `(z̄, 1)`. -/
theorem Phi0_bound (n : ℕ) (G H : ℕ → ℂ → ℂ) {KG T0 : ℝ} (hKG0 : 0 ≤ KG)
    (hG : ∀ j : ℕ, j < n + 2 → ∀ (x T : ℝ), |x| ≤ 1 / 2 → T0 ≤ T → ‖G j ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ KG)
    (hH : ∀ j : ℕ, j < n + 2 → ∀ (x T : ℝ), |x| ≤ 1 / 2 → T0 ≤ T → ‖H j ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ KG) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x T : ℝ, |x| ≤ 1 / 2 → T0 ≤ T → 0 ≤ T →
      ‖Phi0 n G H ![conj ((x : ℂ) + (T : ℂ) * Complex.I), 1] ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        K * (1 + T) ^ (n + 1) := by
  refine ⟨∑ j ∈ Finset.range (n + 2), (2 * KG) * ((n + 1).choose j : ℝ), by positivity, fun x T hx hT0 hT => ?_⟩
  set z : ℂ := (x : ℂ) + (T : ℂ) * Complex.I with hz
  have hzn : ‖z‖ ≤ 1 + T := by
    refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg hT]
    linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  rw [Phi0_eq_sum]
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => ?_))
  have hj' : j ≤ n + 1 := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, one_pow, mul_one]
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj]
  have h1 : ‖G j z + conj (H j z)‖ ≤ 2 * KG := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_conj]
    linarith [hG j (by omega) x T hx hT0, hH j (by omega) x T hx hT0]
  have h2 : ‖z‖ ^ (n + 1 - j) ≤ (1 + T) ^ (n + 1) := by
    calc ‖z‖ ^ (n + 1 - j) ≤ (1 + T) ^ (n + 1 - j) := pow_le_pow_left₀ (norm_nonneg _) hzn _
      _ ≤ (1 + T) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 := norm_cc_le n j
  have hKG : 0 ≤ 2 * KG := by linarith
  calc ‖G j z + conj (H j z)‖ * ‖cc n j‖ * ‖z‖ ^ (n + 1 - j)
      ≤ (2 * KG) * ((n + 1).choose j : ℝ) * (1 + T) ^ (n + 1) := by
        apply mul_le_mul (mul_le_mul h1 h3 (norm_nonneg _) hKG) h2 (by positivity) (by positivity)
    _ = _ := by ring

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
