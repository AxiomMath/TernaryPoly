module

public import Mathlib

@[expose] public section


/-!
# Elementary growth bounds

`(1+T)^k e^{-cT} → 0`, and the norm of a polynomial evaluation bounded by a power of `1 + |a₀| + |a₁|`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

theorem tendsto_poly_exp (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => (1 + T) ^ k * Real.exp (-c * T)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc
  have h2 : Tendsto (fun T : ℝ => 1 + T) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h3 := (h1.comp h2).const_mul (Real.exp c)
  simp only [mul_zero] at h3
  refine h3.congr (fun T => ?_)
  simp only [Function.comp, Real.rpow_natCast]
  rw [show -c * (1 + T) = -c + -c * T by ring, Real.exp_add]
  have : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp c * ((1 + T) ^ k * (Real.exp (-c) * Real.exp (-c * T)))
      = (Real.exp c * Real.exp (-c)) * ((1 + T) ^ k * Real.exp (-c * T)) := by ring
    _ = _ := by rw [this, one_mul]

theorem norm_eval_le (P : MvPolynomial (Fin 2) ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : Fin 2 → ℂ, ‖MvPolynomial.eval a P‖ ≤ K * (1 + ‖a 0‖ + ‖a 1‖) ^ P.totalDegree := by
  refine ⟨∑ d ∈ P.support, ‖P.coeff d‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun a => ?_⟩
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d hd => ?_))
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set B := 1 + ‖a 0‖ + ‖a 1‖ with hB
  have hB1 : 1 ≤ B := by rw [hB]; linarith [norm_nonneg (a 0), norm_nonneg (a 1)]
  have hdeg : d 0 + d 1 ≤ P.totalDegree := by
    have := MvPolynomial.le_totalDegree hd
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using this
  rw [Fin.prod_univ_two]
  simp only [norm_pow]
  calc ‖a 0‖ ^ d 0 * ‖a 1‖ ^ d 1 ≤ B ^ d 0 * B ^ d 1 := by
        apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (by rw [hB]; linarith [norm_nonneg (a 1)]) _)
          (pow_le_pow_left₀ (norm_nonneg _) (by rw [hB]; linarith [norm_nonneg (a 0)]) _)
          (by positivity) (by positivity)
    _ = B ^ (d 0 + d 1) := (pow_add _ _ _).symm
    _ ≤ B ^ P.totalDegree := pow_le_pow_right₀ hB1 hdeg

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
