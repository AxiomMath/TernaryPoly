module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.Defs

@[expose] public section


/-! Clause (iv) of Lemma C.3 (`ar:lem:seed`): at `u = 0` the radical cochain
`(τY - X)ⁿ(1, -τ)` is the gradient of the potential `-(τY - X)^{n+1}/(n+1)`.
Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `∂/∂X` of the linear form `𝓑 = τY - X + (u₁ - τu₂)Z` is the constant `-1`. -/
theorem seedLinear_pderiv_zero (p : Fin 5 → ℝ) :
    pderiv (0 : Fin 3) (seedLinear p) = -1 := by
  have e1 : pderiv (0 : Fin 3) (C (seedTau p) * X 1 - X 0) = -1 := by
    rw [map_sub, pderiv_C_mul, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
      pderiv_X_self, mul_zero, zero_sub]
  have e3 : pderiv (0 : Fin 3) (C ((p 0 : ℂ) - seedTau p * (p 1 : ℂ)) * X 2) = 0 := by
    rw [pderiv_C_mul, pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide), mul_zero]
  change pderiv (0 : Fin 3)
      (C (seedTau p) * X 1 - X 0 + C ((p 0 : ℂ) - seedTau p * (p 1 : ℂ)) * X 2) = -1
  rw [map_add, e1, e3, add_zero]

/-- `∂/∂Y` of the linear form `𝓑 = τY - X + (u₁ - τu₂)Z` is the constant `τ`. -/
theorem seedLinear_pderiv_one (p : Fin 5 → ℝ) :
    pderiv (1 : Fin 3) (seedLinear p) = C (seedTau p) := by
  have e1 : pderiv (1 : Fin 3) (C (seedTau p) * X 1 - X 0) = C (seedTau p) := by
    rw [map_sub, pderiv_C_mul, pderiv_X_self, mul_one,
      pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide), sub_zero]
  have e3 : pderiv (1 : Fin 3) (C ((p 0 : ℂ) - seedTau p * (p 1 : ℂ)) * X 2) = 0 := by
    rw [pderiv_C_mul, pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero]
  change pderiv (1 : Fin 3)
      (C (seedTau p) * X 1 - X 0 + C ((p 0 : ℂ) - seedTau p * (p 1 : ℂ)) * X 2) = C (seedTau p)
  rw [map_add, e1, e3, add_zero]

/-- Clause (iv) of Lemma C.3: the gradient of the potential `-𝓑^{n+1}/(n+1)` along `X` and `Y`
recovers the radical cochain `𝓑ⁿ β`, i.e. `𝓑ⁿ` and `-τ𝓑ⁿ`. The target's hypotheses `p 0 = 0`,
`p 1 = 0` are not needed: the identity holds for every `p`. -/
theorem lemma_C3_iv (n : ℕ) (p : Fin 5 → ℝ) :
    pderiv 0 (-(C ((n : ℂ) + 1)⁻¹ * seedLinear p ^ (n + 1))) =
        C (seedBeta p 0) * seedLinear p ^ n ∧
      pderiv 1 (-(C ((n : ℂ) + 1)⁻¹ * seedLinear p ^ (n + 1))) =
        C (seedBeta p 1) * seedLinear p ^ n := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h2 : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h2]; exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hb0 : seedBeta p 0 = (1 : ℂ) := by simp [seedBeta]
  have hb1 : seedBeta p 1 = -seedTau p := by simp [seedBeta]
  have hpow : seedLinear p ^ (n + 1 - 1) = seedLinear p ^ n := by rw [Nat.add_sub_cancel]
  have hcast : (((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ)) = C ((n : ℂ) + 1) := by
    rw [← map_natCast C (n + 1)]
    congr 1
    push_cast
    ring
  have hAB : C (((n : ℂ) + 1)⁻¹) * ((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ) = 1 := by
    rw [hcast, ← map_mul, inv_mul_cancel₀ hn1, map_one]
  constructor
  · rw [map_neg, pderiv_C_mul, pderiv_pow, seedLinear_pderiv_zero, hpow, hb0, map_one]
    rw [show (-(C (((n : ℂ) + 1)⁻¹) *
          (((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ) * seedLinear p ^ n * (-1)))) =
        (C (((n : ℂ) + 1)⁻¹) * ((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ)) * seedLinear p ^ n by
      ring]
    rw [hAB]
  · rw [map_neg, pderiv_C_mul, pderiv_pow, seedLinear_pderiv_one, hpow, hb1, map_neg]
    rw [show (-(C (((n : ℂ) + 1)⁻¹) *
          (((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ) * seedLinear p ^ n * C (seedTau p)))) =
        -(C (((n : ℂ) + 1)⁻¹) * ((n + 1 : ℕ) : MvPolynomial (Fin 3) ℂ)) *
          (seedLinear p ^ n * C (seedTau p)) by
      ring]
    rw [hAB]
    ring

end TernaryPeriodPolynomials.Argument
