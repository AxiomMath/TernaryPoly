module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Phi0Bound

@[expose] public section


/-!
# Polynomial bound for the remainder

`R_bound`: `‖R_σ(z)‖ ≤ K (1 + ‖z‖)^D`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral Filter Topology
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

theorem Phi_eq_eval (n : ℕ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ) (a : Fin 2 → ℂ) (w : ℂ) :
    Phi n Gf Gg v a w = MvPolynomial.eval a
      (eichlerPoly n Gf w + MvPolynomial.map (starRingEnd ℂ) (eichlerPoly n Gg w) + v) := by
  unfold Phi Phi0
  rw [map_add, map_add]

theorem R_bound (n : ℕ) (Gf Gg : ℕ → ℂ → ℂ) (v : MvPolynomial (Fin 2) ℂ) (σ : SL(2, ℤ)) :
    ∃ (K : ℝ) (D : ℕ), 0 ≤ K ∧ ∀ z : ℂ, 0 < z.im →
      ‖Phi n Gf Gg v (conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1]) (mob (toR σ) Complex.I)‖ ≤
        K * (1 + ‖z‖) ^ D := by
  set Pw := eichlerPoly n Gf (mob (toR σ) Complex.I) +
    MvPolynomial.map (starRingEnd ℂ) (eichlerPoly n Gg (mob (toR σ) Complex.I)) + v with hPw
  obtain ⟨K, hK0, hK⟩ := norm_eval_le Pw
  set L : ℝ := 1 + |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0| +
    |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1| +
    |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0| +
    |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1| with hL
  have hL1 : 0 ≤ L := by
    rw [hL]
    have := abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
    have := abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1)
    have := abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
    have := abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1)
    linarith
  refine ⟨K * L ^ Pw.totalDegree, Pw.totalDegree, by positivity, fun z hz => ?_⟩
  rw [Phi_eq_eval]
  refine (hK _).trans ?_
  have hJ : dnm (toR σ) z ≠ 0 := dnm_ne_zero _ hz
  have h0 : dnm (toR σ) z * mob (toR σ) z = (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) * z +
      (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) := by
    have hm : mob (toR σ) z = ((((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) * z +
      (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ)) / dnm (toR σ) z := rfl
    rw [hm]
    exact mul_div_cancel₀ _ hJ
  have hz0 := norm_nonneg z
  have ha0 : ‖(conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1] : Fin 2 → ℂ) 0‖ ≤
      |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0| * ‖z‖ +
        |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1| := by
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    rw [← map_mul, Complex.norm_conj, h0]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact le_rfl
  have ha1 : ‖(conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1] : Fin 2 → ℂ) 1‖ ≤
      |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0| * ‖z‖ +
        |((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1| := by
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one]
    rw [Complex.norm_conj]
    unfold dnm
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact le_rfl
  have hB : 1 + ‖(conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1] : Fin 2 → ℂ) 0‖ +
      ‖(conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1] : Fin 2 → ℂ) 1‖ ≤ L * (1 + ‖z‖) := by
    rw [hL]
    nlinarith [abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0),
      abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1),
      abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0),
      abs_nonneg (((toR σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1)]
  calc K * (1 + ‖(conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1] : Fin 2 → ℂ) 0‖ +
        ‖(conj (dnm (toR σ) z) • ![conj (mob (toR σ) z), 1] : Fin 2 → ℂ) 1‖) ^ Pw.totalDegree
      ≤ K * (L * (1 + ‖z‖)) ^ Pw.totalDegree := by
        gcongr
    _ = K * L ^ Pw.totalDegree * (1 + ‖z‖) ^ Pw.totalDegree := by rw [mul_pow]; ring

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
