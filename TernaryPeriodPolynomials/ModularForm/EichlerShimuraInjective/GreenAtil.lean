module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.SetupAtil

@[expose] public section


/-!
# Green's formula for the coset sum

`stokes_Atil`: `∬_{F_T} ∂_z Ã = -(i/2) ∫ Ã(x+iT) dx`, where `Ã` is the `SL₂(ℤ)`-covariant coset sum.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane MeasureTheory Set intervalIntegral
open scoped UpperHalfPlane ComplexConjugate MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

open TernaryPeriodPolynomials.Argument.SeedC3

section Main

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {n : ℕ} {f g : ℂ → ℂ} {Gf Gg : ℕ → ℂ → ℂ}
  {v : MvPolynomial (Fin 2) ℂ}

/-- The Wirtinger derivative of the coset sum. -/
def DAtil (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Γ, ((dnm (toR (gq Γ q)) z ^ 2)⁻¹ * (conj (dnm (toR (gq Γ q)) z ^ 2))⁻¹ *
    ((f (mob (toR (gq Γ q)) z) * conj (f (mob (toR (gq Γ q)) z))) *
      (mob (toR (gq Γ q)) z - conj (mob (toR (gq Γ q)) z)) ^ (n + 1)))

theorem Atil_T (S : Setup Γ n f g Gf Gg v) {z : ℂ} (hz : 0 < z.im) :
    Atil Γ (Aval n f Gf Gg v) (z + 1) = Atil Γ (Aval n f Gf Gg v) z := by
  have := Atil_cov (Aval n f Gf Gg v) (Aval_Gamma S) ModularGroup.T hz
  rw [mob_T, dnm_T] at this
  simpa using this

theorem Atil_S (S : Setup Γ n f g Gf Gg v) {z : ℂ} (hz : 0 < z.im) :
    Atil Γ (Aval n f Gf Gg v) (-1 / z) = conj z ^ 2 * Atil Γ (Aval n f Gf Gg v) z := by
  have := Atil_cov (Aval n f Gf Gg v) (Aval_Gamma S) ModularGroup.S hz
  rw [mob_S, dnm_S] at this
  exact this

/-- **Green's formula for the coset sum** on the truncated fundamental domain of `SL₂(ℤ)`. -/
theorem stokes_Atil (S : Setup Γ n f g Gf Gg v) {T : ℝ} (hT : 1 ≤ T) :
    ∫ x in (-1 / 2 : ℝ)..(1 / 2), ∫ y in arcY x..T, DAtil Γ n f ((x : ℂ) + (y : ℂ) * Complex.I) =
      -(Complex.I / 2) * ∫ x in (-1 / 2 : ℝ)..(1 / 2),
        Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I) := by
  have hu : ∀ p : (SL(2, ℤ) ⧸ Γ) × ι0 n, DifferentiableOn ℂ (uQ (gq Γ) (u0 n Gf) p) Uset :=
    fun p => uQ_diff (gq Γ) (u0_diff S.dGf) p
  have hw : ∀ p : (SL(2, ℤ) ⧸ Γ) × ι0 n, DifferentiableOn ℂ (wQ (gq Γ) (w0 n f Gg v) p) Uset :=
    fun p => wQ_diff (gq Γ) (w0_diff S.hf S.dGg) p
  have hS' : ∀ z : ℂ, 0 < z.im → 0 < (-1 / z).im := fun z hz => by
    have := mob_mem_Uset ModularGroup.S hz
    rwa [mob_S] at this
  have h := stokes_ha hu hw
    (fun z hz => by
      rw [← Atil_eq_holAnti S hz, ← Atil_eq_holAnti S (by simpa using hz)]
      exact Atil_T S hz)
    (fun z hz => by
      rw [← Atil_eq_holAnti S hz, ← Atil_eq_holAnti S (hS' z hz)]
      exact Atil_S S hz) hT
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hR : ∫ x in (-1 / 2 : ℝ)..(1 / 2), holAnti (uQ (gq Γ) (u0 n Gf)) (wQ (gq Γ) (w0 n f Gg v))
      ((x : ℂ) + (T : ℂ) * Complex.I) =
      ∫ x in (-1 / 2 : ℝ)..(1 / 2), Atil Γ (Aval n f Gf Gg v) ((x : ℂ) + (T : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact (Atil_eq_holAnti S (by simpa using hT0)).symm
  have hL : ∀ x ∈ uIcc (-1 / 2 : ℝ) (1 / 2), (∫ y in arcY x..T,
      holAntiD (wQ (gq Γ) (w0 n f Gg v)) (fun i => deriv (uQ (gq Γ) (u0 n Gf) i))
        ((x : ℂ) + (y : ℂ) * Complex.I)) = ∫ y in arcY x..T, DAtil Γ n f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hxa : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [uIcc_of_le ((arcY_le_one x).trans hT)] at hy
    have hy0 : 0 < y := lt_of_lt_of_le (arcY_pos hxa) hy.1
    have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy0
    rw [holAntiD_Q (gq Γ) (w0 n f Gg v) (u0_diff S.dGf) hz]
    unfold DAtil
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [holAntiD_w0 S.dGf (mob_mem_Uset (gq Γ q) hz)]
  rw [hR] at h
  rw [← h]
  exact (intervalIntegral.integral_congr hL).symm

end Main

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
