module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PsiIntegral

@[expose] public section


/-!
# The `E`-valued intertwiner `Tφ(y; i, j)`: integrability at a general point and commutation with the line-face pullback

Formalized by Claude Sonnet 5.5.

* `FzE_integral`, `TcoefK_integrable`: for every `y ∈ Ω`, `i, j`, `m` the coefficient of `(Tφ^b)(g)(y; i, j)` is an absolutely convergent
  integral over `𝔸²`, with value `cx b (Σ_o ∫_{ℝ²} PsiCoefQ(c_o)(N v) dv)`.
* `TformK b k y i j`: the polynomial `Σ_{m ∈ monSet n} TcoefK(m) x^m` (the integral of the homogeneous polynomial-valued section).
* `fPull_TformK`: **`T` commutes with the line-face pullback**: the `(x; e_p, e_q)`, `m` coordinate of `jFace^*(Tφ^b)` is
  `∫_{𝔸²} printedIntegrandB`, i.e. the integral of the pullback of `φ^b(w₀⁻¹u g)`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open MvPolynomial
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem FzE_false_integral (hN : 3 ≤ N) (hn : 4 ≤ n) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    Integrable (FzE N k n f false y i j m) nuZ ∧
    ∫ z, FzE N k n f false y i j m z ∂nuZ = ∑' o : FreeOrbK N k, ∫ v : Fin 2 → ℝ, psiO N k n f y i j m o ((N : ℝ) • v) := by
  have hfin : ∀ o, finMeas2 (pieceFinK N k o) < ⊤ := fun o => by
    rw [volume_pieceFinK]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by simp [NeZero.pos])) (ENNReal.inv_lt_top.2 (by simp [NeZero.pos]))
  have hon : ∀ o z, z.1 ∈ pieceFinK N k o →
      FzE N k n f false y i j m z = psiO N k n f y i j m o (shiftV (orbPtK N k o) z.2) := by
    intro o z hz
    rw [FzE_on_piece N k n f hN false hy i j m o hz z.2]
    simp [cx, psiO]
  have hzero : ∀ z, (∀ o, z.1 ∉ pieceFinK N k o) → FzE N k n f false y i j m z = 0 := by
    intro z hz
    by_cases hd : ∃ π κ, IsDecomp N (gFin z.1 * kInvFin k) π κ
    · obtain ⟨o, ho⟩ := exists_orbit_of_decompK N k z.1 hd
      exact absurd ho (hz o)
    · exact FzE_eq_zero_of_not N k n f false y i j m z.1 z.2 hd
  have hG : ∀ o, Integrable (fun w => psiO N k n f y i j m o (shiftV (orbPtK N k o) w)) := fun o =>
    (integrable_shiftV _ _).2 (psiO_integrable N k n f hn hy i j m o)
  have hsum : Summable fun o : FreeOrbK N k => finMeas2.real (pieceFinK N k o) *
      ∫ w, ‖psiO N k n f y i j m o (shiftV (orbPtK N k o) w)‖ := by
    refine (psiO_norm_summable N k n f hn hy i j m).congr fun o => ?_
    rw [real_pieceFinK, integral_shiftV (orbPtK N k o) (fun v => ‖psiO N k n f y i j m o v‖),
      integral_norm_psiO]
  obtain ⟨hI, hE⟩ := cells_integral (pieceFinK N k) (pieceFinK_measurable N k) hfin (pieceFinK_disjoint N k hN)
    (FzE N k n f false y i j m) (fun o w => psiO N k n f y i j m o (shiftV (orbPtK N k o) w)) hon hzero hG hsum
  refine ⟨hI, hE.trans (tsum_congr fun o => ?_)⟩
  rw [integral_shiftV (orbPtK N k o) (psiO N k n f y i j m o), real_pieceFinK, integral_psiO]
  push_cast
  rfl

theorem FzE_eq_cx (b : Bool) (y : Fin 5 → ℝ) (i j : Fin 5) (m : Fin 3 →₀ ℕ) :
    FzE N k n f b y i j m = fun z => cx b (FzE N k n f false y i j m z) := by
  funext z
  unfold FzE
  rw [coeff_cxP, cxP_false]

/-- **Integrability and value of the `E`-valued intertwiner at a general point `y ∈ Ω`**, for both seed types. -/
theorem FzE_integral (hN : 3 ≤ N) (hn : 4 ≤ n) (b : Bool) {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    Integrable (FzE N k n f b y i j m) nuZ ∧
    ∫ z, FzE N k n f b y i j m z ∂nuZ =
      cx b (∑' o : FreeOrbK N k, ∫ v : Fin 2 → ℝ, psiO N k n f y i j m o ((N : ℝ) • v)) := by
  obtain ⟨hI, hE⟩ := FzE_false_integral N k n f hN hn hy i j m
  rw [FzE_eq_cx]
  refine ⟨?_, ?_⟩
  · have := ((cxL b).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hI
    simpa [cxL_apply] using this
  · have := (cxL b).toContinuousLinearEquiv.integral_comp_comm (fun z => FzE N k n f false y i j m z) (μ := nuZ)
    simp [cxL_apply] at this
    rw [this, hE]

end TernaryPeriodPolynomials.Argument.FormClassK
