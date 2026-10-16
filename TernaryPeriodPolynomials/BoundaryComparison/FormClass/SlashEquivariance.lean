module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AdelicValue

@[expose] public section


/-!
# Towards a `Γ(N)`-level `v_h`: slash equivariance of `F_h`

Formalized by Claude Sonnet 5.5.

`Fh_sl2_mul_slash`: for ANY function `h : ℍ → ℂ`, `δ ∈ SL₂(ℤ)` and `X ∈ GL₂⁺(ℝ)`, `F_h(δ X) = F_{h|_k δ}(X)`.  For a level-one cusp form `h|_k δ = h`, which is H4's `Fh_sl2_mul`;
for a `Γ(N)`-form it is the equivariance that the `Γ(N)`-analogue of `vhValue` needs (replace `h` by `h|_k δ_k^{-1}` for a lift `δ_k ∈ SL₂(ℤ)` of the level-`N` part of `γ g_f`).
-/

open Matrix UpperHalfPlane ModularForm
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.FhSL2Invariance

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem Fh_sl2_mul_slash (k : ℤ) (h : UpperHalfPlane → ℂ) (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (X : GL (Fin 2) ℝ) (hX : 0 < (Matrix.GeneralLinearGroup.det X).val) :
    Fh k h (sl2 δ * X) = Fh k (h ∣[k] sl2 δ) X := by
  unfold Fh Nf
  have hdet : (Matrix.GeneralLinearGroup.det (sl2 δ * X)).val =
      (Matrix.GeneralLinearGroup.det X).val := by
    rw [map_mul, Units.val_mul, sl2_det, one_mul]
  have hden : UpperHalfPlane.denom (sl2 δ * X) Complex.I =
      UpperHalfPlane.denom (sl2 δ) ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) *
        UpperHalfPlane.denom X Complex.I := by
    rw [UpperHalfPlane.denom_cocycle _ _ (by simp)]
    rw [UpperHalfPlane.coe_smul_of_det_pos hX UpperHalfPlane.I]
    rfl
  have hA : UpperHalfPlane.denom (sl2 δ) ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ≠ 0 :=
    UpperHalfPlane.denom_ne_zero_of_im _ (by
      rw [UpperHalfPlane.coe_im]
      exact ((X • UpperHalfPlane.I : UpperHalfPlane).im_pos).ne')
  have hs : (h ∣[k] sl2 δ) (X • UpperHalfPlane.I) =
      UpperHalfPlane.denom (sl2 δ) ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ (-k) *
        h (sl2 δ • (X • UpperHalfPlane.I)) := by
    simp [slash_apply, σ, mul_comm]
  rw [mul_smul, hs, hdet, hden, mul_zpow]
  ring

end TernaryPeriodPolynomials.Argument.FormClassK
