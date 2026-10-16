module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.DictionaryCusp

@[expose] public section


/-!
# Full `SL₂(ℤ)`-invariance of `F_h` for level-one cusp forms (step (c))

Formalized by Claude Haiku 5.5.

For `h : CuspForm levelOne k`, `δ ∈ SL₂(ℤ)` and `X ∈ GL₂(ℝ)` with `det X > 0`:
`F_h(δ X) = F_h(X)` (the paper's `F_h` of the paper).
Derived from the slash invariance of `h` under `δ` and the cocycle `denom_cocycle`.
-/

open Matrix UpperHalfPlane ModularForm
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.FhSL2Invariance

/-- The real image of `δ ∈ SL₂(ℤ)` in `GL₂(ℝ)`. -/
abbrev sl2 (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ δ

theorem sl2_det (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (Matrix.GeneralLinearGroup.det (sl2 δ)).val = 1 := by
  rw [Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]

theorem sl2_mem (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : sl2 δ ∈ levelOne :=
  ⟨δ, rfl⟩

theorem slash_sl2 {k : ℤ} (h : CuspForm levelOne k) (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (⇑h ∣[k] sl2 δ) = ⇑h :=
  SlashInvariantFormClass.slash_action_eq h _ (sl2_mem δ)

/-- The weight-`k` transformation of a level-one cusp form under any `δ ∈ SL₂(ℤ)`. -/
theorem cusp_sl2_transform {k : ℤ} (h : CuspForm levelOne k)
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    h (sl2 δ • z) = (UpperHalfPlane.denom (sl2 δ) (z : ℂ)) ^ k * h z := by
  have hz := congrFun (slash_sl2 h δ) z
  simp [slash_apply, σ] at hz
  have hd : UpperHalfPlane.denom (sl2 δ) (z : ℂ) ≠ 0 :=
    UpperHalfPlane.denom_ne_zero_of_im _ (by rw [UpperHalfPlane.coe_im]; exact (z.im_pos).ne')
  have hk : (UpperHalfPlane.denom (sl2 δ) (z : ℂ)) ^ k ≠ 0 := zpow_ne_zero _ hd
  have hinv : (UpperHalfPlane.denom (sl2 δ) (z : ℂ)) ^ k *
      ((UpperHalfPlane.denom (sl2 δ) (z : ℂ)) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hk
  linear_combination ((UpperHalfPlane.denom (sl2 δ) (z : ℂ)) ^ k) * hz
    - (h (sl2 δ • z)) * hinv

/-- Full `SL₂(ℤ)`-invariance of `F_h` on `GL₂⁺(ℝ)`: `F_h(δ X) = F_h(X)`. -/
theorem Fh_sl2_mul (k : ℤ) {h : CuspForm levelOne k} (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (X : GL (Fin 2) ℝ) (hX : 0 < (Matrix.GeneralLinearGroup.det X).val) :
    Fh k ⇑h (sl2 δ * X) = Fh k ⇑h X := by
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
  have hcT := cusp_sl2_transform h δ (X • UpperHalfPlane.I)
  rw [mul_smul, hcT, hdet, hden, mul_zpow]
  have hw : ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  have hA : UpperHalfPlane.denom (sl2 δ) ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ≠ 0 :=
    UpperHalfPlane.denom_ne_zero_of_im _ (by
      rw [UpperHalfPlane.coe_im]
      exact ((X • UpperHalfPlane.I : UpperHalfPlane).im_pos).ne')
  have hA1 : UpperHalfPlane.denom (sl2 δ) ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ (-k) *
      UpperHalfPlane.denom (sl2 δ) ((X • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hA]
    simp
  linear_combination (((Matrix.GeneralLinearGroup.det X).val : ℝ) : ℂ) ^ ((k : ℂ) / 2) *
    UpperHalfPlane.denom X Complex.I ^ (-k) * h (X • UpperHalfPlane.I) * hA1

end TernaryPeriodPolynomials.Argument.LatticeCounts.FhSL2Invariance
