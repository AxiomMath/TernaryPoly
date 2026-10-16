module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Coefficients
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Series

@[expose] public section


open MvPolynomial UpperHalfPlane ModularForm Matrix
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# `E^∨ = E∘ȷ` is the literal contragredient `E*`, for the actual coefficient representation of `Γ`

Formalized by Claude Sonnet 5.5.

Bridges `DualCoefficients.dualIso_equivariant` (for `GL₃(ℂ)`) to the coefficient representation
`gammaRhoC Γ n` (`= homogeneousAction n (-1)` composed with `Γ → GL₃(ℝ) → GL₃(ℂ)`) and the dual coefficient system `dualRho` of
the dual series: `map_gammaSigma_jmath` (the matrix of `ȷ(δ)` is `J (δ⁻¹)ᵗ J`), `dualRepC` (the literal dual `E*` with the contragredient
action) and `dualIso_dualRho` : `dualIso (ρ(ȷ δ) q) = δ · dualIso q` in `E*`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3 GeneralEisenstein
open TernaryPeriodPolynomials.Argument.GammaNFaces

variable (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (α : Γ →* Γ')
  (hα : ∀ g : Γ, (α g).1 = jmath g.1)

theorem Jm_mul_transpose_mul (M : Matrix (Fin 3) (Fin 3) ℂ) : Jm * Mᵀ * Jm = rt M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, rt, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

include hα in
theorem map_gammaSigma_jmath (δ : Γ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ' (α δ)) =
      jGL (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ δ)) := by
  apply Units.ext
  have h1 : ((gammaSigma Γ' (α δ) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = realMat (jmath δ.1) := by
    rw [gammaSigma_val, hα]
  have h2 : (((gammaSigma Γ δ)⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = realMat δ.1⁻¹ := by
    rw [← map_inv, gammaSigma_val]
    rfl
  change ((gammaSigma Γ' (α δ) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).map (algebraMap ℝ ℂ) =
    Jm * ((((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ δ))⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ))ᵀ * Jm
  rw [Jm_mul_transpose_mul, ← map_inv, h1, realMat_jmath]
  have h3 : ((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) ((gammaSigma Γ δ)⁻¹) : GL3) : Matrix (Fin 3) (Fin 3) ℂ) =
      ((realMat δ.1)⁻¹).map (algebraMap ℝ ℂ) := by
    change (((gammaSigma Γ δ)⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).map (algebraMap ℝ ℂ) = _
    rw [h2, realMat_inv]
  rw [h3]
  rfl

/-- The literal dual `E*` of the complex coefficient representation of `Γ`: `Module.Dual ℂ (Sym^n)` with the contragredient action. -/
abbrev dualRepC (n : ℕ) : Representation ℂ Γ (Module.Dual ℂ (HomogeneousPoly n)) := (gammaRhoC Γ n).dual

theorem gammaRhoC_eq (n : ℕ) (δ : Γ) :
    gammaRhoC Γ n δ = homogeneousAction n (-1) (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ δ)) := rfl

theorem dualRepC_eq (n : ℕ) (δ : Γ) :
    dualRepC Γ n δ = (homogeneousAction n (-1)).dual (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ δ)) := by
  have e1 : gammaSigma Γ δ⁻¹ = (gammaSigma Γ δ)⁻¹ := map_inv _ _
  have e2 : Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) ((gammaSigma Γ δ)⁻¹) =
      (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ δ))⁻¹ := map_inv _ _
  rw [dualRepC, Representation.dual_apply, Representation.dual_apply, gammaRhoC_eq, e1, e2]

include hα in
/-- **`E^∨ = E∘ȷ` is the contragredient `E*` after the coordinate change `J`** (explicit and equivariant): the linear isomorphism
`dualIso n` intertwines `δ ↦ ρ(ȷ(δ))` (`dualRho`) with the contragredient of `ρ(δ)`. -/
theorem dualIso_dualRho (n : ℕ) (δ : Γ) (q : Coef n) :
    dualIso n (dualRho Γ Γ' α n δ q).val = dualRepC Γ n δ (dualIso n q.val) := by
  have h := dualIso_equivariant n (-1) (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (gammaSigma Γ δ)) q.val
  rw [← map_gammaSigma_jmath Γ Γ' α hα δ] at h
  rw [dualRepC_eq]
  refine Eq.trans ?_ h
  rfl

end TernaryPeriodPolynomials.Argument.EisensteinDual
