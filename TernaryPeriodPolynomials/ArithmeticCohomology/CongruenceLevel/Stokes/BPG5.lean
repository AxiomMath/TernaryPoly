module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BPG4

@[expose] public section


/-!
# Plane geometry package, part 5: powers of the cusp generator

Formalized by Claude Sonnet 5.5.

`PKw w k = (colSL w) [[1, 6k], [0, 1]] (colSL w)⁻¹ ∈ Γ(6)`: additive in `k` (`PKw_add`), equal to the positive parabolic generator `posParSL w` for `k = 1` (`PKw_one`), so that an additive function `ψ` on `Γ(6)` satisfies
`ψ (PKw w k) = k ψ (posParSL w)` (`psi_PKw`).
-/

open scoped MatrixGroups
open CongruenceSubgroup Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

/-- The matrix `(colSL w) [[1, 6k], [0, 1]] (colSL w)⁻¹`. -/
def PKwMat (w : Prim2) (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (colSL w : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 6 * k; 0, 1] * ((colSL w)⁻¹ : SL(2, ℤ))

theorem PKwMat_det (w : Prim2) (k : ℤ) : (PKwMat w k).det = 1 := by
  have h1 : (colSL w : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := (colSL w).2
  have h2 : (((colSL w)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := ((colSL w)⁻¹).2
  rw [PKwMat, Matrix.det_mul, Matrix.det_mul, h1, h2, Matrix.det_fin_two_of]
  simp

theorem PKwMat_mem (w : Prim2) (k : ℤ) : (⟨PKwMat w k, PKwMat_det w k⟩ : SL(2, ℤ)) ∈ Gamma 6 := by
  refine Gamma_mem.2 ?_
  have hQ : (colSL w : Matrix (Fin 2) (Fin 2) ℤ) * (((colSL w)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have hT : (!![1, 6 * k; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (6 * k) • !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  set X : Matrix (Fin 2) (Fin 2) ℤ := (colSL w : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; 0, 0] * (((colSL w)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hX
  have hP : PKwMat w k = 1 + (6 * k) • X := by
    rw [PKwMat, hT, hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQ, Matrix.mul_smul, Matrix.smul_mul]
  have h6 : (6 : ZMod 6) = 0 := by decide
  have hent : ∀ i j, PKwMat w k i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + 6 * (k * X i j) := by
    intro i j
    rw [hP, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  show ((PKwMat w k 0 0 : ℤ) : ZMod 6) = 1 ∧ ((PKwMat w k 0 1 : ℤ) : ZMod 6) = 0 ∧ ((PKwMat w k 1 0 : ℤ) : ZMod 6) = 0 ∧
    ((PKwMat w k 1 1 : ℤ) : ZMod 6) = 1
  rw [hent, hent, hent, hent]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h6]

/-- `(colSL w) T^{6k} (colSL w)⁻¹` as an element of `Γ(6)`. -/
def PKw (w : Prim2) (k : ℤ) : Gamma 6 := ⟨⟨PKwMat w k, PKwMat_det w k⟩, PKwMat_mem w k⟩

theorem PKw_add (w : Prim2) (k l : ℤ) : PKw w (k + l) = PKw w k * PKw w l := by
  have hQ : (((colSL w)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (colSL w : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  apply Subtype.ext
  apply Subtype.ext
  show PKwMat w (k + l) = PKwMat w k * PKwMat w l
  have : PKwMat w k * PKwMat w l = (colSL w : Matrix (Fin 2) (Fin 2) ℤ) *
      (!![1, 6 * k; 0, 1] * ((((colSL w)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (colSL w : Matrix (Fin 2) (Fin 2) ℤ)) * !![1, 6 * l; 0, 1]) *
      ((colSL w)⁻¹ : SL(2, ℤ)) := by
    simp only [PKwMat, Matrix.mul_assoc]
  rw [this, hQ, Matrix.mul_one]
  unfold PKwMat
  congr 2
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem psi_PKw (ψ : Gamma 6 → ℚ) (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) (w : Prim2) (k : ℤ) :
    ψ (PKw w k) = k * ψ (PKw w 1) := by
  let f : ℤ →+ ℚ := AddMonoidHom.mk' (fun k => ψ (PKw w k)) (fun k l => by rw [PKw_add, hψ])
  have := map_zsmul f k 1
  simpa [f] using this

theorem PKw_one (w : Prim2) : PKw w 1 = posParSL w.1 := by
  apply Subtype.ext
  apply Subtype.ext
  show PKwMat w 1 = (posPar w.1 : Matrix (Fin 2) (Fin 2) ℤ)
  have h := posPar_conj (colSL w) ![1, 0]
  have e : (posPar ![1, 0] : SL(2, ℤ)) = ⟨!![1, 6; 0, 1], by simp [Matrix.det_fin_two]⟩ := by
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [posPar]
  rw [e, colSL_mulVec] at h
  have := congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  rw [← this, PKwMat]
  simp only [mul_one]
  rfl

end TernaryPeriodPolynomials.Argument.GammaNStokes
