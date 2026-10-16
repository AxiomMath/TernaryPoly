module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BLine5

@[expose] public section


/-!
# The involution `M ↦ W (M⁻¹)ᵗ W` of `SL₃(ℤ)` exchanging line and plane stabilizers

Formalized by Claude Sonnet 5.5.

`tau M = W (M⁻¹)ᵗ W` with `W` the antidiagonal permutation matrix is an involutive automorphism of `SL₃(ℤ)` (`tau_tau`) with `(tau M)ᵢⱼ = (M⁻¹)_{rev j, rev i}`.  It preserves `Γ(6)` and the upper triangular
group, and exchanges the Borel of a line (first column `(*, 0, 0)ᵗ`) with the Borel of a plane (bottom row `(0, 0, *)`).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- The antidiagonal permutation matrix. -/
def Wm : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem Wm_mul_Wm : Wm * Wm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Wm, Matrix.mul_apply, Fin.sum_univ_three]

theorem Wm_transpose : Wmᵀ = Wm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Wm]

theorem Wm_det : Wm.det = -1 := by simp [Wm, Matrix.det_fin_three]

/-- The matrix of `tau M`. -/
def tauMat (M : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ := Wm * ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ)ᵀ * Wm

theorem tauMat_det (M : SL(3, ℤ)) : (tauMat M).det = 1 := by
  rw [tauMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, (M⁻¹).2, Wm_det]
  norm_num

theorem conj_mul3 (W A B : Matrix (Fin 3) (Fin 3) ℤ) (h : W * W = 1) : W * A * W * (W * B * W) = W * (A * B) * W := by
  calc W * A * W * (W * B * W) = W * A * (W * W) * B * W := by simp only [Matrix.mul_assoc]
    _ = W * (A * B) * W := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem tauMat_mul (M N : SL(3, ℤ)) : tauMat (M * N) = tauMat M * tauMat N := by
  rw [tauMat, tauMat, tauMat, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
  exact (conj_mul3 Wm _ _ Wm_mul_Wm).symm

/-- **The involution exchanging lines and planes.** -/
def tau : SL(3, ℤ) →* SL(3, ℤ) where
  toFun M := ⟨tauMat M, tauMat_det M⟩
  map_one' := by
    apply Subtype.ext
    simp [tauMat, Wm_mul_Wm]
  map_mul' M N := by
    apply Subtype.ext
    exact tauMat_mul M N

theorem tau_coe (M : SL(3, ℤ)) : ((tau M : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = Wm * ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ)ᵀ * Wm := rfl

theorem tau_apply (M : SL(3, ℤ)) (i j : Fin 3) :
    ((tau M : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) i j = ((M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) j.rev i.rev := by
  rw [tau_coe]
  fin_cases i <;> fin_cases j <;> simp [Wm, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, Matrix.vecMul, dotProduct]

theorem tau_tau (M : SL(3, ℤ)) : tau (tau M) = M := by
  apply Subtype.ext
  rw [tau_coe (tau M)]
  have h1 : (((tau M)⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = ((tau M⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) := by
    rw [map_inv]
  rw [h1, tau_coe, inv_inv]
  have h2 : (Wm * (M : Matrix (Fin 3) (Fin 3) ℤ)ᵀ * Wm)ᵀ = Wm * (M : Matrix (Fin 3) (Fin 3) ℤ) * Wm := by
    simp [Matrix.transpose_mul, Wm_transpose, Matrix.mul_assoc]
  rw [h2]
  calc Wm * (Wm * (M : Matrix (Fin 3) (Fin 3) ℤ) * Wm) * Wm = (Wm * Wm) * (M : Matrix (Fin 3) (Fin 3) ℤ) * (Wm * Wm) := by
        simp only [Matrix.mul_assoc]
    _ = M := by rw [Wm_mul_Wm]; simp

/-- `tau` preserves `Γ(6)`. -/
theorem tau_mem_gammaN {M : SL(3, ℤ)} (hM : M ∈ gammaN 6) : tau M ∈ gammaN 6 := by
  rw [mem_gammaN]
  have h := mem_gammaN.1 (Subgroup.inv_mem _ hM)
  intro i j
  rw [tau_apply]
  have := h j.rev i.rev
  have e : (1 : Matrix (Fin 3) (Fin 3) ℤ) j.rev i.rev = (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
    fin_cases i <;> fin_cases j <;> simp [Fin.rev]
  rwa [e] at this

theorem tau_mem_borelStab {M : SL(3, ℤ)} (hM : M ∈ borelStab) : tau M ∈ borelStab := by
  have h := Subgroup.inv_mem _ hM
  refine ⟨?_, ?_, ?_⟩
  · rw [tau_apply]; exact h.2.2
  · rw [tau_apply]; exact h.2.1
  · rw [tau_apply]; exact h.1

theorem tau_mem_lineBorel_of_planeBorel {M : SL(3, ℤ)} (hM : M ∈ planeBorel) : tau M ∈ lineBorel := by
  have h := Subgroup.inv_mem _ hM
  refine ⟨?_, ?_⟩
  · rw [tau_apply]; exact h.2
  · rw [tau_apply]; exact h.1

theorem tau_mem_planeBorel_of_lineBorel {M : SL(3, ℤ)} (hM : M ∈ lineBorel) : tau M ∈ planeBorel := by
  have h := Subgroup.inv_mem _ hM
  refine ⟨?_, ?_⟩
  · rw [tau_apply]; exact h.2
  · rw [tau_apply]; exact h.1

theorem tau_mem_lineStab_of_planeStab {M : SL(3, ℤ)} (hM : M ∈ planeStab) : tau M ∈ lineStab := by
  have h := Subgroup.inv_mem _ hM
  refine ⟨?_, ?_, ?_⟩
  · rw [tau_apply]; exact h.2.2
  · rw [tau_apply]; exact h.2.1
  · rw [tau_apply]; exact h.1

end TernaryPeriodPolynomials.Argument.GammaNStokes
