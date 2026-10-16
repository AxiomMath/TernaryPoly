module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.RhoAction
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.CoefSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Boundary

@[expose] public section


/-!
# Plane parabolic groups acting on the face `e(P)`

A group `G` with a Levi block `λ : G → GL₂(ℝ)` of determinant one and a radical part
`w : G → ℝ²` with the semidirect-product law `w(gh) = w(g) + λ(g) w(h)` is the group `Γ_P` of the
paper's plane parabolic (e.g. `Γ_P ⊂ SL₃(ℤ)`, the elements `[[λ, w], [0, 1]]`). It acts on
the face `e(P) = N_P × ℍ` with coordinates `(u₁, u₂, x, y)` and on the coefficients
`E_n = Sym^n((ℂ³)*) ⊗ det⁻¹` through the matrix `[[λ, w], [0, 1]]`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- The abstract plane parabolic group data. -/
structure PlaneData (G : Type) [Group G] where
  lam : G →* GL (Fin 2) ℝ
  w : G → (Fin 2 → ℝ)
  det_one : ∀ g, (lam g).det = 1
  w_mul : ∀ g h, w (g * h) = w g + (lam g : Matrix (Fin 2) (Fin 2) ℝ).mulVec (w h)

namespace PlaneData

variable {G : Type} [Group G] (D : PlaneData G)

theorem w_one : D.w 1 = 0 := by
  have h := D.w_mul 1 1
  simp only [mul_one, map_one, Units.val_one, Matrix.one_mulVec] at h
  -- w 1 = w 1 + w 1
  have : D.w 1 + D.w 1 = D.w 1 + 0 := by rw [← h, add_zero]
  exact (add_left_cancel this)

/-- The `3 × 3` matrix `[[λ(g), w(g)], [0, 1]]`. -/
def plm (g : G) : Matrix (Fin 3) (Fin 3) ℝ :=
  parabolicMatrix ((D.lam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) (D.w g)

theorem plm_mul (g h : G) : D.plm (g * h) = D.plm g * D.plm h := by
  ext i j
  simp only [plm, map_mul, Units.val_mul, D.w_mul]
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem plm_one : D.plm 1 = 1 := by
  ext i j
  simp only [plm, map_one, Units.val_one, D.w_one]
  fin_cases i <;> fin_cases j <;> simp [parabolicMatrix]

theorem det_plm (g : G) : (D.plm g).det = 1 := by
  rw [plm, det_parabolicMatrix]
  have := D.det_one g
  simpa [Matrix.GeneralLinearGroup.det] using congrArg Units.val this

/-- The embedding into `GL₃(ℝ)`. -/
def sigma : G →* GL (Fin 3) ℝ where
  toFun g := ⟨D.plm g, D.plm g⁻¹, by rw [← D.plm_mul, mul_inv_cancel, D.plm_one],
    by rw [← D.plm_mul, inv_mul_cancel, D.plm_one]⟩
  map_one' := by
    apply Units.ext
    exact D.plm_one
  map_mul' g h := by
    apply Units.ext
    exact D.plm_mul g h

@[simp] theorem sigma_val (g : G) : ((D.sigma g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
    D.plm g := rfl

end PlaneData

end TernaryPeriodPolynomials.Argument.SeedC3
