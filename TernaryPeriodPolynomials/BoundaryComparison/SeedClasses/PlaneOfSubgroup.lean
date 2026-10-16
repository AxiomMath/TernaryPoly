module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneGroup

@[expose] public section


/-!
# Plane parabolic groups as subgroups of `GL₃(ℝ)`

A subgroup `Γ ⊂ GL₃(ℝ)` of determinant-one matrices with last row `(0, 0, 1)` is a `PlaneData`
group: `g = [[λ_g, w_g], [0, 1]]`. This is the shape of the paper's `Γ_P` (plane parabolic of
a congruence subgroup of `SL₃(ℤ)`).

Paper: Appendix C (`Γ_P`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3

/-- The upper-left `2 × 2` block of a `3 × 3` matrix. -/
def blockA (g : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => g i.castSucc j.castSucc

/-- The upper-right column of a `3 × 3` matrix. -/
def blockW (g : Matrix (Fin 3) (Fin 3) ℝ) : Fin 2 → ℝ := fun i => g i.castSucc 2

/-- The shape condition: last row `(0, 0, 1)`. -/
def IsPlaneShape (g : Matrix (Fin 3) (Fin 3) ℝ) : Prop := g 2 0 = 0 ∧ g 2 1 = 0 ∧ g 2 2 = 1

theorem eq_parabolicMatrix {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsPlaneShape g) :
    g = parabolicMatrix (blockA g) (blockW g) := by
  obtain ⟨h0, h1, h2⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parabolicMatrix, blockA, blockW, h0, h1, h2]

theorem isPlaneShape_parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    IsPlaneShape (parabolicMatrix A w) := by
  simp [IsPlaneShape, parabolicMatrix]

theorem parabolicMatrix_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) (w v : Fin 2 → ℝ) :
    parabolicMatrix A w * parabolicMatrix B v = parabolicMatrix (A * B) (w + A.mulVec v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem blockA_parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    blockA (parabolicMatrix A w) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parabolicMatrix, blockA]

theorem blockW_parabolicMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    blockW (parabolicMatrix A w) = w := by
  ext i
  fin_cases i <;> simp [parabolicMatrix, blockW]

theorem blockA_one : blockA (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockA]

theorem blockA_mul {g h : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsPlaneShape g) (hh : IsPlaneShape h) :
    blockA (g * h) = blockA g * blockA h := by
  rw [eq_parabolicMatrix hg, eq_parabolicMatrix hh, parabolicMatrix_mul, blockA_parabolicMatrix,
    blockA_parabolicMatrix, blockA_parabolicMatrix]

theorem blockW_mul {g h : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsPlaneShape g) (hh : IsPlaneShape h) :
    blockW (g * h) = blockW g + (blockA g).mulVec (blockW h) := by
  rw [eq_parabolicMatrix hg, eq_parabolicMatrix hh, parabolicMatrix_mul, blockW_parabolicMatrix,
    blockW_parabolicMatrix, blockA_parabolicMatrix, blockW_parabolicMatrix]

theorem det_blockA {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : IsPlaneShape g) :
    (blockA g).det = g.det := by
  conv_rhs => rw [eq_parabolicMatrix hg, det_parabolicMatrix]

/-- **A subgroup of `GL₃(ℝ)` of determinant-one matrices `[[λ, w], [0, 1]]` is a `PlaneData`.** -/
def PlaneData.ofSubgroup (Γ : Subgroup (GL (Fin 3) ℝ))
    (hshape : ∀ g ∈ Γ, IsPlaneShape (g : Matrix (Fin 3) (Fin 3) ℝ))
    (hdet : ∀ g ∈ Γ, (g : Matrix (Fin 3) (Fin 3) ℝ).det = 1) : PlaneData Γ where
  lam :=
    { toFun := fun g => Matrix.GeneralLinearGroup.mkOfDetNeZero (blockA (g.1 : Matrix _ _ ℝ)) (by
        rw [det_blockA (hshape g.1 g.2), hdet g.1 g.2]; exact one_ne_zero)
      map_one' := by
        apply Units.ext
        change blockA (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1
        exact blockA_one
      map_mul' := fun g h => by
        apply Units.ext
        exact blockA_mul (hshape g.1 g.2) (hshape h.1 h.2) }
  w := fun g => blockW (g.1 : Matrix _ _ ℝ)
  det_one := fun g => by
    apply Units.ext
    change (blockA (g.1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 1
    rw [det_blockA (hshape g.1 g.2), hdet g.1 g.2]
  w_mul := fun g h => blockW_mul (hshape g.1 g.2) (hshape h.1 h.2)

theorem PlaneData.ofSubgroup_plm (Γ : Subgroup (GL (Fin 3) ℝ))
    (hshape : ∀ g ∈ Γ, IsPlaneShape (g : Matrix (Fin 3) (Fin 3) ℝ))
    (hdet : ∀ g ∈ Γ, (g : Matrix (Fin 3) (Fin 3) ℝ).det = 1) (g : Γ) :
    (PlaneData.ofSubgroup Γ hshape hdet).plm g = (g.1 : Matrix (Fin 3) (Fin 3) ℝ) :=
  (eq_parabolicMatrix (hshape g.1 g.2)).symm

/-- The embedding `sigma` of `ofSubgroup Γ` into `GL₃(ℝ)` is the inclusion of `Γ`. -/
theorem PlaneData.ofSubgroup_sigma (Γ : Subgroup (GL (Fin 3) ℝ))
    (hshape : ∀ g ∈ Γ, IsPlaneShape (g : Matrix (Fin 3) (Fin 3) ℝ))
    (hdet : ∀ g ∈ Γ, (g : Matrix (Fin 3) (Fin 3) ℝ).det = 1) (g : Γ) :
    (PlaneData.ofSubgroup Γ hshape hdet).sigma g = g.1 :=
  Units.ext (PlaneData.ofSubgroup_plm Γ hshape hdet g)

end TernaryPeriodPolynomials.Argument.SeedC3
