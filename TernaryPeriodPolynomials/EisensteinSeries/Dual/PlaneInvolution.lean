module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Jmath
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Setup

@[expose] public section


open scoped MatrixGroups ContDiff
open Matrix

/-!
# The involution of the symmetric space and of its plane coordinates

Formalized by Claude Sonnet 5.5.

On Gram matrices of `𝒳 = SL₃(ℝ)/SO(3)` (the model of `ConvergenceC4`, `Ω ≅ 𝒳` through
`planeGram`/`planePoint`) the involution induced by `g ↦ J (g⁻¹)ᵗ J` is `G ↦ J G⁻¹ J = rt (G⁻¹)` (`jGram`); in the plane
coordinates it is `jPlane`.  It preserves `Ω`, is smooth there, and is equivariant along `ȷ` (`jPlane_equivariant`:
`ȷ̃(g · p) = ȷ(g) · ȷ̃(p)`), because `ȷ(g) = rt (g⁻¹)` (`realMat_jmath`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.GammaNFaces

theorem rt_transpose {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) : (rt M)ᵀ = rt Mᵀ := rfl

theorem rt_eq_submatrix {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) :
    rt M = Mᵀ.submatrix Fin.rev Fin.rev := rfl

/-- `rt` commutes with the matrix inverse of an invertible real matrix. -/
theorem rt_inv_real (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det) : rt M⁻¹ = (rt M)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← rt_mul, Matrix.nonsing_inv_mul _ hM, rt_one]

/-- The involution of Gram matrices `G ↦ J G⁻¹ J = rt (G⁻¹)`. -/
def jGram (G : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := rt G⁻¹

theorem isGram_jGram {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : IsGram G) : IsGram (jGram G) := by
  refine ⟨?_, ?_⟩
  · have h := (hG.1.inv).transpose.submatrix (e := Fin.rev) Fin.rev_injective
    exact h
  · unfold jGram
    rw [det_rt, Matrix.det_nonsing_inv, hG.2]
    simp

theorem realMat_jmath (A : SL(3, ℤ)) : realMat (jmath A) = rt ((realMat A)⁻¹) := by
  rw [← realMat_inv]
  unfold realMat
  rw [coe_jmath]
  rfl

/-- The involution of the plane coordinates `Ω ≅ 𝒳` induced by `g ↦ J (g⁻¹)ᵗ J`: `G ↦ J G⁻¹ J` on Gram matrices. -/
def jPlane (p : Fin 5 → ℝ) : Fin 5 → ℝ := planePoint (jGram (planeGram p))

theorem planeGram_jPlane {p : Fin 5 → ℝ} (hp : p ∈ Omega) : planeGram (jPlane p) = jGram (planeGram p) :=
  planeGram_planePoint (isGram_jGram (planeGram_isGram hp))

theorem jPlane_mem {p : Fin 5 → ℝ} (hp : p ∈ Omega) : jPlane p ∈ Omega :=
  planePoint_mem (isGram_jGram (planeGram_isGram hp))

/-- **Equivariance of the plane involution**: `ȷ̃(g · p) = ȷ(g) · ȷ̃(p)`. -/
theorem jPlane_equivariant (A : SL(3, ℤ)) {p : Fin 5 → ℝ} (hp : p ∈ Omega) :
    jPlane (planeAct (realMat A) p) = planeAct (realMat (jmath A)) (jPlane p) := by
  have hg : (realMat A).det = 1 := det_realMat A
  have hgu : IsUnit (realMat A).det := by rw [hg]; exact isUnit_one
  have hG := planeGram_isGram hp
  have hGu : IsUnit (planeGram p).det := by rw [hG.2]; exact isUnit_one
  unfold jPlane
  rw [planeGram_planeAct hg hp]
  unfold planeAct
  rw [planeGram_planePoint (isGram_jGram hG), realMat_jmath, rt_transpose]
  congr 1
  unfold jGram
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  rw [← rt_mul, ← rt_mul]

theorem contDiffAt_adj_planeGram {p : Fin 5 → ℝ} (hp : p ∈ Omega) (a b : Fin 3) :
    ContDiffAt ℝ ⊤ (fun y : Fin 5 → ℝ => (planeGram y).adjugate a b) p := by
  have g00 := contDiffAt_planeGram_entry hp 0 0
  have g01 := contDiffAt_planeGram_entry hp 0 1
  have g02 := contDiffAt_planeGram_entry hp 0 2
  have g10 := contDiffAt_planeGram_entry hp 1 0
  have g11 := contDiffAt_planeGram_entry hp 1 1
  have g12 := contDiffAt_planeGram_entry hp 1 2
  have g20 := contDiffAt_planeGram_entry hp 2 0
  have g21 := contDiffAt_planeGram_entry hp 2 1
  have g22 := contDiffAt_planeGram_entry hp 2 2
  fin_cases a <;> fin_cases b <;> simp [Matrix.adjugate_fin_three] <;> fun_prop

theorem inv_planeGram_eq_adjugate {y : Fin 5 → ℝ} (hy : y ∈ Omega) :
    (planeGram y)⁻¹ = (planeGram y).adjugate := by
  rw [Matrix.inv_def, (planeGram_isGram hy).2]
  simp

theorem contDiffAt_jGram_entry {p : Fin 5 → ℝ} (hp : p ∈ Omega) (i j : Fin 3) :
    ContDiffAt ℝ ⊤ (fun y : Fin 5 → ℝ => jGram (planeGram y) i j) p := by
  refine (contDiffAt_adj_planeGram hp j.rev i.rev).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Omega.mem_nhds hp] with y hy
  unfold jGram
  rw [rt_apply, inv_planeGram_eq_adjugate hy]

theorem contDiffAt_jPlane {p : Fin 5 → ℝ} (hp : p ∈ Omega) : ContDiffAt ℝ ⊤ jPlane p := by
  have hG := isGram_jGram (planeGram_isGram hp)
  exact contDiffAt_planePoint_comp (F := fun y => jGram (planeGram y)) (contDiffAt_jGram_entry hp) hG.s_pos hG.schur_pos

theorem contDiffOn_jPlane : ContDiffOn ℝ ∞ jPlane Omega := fun _ hp =>
  ((contDiffAt_jPlane hp).of_le le_top).contDiffWithinAt

end TernaryPeriodPolynomials.Argument.EisensteinDual
