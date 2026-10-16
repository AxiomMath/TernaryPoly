module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.GL3

@[expose] public section


/-!
# Block embedding `GL₂ → GL₃` on finite adeles (for the generalised local integral)

`blk3 M = diag(M, 1)` with `M` in the upper-left `2 × 2` corner. On finite adeles, `blkGL g`
is the `GL₃(𝔸_f)` element with `GL₂`-block `g`. Its local compatibility with `ι_v` and its
commutation with `ι_v(K)` for `g` trivial at `v` are the two facts used to move the integral
local factor past a base point `g_f`.

Formalized by Claude Haiku 5.5.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG

/-- `diag(M, 1)`: the `2 × 2` block `M` in the upper-left corner, `1` in the lower-right. -/
def blk3 {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

theorem blk3_mul {R : Type*} [Ring R] (M N : Matrix (Fin 2) (Fin 2) R) :
    blk3 (M * N) = blk3 M * blk3 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blk3_one {R : Type*} [Ring R] : blk3 (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk3]

theorem blk3_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (M : Matrix (Fin 2) (Fin 2) R) :
    (blk3 M).map f = blk3 (M.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk3]

/-- The `GL₃` block embedding of a finite-adelic `GL₂` element. -/
def blkGL (g : GeneralLinearGroup (Fin 2) FiniteAdeles) : GeneralLinearGroup (Fin 3) FiniteAdeles :=
  ⟨blk3 g.val, blk3 g⁻¹.val,
    by rw [← blk3_mul, Units.mul_inv, blk3_one],
    by rw [← blk3_mul, Units.inv_mul, blk3_one]⟩

theorem blkGL_val (g : GeneralLinearGroup (Fin 2) FiniteAdeles) : (blkGL g).val = blk3 g.val :=
  rfl

theorem blkGL_mul (g h : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    blkGL (g * h) = blkGL g * blkGL h :=
  Units.ext (blk3_mul g.val h.val)

theorem blkGL_one : blkGL (1 : GeneralLinearGroup (Fin 2) FiniteAdeles) = 1 :=
  Units.ext blk3_one

/-- The block embedding lies in the plane parabolic (bottom row `(0, 0, 1)`). -/
theorem blkGL_mem_plane (g : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    blkGL g ∈ planeParabolic FiniteAdeles :=
  ⟨rfl, rfl⟩

/-- The `GL₂` block of `blkGL g` is `g`. -/
theorem planeBlockGL_blkGL (g : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (h : blkGL g ∈ planeParabolic FiniteAdeles) :
    planeBlockGL (blkGL g) h = g := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Local compatibility -/

/-- The `GL₃` block embedding of a local `GL₂` element. -/
def blkLocGL (v : FinitePlace) (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ) :=
  ⟨blk3 A.val, blk3 A⁻¹.val,
    by rw [← blk3_mul, Units.mul_inv, blk3_one],
    by rw [← blk3_mul, Units.inv_mul, blk3_one]⟩

/-- `ι_v(1)` on the diagonal is `1`. -/
theorem ιEntry3_one_diag (v : FinitePlace) (i : Fin 3) : ιEntry3 v 1 i i = 1 := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  show finiteEvaluation w (ιEntry3 v 1 i i) = finiteEvaluation w 1
  by_cases hw : w = v
  · subst hw
    rw [eval_ιEntry3_self, map_one]
  · rw [eval_ιEntry3_ne v w hw, map_one, Matrix.one_apply_eq]

/-- `blk3` of an `ι_v`-image is the `ι_v`-image of the `GL₃` block. -/
theorem blk3_ιMat (v : FinitePlace) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    blk3 (ιMat v M) = ιMat3 v (blk3 M) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact (ιEntry3_castSucc v (M 0 0) 0 0).symm
  · exact (ιEntry3_castSucc v (M 0 1) 0 1).symm
  · show (0 : FiniteAdeles) = ιEntry3 v 0 0 2
    exact (ιEntry3_zero v (by decide)).symm
  · exact (ιEntry3_castSucc v (M 1 0) 1 0).symm
  · exact (ιEntry3_castSucc v (M 1 1) 1 1).symm
  · show (0 : FiniteAdeles) = ιEntry3 v 0 1 2
    exact (ιEntry3_zero v (by decide)).symm
  · show (0 : FiniteAdeles) = ιEntry3 v 0 2 0
    exact (ιEntry3_zero v (by decide)).symm
  · show (0 : FiniteAdeles) = ιEntry3 v 0 2 1
    exact (ιEntry3_zero v (by decide)).symm
  · show (1 : FiniteAdeles) = ιEntry3 v 1 2 2
    exact (ιEntry3_one_diag v 2).symm

/-- **Local compatibility.** `blkGL (ι_v A) = ι_v (blk A)` in `GL₃`. -/
theorem blkGL_ιGL (v : FinitePlace) (A : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    blkGL (ιGL v A) = ιGL3 v (blkLocGL v A) :=
  Units.ext (blk3_ιMat v A.val)

/-! ## Commutation with a local element, for a base point trivial at `v` -/

theorem evM3_blk3 (w : FinitePlace) (M : Matrix (Fin 2) (Fin 2) FiniteAdeles) :
    evM3 w (blk3 M) = blk3 (M.map (finiteEvaluation w)) := by
  unfold evM3
  exact blk3_map (finiteEvaluation w) M

/-- A `GL₃`-local element commutes with a `GL₂`-block that is trivial at `v`. -/
theorem ιMat3_blk3_comm (v : FinitePlace) (K : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    (G : Matrix (Fin 2) (Fin 2) FiniteAdeles)
    (hG : ∀ i j, finiteEvaluation v (G i j) = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    ιMat3 v K * blk3 G = blk3 G * ιMat3 v K := by
  apply ext_of_evM3
  intro w
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) FiniteAdeles,
      evM3 w (X * Y) = evM3 w X * evM3 w Y := fun X Y => Matrix.map_mul
  rw [hmul, hmul, evM3_blk3]
  by_cases hw : w = v
  · subst hw
    have h1 : G.map (finiteEvaluation w) = 1 :=
      Matrix.ext fun i j => by rw [Matrix.map_apply]; exact hG i j
    rw [evM3_ιMat3_self, h1, blk3_one, Matrix.mul_one, Matrix.one_mul]
  · rw [evM3_ιMat3_ne v w hw, Matrix.one_mul, Matrix.mul_one]

/-- **Commutation.** For `g` trivial at `v`, `ι_v(K)` commutes with `blkGL g`. -/
theorem ιGL3_blkGL_comm (v : FinitePlace) (K : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ))
    (g : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hg : ∀ i j, finiteEvaluation v (g.val i j) = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    ιGL3 v K * blkGL g = blkGL g * ιGL3 v K :=
  Units.ext (ιMat3_blk3_comm v K.val g.val hg)

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG

end
