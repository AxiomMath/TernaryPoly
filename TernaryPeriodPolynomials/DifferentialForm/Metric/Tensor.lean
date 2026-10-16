module

public import TernaryPeriodPolynomials.DifferentialForm.Metric.Matrix
public import Mathlib.LinearAlgebra.Multilinear.Basic

@[expose] public section


/-! Tensor powers of inverse Gram matrices in every finite exterior degree. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix
open scoped Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix on ordered k-tuples. Restricting its contraction to alternating maps gives
an exterior metric after division by k factorial. -/
def tensorMatrix (k : ℕ) (A : Matrix ι ι ℝ) :
    Matrix (Fin k → ι) (Fin k → ι) ℝ := fun I J => ∏ r, A (I r) (J r)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem tensorMatrix_transpose (k : ℕ) (A : Matrix ι ι ℝ) :
    tensorMatrix k A.transpose = (tensorMatrix k A).transpose := rfl

omit [DecidableEq ι] in
theorem tensorMatrix_mul (k : ℕ) (A D : Matrix ι ι ℝ) :
    tensorMatrix k (A * D) = tensorMatrix k A * tensorMatrix k D := by
  ext I J
  simp only [tensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum _

omit [Fintype ι] in
@[simp] theorem tensorMatrix_one (k : ℕ) : tensorMatrix k (1 : Matrix ι ι ℝ) = 1 := by
  ext I J
  by_cases h : I = J
  · simp [tensorMatrix, Matrix.one_apply, h]
  · have hex : ∃ r, I r ≠ J r := Function.ne_iff.mp h
    obtain ⟨r, hr⟩ := hex
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (Matrix.one_apply_ne hr)

theorem tensorMatrix_posDef (k : ℕ) (H : Matrix ι ι ℝ) (hH : H.PosDef) :
    (tensorMatrix k H).PosDef := by
  induction k with
  | zero =>
      have he : tensorMatrix 0 H = 1 := by
        ext I J
        simp [tensorMatrix, Matrix.one_apply, Subsingleton.elim I J]
      rw [he]
      exact Matrix.PosDef.one
  | succ k ih =>
      let e : (Fin (k + 1) → ι) → ι × (Fin k → ι) := fun I => (I 0, fun r => I r.succ)
      have hi : Function.Injective e := by
        intro I J h
        have h0 := congrArg Prod.fst h
        have hs := congrArg Prod.snd h
        funext r
        refine Fin.cases h0 (fun r => congrFun hs r) r
      have he : tensorMatrix (k + 1) H = (H ⊗ₖ tensorMatrix k H).submatrix e e := by
        ext I J
        simp [tensorMatrix, Fin.prod_univ_succ, e]
      rw [he]
      exact (hH.kronecker ih).submatrix hi

end TernaryPoly.PolynomialFormMetric
