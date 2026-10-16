module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

noncomputable section
namespace TernaryPoly.ProjectiveChartOrientation
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The homogeneous matrix of a literal affine projective chart. -/
def homogeneous (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  fromBlocks A (replicateCol Unit b) (replicateRow Unit c) (of fun _ _ => d)

def denominator (c : ι → ℝ) (d : ℝ) (x : ι → ℝ) : ℝ := c ⬝ᵥ x+d

def numerator (A : Matrix ι ι ℝ) (b x : ι → ℝ) : ι → ℝ := A *ᵥ x+b

/-- The derivative matrix of x ↦ (Ax+b)/(c·x+d), at a nonzero denominator. -/
def jacobian (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ) (x : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => (denominator c d x)⁻¹ * A i j -
    (denominator c d x)⁻¹ ^ 2 * numerator A b x i * c j

/-- Translation of the homogeneous last column preserves the actual determinant. -/
theorem homogeneous_translate_det (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ)
    (x : ι → ℝ) :
    (homogeneous A (numerator A b x) c (denominator c d x)).det =
      (homogeneous A b c d).det := by
  have heq : homogeneous A b c d *
      fromBlocks (1 : Matrix ι ι ℝ) (replicateCol Unit x) 0 1 =
      homogeneous A (numerator A b x) c (denominator c d x) := by
    rw [homogeneous,fromBlocks_multiply]
    apply fromBlocks_inj.mpr
    refine ⟨?_,?_,?_,?_⟩
    · simp
    · ext i j
      simp [numerator,Matrix.mul_apply,Matrix.mulVec,dotProduct,replicateCol_apply]
    · simp
    · ext i j
      simp [denominator,Matrix.mul_apply,dotProduct,replicateRow_apply]
  rw [←heq,det_mul,det_fromBlocks_zero₂₁,det_one,det_one,mul_one,mul_one]

/-- Exact projective Jacobian determinant, without a bounded dimension assumption. -/
theorem jacobian_det (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ) (x : ι → ℝ)
    (ht : denominator c d x ≠ 0) :
    (jacobian A b c d x).det =
      (denominator c d x)⁻¹ ^ (Fintype.card ι+1) * (homogeneous A b c d).det := by
  let t := denominator c d x
  have ht' : t ≠ 0 := ht
  let y := numerator A b x
  let D : Matrix Unit Unit ℝ := of fun _ _ => t
  let : Invertible D :=
    { invOf := of fun _ _ => t⁻¹
      invOf_mul_self := by ext i j; simp [Matrix.mul_apply,D,ht,t]
      mul_invOf_self := by ext i j; simp [Matrix.mul_apply,D,ht,t] }
  have hschur := det_fromBlocks₂₂ A (replicateCol Unit y)
    (replicateRow Unit c) D
  have hmatrix : A-(replicateCol Unit y)*⅟D*(replicateRow Unit c) =
      t • jacobian A b c d x := by
    ext i j
    simp only [Matrix.sub_apply,Matrix.mul_apply,Finset.univ_unique,Finset.sum_singleton,
      Matrix.smul_apply,smul_eq_mul,jacobian,replicateCol_apply,replicateRow_apply]
    change A i j-y i*t⁻¹*c j=t*(t⁻¹*A i j-t⁻¹^2*y i*c j)
    field_simp [ht']
  rw [hmatrix,det_smul] at hschur
  have hd : D.det=t := by simp [D,det_unique]
  rw [hd] at hschur
  have hhom : (fromBlocks A (replicateCol Unit y) (replicateRow Unit c) D).det =
      (homogeneous A b c d).det := homogeneous_translate_det A b c d x
  rw [hhom] at hschur
  change _=t⁻¹^(Fintype.card ι+1)*_
  rw [hschur,pow_succ]
  symm
  calc
    _ = (t⁻¹*t)^Fintype.card ι*(t⁻¹*t)*(jacobian A b c d x).det := by
      rw [mul_pow]
      ring
    _ = _ := by simp [ht']

/-- Positive homogeneous determinant and positive denominator give positive chart orientation. -/
theorem jacobian_det_pos (A : Matrix ι ι ℝ) (b c : ι → ℝ) (d : ℝ) (x : ι → ℝ)
    (ht : 0 < denominator c d x) (hdet : 0 < (homogeneous A b c d).det) :
    0 < (jacobian A b c d x).det := by
  rw [jacobian_det A b c d x (ne_of_gt ht)]
  exact mul_pos (pow_pos (inv_pos.mpr ht) _) hdet

end TernaryPoly.ProjectiveChartOrientation
