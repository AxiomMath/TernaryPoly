module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Positive matrix contractions with vector-valued coefficients. -/
noncomputable section
namespace TernaryPoly.PolynomialFormMetric
open Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The actual action of a real matrix on a finite family of coefficient vectors. -/
def matrixAction (A : Matrix ι ι ℝ) (v : ι → V) (i : ι) : V := ∑ j, A i j • v j

@[simp] theorem matrixAction_one (v : ι → V) : matrixAction 1 v = v := by
  ext i
  simp [matrixAction, Matrix.one_apply]

omit [DecidableEq ι] in
theorem matrixAction_mul (A D : Matrix ι ι ℝ) (v : ι → V) :
    matrixAction (A * D) v = matrixAction A (matrixAction D v) := by
  ext i
  simp only [matrixAction, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

omit [DecidableEq ι] in
@[simp] theorem matrixAction_zero (A : Matrix ι ι ℝ) : matrixAction A (0 : ι → V) = 0 := by
  ext i
  simp [matrixAction]

theorem matrixAction_injective (A : (Matrix ι ι ℝ)ˣ) :
    Function.Injective (matrixAction (A : Matrix ι ι ℝ) : (ι → V) → (ι → V)) := by
  intro v w h
  have := congrArg (matrixAction (↑A⁻¹ : Matrix ι ι ℝ)) h
  simpa only [← matrixAction_mul, Units.inv_mul, matrixAction_one] using this

/-- Contraction of a matrix with a coefficient bilinear form. -/
def matrixContraction (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : Matrix ι ι ℝ) (v w : ι → V) : ℝ :=
  ∑ i, ∑ j, A i j * B (v i) (w j)

omit [DecidableEq ι] in
theorem matrixContraction_frame (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : Matrix ι ι ℝ)
    (v w : ι → V) :
    matrixContraction B (A * A.transpose) v w =
      ∑ i, B (matrixAction A.transpose v i) (matrixAction A.transpose w i) := by
  simp only [matrixContraction, matrixAction, Matrix.mul_apply, Matrix.transpose_apply,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k, A i k * A j k * B (v i) (w j)) =
        ∑ i, ∑ k, ∑ j, A i k * A j k * B (v i) (w j) := by
      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, A i k * A j k * B (v i) (w j) := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, A i k * A j k * B (v i) (w j) := by
      apply Finset.sum_congr rfl; intro k _; exact Finset.sum_comm
    _ = _ := by congr 1; ext k; congr 1; ext i; congr 1; ext j; ring

/-- An arbitrary positive definite real matrix admits an invertible square root frame. -/
theorem exists_matrix_frame (H : Matrix ι ι ℝ) (hH : H.PosDef) :
    ∃ A : (Matrix ι ι ℝ)ˣ, H = (A : Matrix ι ι ℝ) * (A : Matrix ι ι ℝ).transpose := by
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.posSemidef.nonneg
  have hd : H.det ≠ 0 := isUnit_iff_ne_zero.mp ((H.isUnit_iff_isUnit_det).mp hH.isUnit)
  have hdd : D.det ≠ 0 := by
    intro hz
    apply hd
    rw [hD, det_mul, hz, mul_zero]
  obtain ⟨d, rfl⟩ := (D.isUnit_iff_isUnit_det).mpr (isUnit_iff_ne_zero.mpr hdd)
  refine ⟨star d, ?_⟩
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hD

theorem matrixContraction_nonneg (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ v, 0 ≤ B v v) (H : Matrix ι ι ℝ) (hH : H.PosDef) (v : ι → V) :
    0 ≤ matrixContraction B H v v := by
  obtain ⟨A, rfl⟩ := exists_matrix_frame H hH
  rw [matrixContraction_frame]
  exact Finset.sum_nonneg (fun i _ => hB _)

theorem matrixContraction_positive (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (v : ι → V) (hv : v ≠ 0) : 0 < matrixContraction B H v v := by
  have hn (v : V) : 0 ≤ B v v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact (hB v hz).le
  obtain ⟨A, hA⟩ := exists_matrix_frame H hH
  rw [hA, matrixContraction_frame]
  have ht : matrixAction (A : Matrix ι ι ℝ).transpose v ≠ 0 := by
    intro hz
    apply hv
    apply matrixAction_injective (star A)
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hz
  obtain ⟨i, hi⟩ : ∃ i, matrixAction (A : Matrix ι ι ℝ).transpose v i ≠ 0 := by
    by_contra h
    apply ht
    ext i
    simpa only [Pi.zero_apply] using (not_exists.mp h i |> not_not.mp)
  exact Finset.sum_pos' (fun j _ => hn _) ⟨i, Finset.mem_univ i, hB _ hi⟩

end TernaryPoly.PolynomialFormMetric
