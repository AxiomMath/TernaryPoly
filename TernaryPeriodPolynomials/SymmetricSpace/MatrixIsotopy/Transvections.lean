module

public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.RealMatrixIsotopy
open Matrix Matrix.SpecialLinearGroup

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual product of two matrix-unit multiples. -/
theorem single_mul_single_eq (i j k l : ι) (a b : ℝ) :
    single i j a * single k l b = if j = k then single i l (a*b) else 0 := by
  split_ifs with h
  · subst k
    exact single_mul_single_same a i j l b
  · exact single_mul_single_of_ne a i j k h b

/-- The actual two-coordinate determinant-one diagonal block is a product of six transvections. -/
theorem diag2n_decompose {i j : ι} (hij : i ≠ j) (a : ℝ) (ha : a ≠ 0) :
    diag2n hij a ha = transvection hij a * transvection hij.symm (-a⁻¹) *
      transvection hij a * transvection hij (-1) * transvection hij.symm 1 * transvection hij (-1) := by
  apply Subtype.ext
  simp only [coe_mul, transvection_coe, mul_add, add_mul, one_mul, mul_one,
    single_mul_single_eq, hij, hij.symm, ite_false, ite_true, add_zero]
  apply Matrix.ext
  intro k l
  by_cases hki : i = k <;> by_cases hkj : j = k <;>
    by_cases hli : i = l <;> by_cases hlj : j = l <;>
    simp_all [diag2n_coe, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.add_apply] <;> grind

/-- Scaling its coefficient gives an actual continuous path from identity to a transvection. -/
def transvectionPath {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Path (1 : SpecialLinearGroup ι ℝ) (transvection hij a) where
  toFun t := transvection hij ((t : ℝ) * a)
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun t : unitInterval => (1 : Matrix ι ι ℝ) + single i j ((t : ℝ) * a))
    apply continuous_matrix
    intro k l
    simp only [Matrix.add_apply, single_apply]
    split_ifs <;> fun_prop
  source' := by simp [transvection_coeff_zero]
  target' := by simp

end TernaryPoly.RealMatrixIsotopy
