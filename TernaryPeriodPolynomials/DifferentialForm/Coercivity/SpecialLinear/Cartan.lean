module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Concrete Cartan decomposition with the trace normalization of the bilinear form. -/
noncomputable section

namespace TernaryPoly.SL3PolynomialCoercivity

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def traceZero : Submodule ℝ Mat := LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℝ ℝ)

def symmetricTraceZero : Submodule ℝ Mat where
  carrier := {A | A.transpose = A ∧ Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by rintro A B ⟨hA, tA⟩ ⟨hB, tB⟩; simp [hA, hB, tA, tB]
  smul_mem' := by rintro c A ⟨hA, tA⟩; simp [hA, tA]

def skewSymmetric : Submodule ℝ Mat where
  carrier := {A | A.transpose = -A}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change (A + B).transpose = -(A + B)
    rw [Matrix.transpose_add, hA, hB, neg_add]
  smul_mem' := by intro c A hA; simpa using congrArg (c • ·) hA

def symmetricPart (A : Mat) : Mat := (1 / 2 : ℝ) • (A + A.transpose)
def skewPart (A : Mat) : Mat := (1 / 2 : ℝ) • (A - A.transpose)

theorem symmetricPart_transpose (A : Mat) : (symmetricPart A).transpose = symmetricPart A := by
  ext i j
  simp [symmetricPart, Matrix.transpose_apply, add_comm]
  ring

theorem skewPart_transpose (A : Mat) : (skewPart A).transpose = -skewPart A := by
  ext i j
  simp [skewPart, Matrix.transpose_apply]
  ring

theorem skewPart_add_symmetricPart (A : Mat) : skewPart A + symmetricPart A = A := by
  ext i j
  simp [skewPart, symmetricPart]
  ring

theorem skew_trace_zero {A : Mat} (hA : A.transpose = -A) : Matrix.trace A = 0 := by
  have h := congrArg Matrix.trace hA
  simp only [Matrix.trace_transpose, Matrix.trace_neg] at h
  linarith

theorem symmetricPart_trace (A : Mat) : Matrix.trace (symmetricPart A) = Matrix.trace A := by
  simp [symmetricPart]
  ring

theorem cartan_decomposition (A : Mat) (hA : Matrix.trace A = 0) :
    skewPart A ∈ skewSymmetric ∧ symmetricPart A ∈ symmetricTraceZero ∧
      skewPart A + symmetricPart A = A := by
  exact ⟨skewPart_transpose A, ⟨symmetricPart_transpose A, (symmetricPart_trace A).trans hA⟩,
    skewPart_add_symmetricPart A⟩

theorem cartan_intersection {A : Mat} (hk : A ∈ skewSymmetric)
    (hp : A ∈ symmetricTraceZero) : A = 0 := by
  have h : A = -A := hp.1.symm.trans hk
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.neg_apply] at hij
  simpa using (show A i j = 0 by linarith)

theorem symmetric_commutator_skew {A B : Mat} (hA : A.transpose = A)
    (hB : B.transpose = B) : (A * B - B * A) ∈ skewSymmetric := by
  change (A * B - B * A).transpose = -(A * B - B * A)
  simp [hA, hB, neg_sub]

theorem skew_symmetric_commutator_symmetric {A B : Mat} (hA : A.transpose = -A)
    (hB : B.transpose = B) : (A * B - B * A) ∈ symmetricTraceZero := by
  constructor
  · simp [hA, hB, sub_eq_add_neg, add_comm]
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

end TernaryPoly.SL3PolynomialCoercivity
