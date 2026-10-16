module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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

/-! The trace metric on matrix rays: centering and its conjugation identities. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

/-- Remove the scalar direction of a logarithmic tangent matrix. -/
def center (A : Mat) : Mat := A - (A.trace / 3) • 1

@[simp] theorem center_trace (A : Mat) : (center A).trace = 0 := by
  simp [center]

@[simp] theorem center_add (A B : Mat) : center (A + B) = center A + center B := by
  simp only [center, trace_add, add_div, add_smul]
  module

@[simp] theorem center_smul (c : ℝ) (A : Mat) : center (c • A) = c • center A := by
  simp only [center, trace_smul, smul_eq_mul, smul_sub, smul_smul]
  congr 1
  ring_nf

@[simp] theorem center_scalar (c : ℝ) : center (c • (1 : Mat)) = 0 := by
  simp [center]

@[simp] theorem center_add_scalar (A : Mat) (c : ℝ) : center (A + c • 1) = center A := by
  rw [center_add, center_scalar, add_zero]

@[simp] theorem center_eq_zero (A : Mat) : center A = 0 ↔ ∃ c : ℝ, A = c • 1 := by
  constructor
  · intro h
    exact ⟨A.trace / 3, sub_eq_zero.mp h⟩
  · rintro ⟨c, rfl⟩
    exact center_scalar c

/-- Conjugation leaves the trace unchanged. -/
theorem trace_conjugate (g : Matˣ) (A : Mat) :
    ((g : Mat) * A * (↑g⁻¹ : Mat)).trace = A.trace := by
  rw [trace_mul_cycle]
  simp

/-- Scalar removal commutes with every invertible change of frame. -/
theorem center_conjugate (g : Matˣ) (A : Mat) :
    center ((g : Mat) * A * (↑g⁻¹ : Mat)) = (g : Mat) * center A * (↑g⁻¹ : Mat) := by
  rw [center, trace_conjugate, center, mul_sub, sub_mul]
  simp

/-- The projective trace pairing on logarithmic tangent matrices. -/
def tracePair (A B : Mat) : ℝ := (center A * center B).trace

theorem tracePair_comm (A B : Mat) : tracePair A B = tracePair B A :=
  trace_mul_comm _ _

theorem tracePair_formula (A B : Mat) :
    tracePair A B = (A * B).trace - A.trace * B.trace / 3 := by
  simp [tracePair, center, sub_mul, mul_sub]
  ring_nf

theorem tracePair_conjugate (g : Matˣ) (A B : Mat) :
    tracePair ((g : Mat) * A * (↑g⁻¹ : Mat)) ((g : Mat) * B * (↑g⁻¹ : Mat)) =
      tracePair A B := by
  rw [tracePair, center_conjugate, center_conjugate]
  have h : (g : Mat) * center A * (↑g⁻¹ : Mat) * ((g : Mat) * center B * (↑g⁻¹ : Mat)) =
      (g : Mat) * (center A * center B) * (↑g⁻¹ : Mat) := by
    simp [mul_assoc]
  rw [h, trace_conjugate]
  rfl

end TernaryPoly.SymmetricSpaceTraceMetric
