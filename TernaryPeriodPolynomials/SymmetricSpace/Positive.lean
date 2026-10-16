module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpacePositive
open Matrix
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

/-- The concrete real rank-three symmetric-space model modulo positive scalar homotheties. -/
def traceOnePositive : Set Mat := {S | S.PosDef ∧ S.trace=1}
abbrev Space := traceOnePositive

/-- Every positive-definite ray has its explicit trace-one representative. -/
def normalize (S : Mat) : Mat := S.trace⁻¹ • S

theorem normalize_mem (S : Mat) (hS : S.PosDef) : normalize S∈traceOnePositive := by
  refine ⟨hS.smul (inv_pos.mpr hS.trace_pos),?_⟩
  rw [normalize,trace_smul,smul_eq_mul,inv_mul_cancel₀ (ne_of_gt hS.trace_pos)]

@[simp] theorem normalize_of_trace_one (S : Mat) (hS : S.trace=1) : normalize S=S := by
  simp [normalize,hS]

theorem normalize_smul (r : ℝ) (hr : r≠0) (S : Mat) : normalize (r • S)=normalize S := by
  rw [normalize,trace_smul,smul_smul,normalize,smul_eq_mul,_root_.mul_inv_rev]
  congr 1
  rw [mul_assoc,inv_mul_cancel₀ hr,mul_one]

/-- The normalized positive cone is nonempty, with the scalar identity as basepoint. -/
theorem traceOnePositive_nonempty : traceOnePositive.Nonempty := by
  exact ⟨normalize 1,normalize_mem 1 (PosDef.one : (1 : Mat).PosDef)⟩

/-- Positivity and trace one form a convex set in the actual real matrix space. -/
theorem traceOnePositive_convex : Convex ℝ traceOnePositive := by
  intro S hS T hT a b ha hb hab
  refine ⟨?_,?_⟩
  · rcases eq_or_lt_of_le ha with h0 | ha
    · have he : b=1 := by linarith
      simp [←h0,he,hT.1]
    rcases eq_or_lt_of_le hb with h0 | hb
    · have he : a=1 := by linarith
      simp [←h0,he,hS.1]
    exact (hS.1.smul ha).add (hT.1.smul hb)
  · rw [trace_add,trace_smul,trace_smul,hS.2,hT.2,smul_eq_mul,smul_eq_mul,mul_one,mul_one]
    exact hab

/-- Contractibility is proved for the concrete matrix model; no arithmetic quotient is assumed. -/
instance : ContractibleSpace Space := traceOnePositive_convex.contractibleSpace traceOnePositive_nonempty

end TernaryPoly.SymmetricSpacePositive
