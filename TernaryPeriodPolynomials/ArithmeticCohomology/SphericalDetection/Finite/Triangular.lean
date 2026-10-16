module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Control.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteTriangular_solve_boundary {M : Type} [AddCommGroup M] [Module ℂ M]
    (size : ℕ) (spaces : Fin (size + 1) → Submodule ℂ M)
    (coefficient : Fin size → ℂ) (operator : Fin size → Module.End ℂ M)
    (target : Fin (size + 1) → M) (boundary : M)
    (boundary_mem : boundary ∈ spaces (Fin.last size))
    (nonzero : ∀ position, coefficient position ≠ 0)
    (stable : ∀ (position : Fin size) value, value ∈ spaces position.succ → operator position value ∈ spaces position.castSucc)
    (target_mem : ∀ position : Fin size, target position.succ ∈ spaces position.castSucc) :
    ∃ solution : Fin (size + 1) → M,
      solution (Fin.last size) = boundary ∧ (∀ position, solution position ∈ spaces position) ∧
      ∀ position : Fin size,
        coefficient position • solution position.castSucc + operator position (solution position.succ) = target position.succ := by
  induction size with
  | zero =>
    refine ⟨fun _ => boundary, rfl, ?_, fun position => Fin.elim0 position⟩
    intro position
    have equality : position = Fin.last 0 := by fin_cases position; rfl
    simpa only [equality] using boundary_mem
  | succ size induction =>
    obtain ⟨tail, tail_last, tail_mem, tail_equation⟩ := induction
      (fun position => spaces position.succ)
      (fun position => coefficient position.succ)
      (fun position => operator position.succ)
      (fun position => target position.succ) boundary_mem
      (fun position => nonzero position.succ)
      (fun position value member => stable position.succ value member)
      (fun position => target_mem position.succ)
    let head := (coefficient 0)⁻¹ • (target 1 - operator 0 (tail 0))
    refine ⟨Fin.cons head tail, tail_last, ?_, ?_⟩
    · intro position
      refine Fin.cases ?_ (fun position => tail_mem position) position
      exact (spaces 0).smul_mem _ ((spaces 0).sub_mem (target_mem 0) (stable 0 (tail 0) (tail_mem 0)))
    · intro position
      refine Fin.cases ?_ (fun position => tail_equation position) position
      change coefficient 0 • head + operator 0 (tail 0) = target 1
      dsimp only [head]
      rw [smul_inv_smul₀ (nonzero 0), sub_add_cancel]

theorem finiteTriangular_solve {M : Type} [AddCommGroup M] [Module ℂ M]
    (size : ℕ) (spaces : Fin (size + 1) → Submodule ℂ M)
    (coefficient : Fin size → ℂ) (operator : Fin size → Module.End ℂ M)
    (target : Fin (size + 1) → M)
    (nonzero : ∀ position, coefficient position ≠ 0)
    (stable : ∀ (position : Fin size) value, value ∈ spaces position.succ → operator position value ∈ spaces position.castSucc)
    (target_mem : ∀ position : Fin size, target position.succ ∈ spaces position.castSucc) :
    ∃ solution : Fin (size + 1) → M,
      solution (Fin.last size) = 0 ∧ (∀ position, solution position ∈ spaces position) ∧
      ∀ position : Fin size,
        coefficient position • solution position.castSucc + operator position (solution position.succ) = target position.succ := by
  induction size with
  | zero =>
    refine ⟨fun _ => 0, rfl, fun position => (spaces position).zero_mem, ?_⟩
    intro position
    exact Fin.elim0 position
  | succ size induction =>
    obtain ⟨tail, tail_last, tail_mem, tail_equation⟩ := induction
      (fun position => spaces position.succ)
      (fun position => coefficient position.succ)
      (fun position => operator position.succ)
      (fun position => target position.succ)
      (fun position => nonzero position.succ)
      (fun position value member => stable position.succ value member)
      (fun position => target_mem position.succ)
    let head := (coefficient 0)⁻¹ • (target 1 - operator 0 (tail 0))
    refine ⟨Fin.cons head tail, ?_, ?_, ?_⟩
    · exact tail_last
    · intro position
      refine Fin.cases ?_ (fun position => tail_mem position) position
      exact (spaces 0).smul_mem _ ((spaces 0).sub_mem (target_mem 0) (stable 0 (tail 0) (tail_mem 0)))
    · intro position
      refine Fin.cases ?_ (fun position => tail_equation position) position
      change coefficient 0 • head + operator 0 (tail 0) = target 1
      dsimp only [head]
      rw [smul_inv_smul₀ (nonzero 0), sub_add_cancel]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
