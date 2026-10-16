module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Finsupp.Antidiagonal
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


namespace TernaryPoly

/-- A polynomial over a characteristic-zero domain has no nonzero additive period. -/
theorem polynomial_eq_constant_of_translation {R : Type*}
    [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (a : R) (ha : a ≠ 0)
    (hp : p.comp (Polynomial.X + Polynomial.C a) = p) :
    p = Polynomial.C (p.coeff 0) := by
  have heval (x : R) : p.eval (x + a) = p.eval x := by
    simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C] using congrArg (Polynomial.eval x) hp
  have hnat (n : ℕ) : p.eval ((n : R) * a) = p.eval 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, heval, ih]
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => (n : R) * a) := by
    intro m n h
    exact Nat.cast_injective (mul_right_cancel₀ ha h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_C, ← Polynomial.coeff_zero_eq_eval_zero] using hnat n

end TernaryPoly
