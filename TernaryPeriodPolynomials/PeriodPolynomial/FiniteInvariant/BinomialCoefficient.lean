module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support
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
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

/-- A shifted binomial coefficient in two literal polynomial variables. -/
theorem coeff_Y_mul_add_pow (a b : ℕ) :
    ((X 1)^a*(X 0+X 1 : MvPolynomial (Fin 2) ℚ)^b).coeff (Finsupp.single 0 a+Finsupp.single 1 b) = (b.choose a : ℚ) := by
  rw [X_pow_eq_monomial,coeff_monomial_mul']
  by_cases hi : a≤b
  · have hm : Finsupp.single (1 : Fin 2) a ≤ Finsupp.single 0 a+Finsupp.single 1 b := by
      intro j
      fin_cases j <;> simp [hi]
    rw [ite_eq_left hm,one_mul,coeff_add_pow]
    simp only [Finsupp.tsub_apply,Finsupp.add_apply,Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2)≠1),
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2)≠0),Nat.sub_zero,add_zero,zero_add]
    rw [ite_eq_left]
    exact Finset.mem_antidiagonal.mpr (by omega)
  · have hm : ¬Finsupp.single (1 : Fin 2) a ≤ Finsupp.single 0 a+Finsupp.single 1 b := by
      intro h
      have h1 := h 1
      apply hi
      simpa using h1
    rw [ite_eq_right hm,Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero]

end TernaryPoly.BinaryFiniteInvariant
