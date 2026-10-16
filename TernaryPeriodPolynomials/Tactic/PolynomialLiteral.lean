module

public import Mathlib.Algebra.MvPolynomial.Basic
public meta import Lean.Elab.Term
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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

public meta section


/-!
# Typed polynomial literals

Large explicit polynomials in the variables `X 0, X 1, X 2` elaborate slowly when the type of every
leaf `X i` and every numeral exponent is left to unification: the elaborator keeps one pending
instance problem per arithmetic operation. `poly_literal% T p` elaborates exactly the same term as
`p` in a context of expected type `T`, but supplies the missing type information explicitly: each
`X i` is ascribed the type `T`, each numeral exponent the type `ℕ`, and the outermost `+` or `-` is
elaborated with result type `T` (as the expected type would make it). Only type ascriptions are
inserted, so the elaborated term is unchanged.
-/

open Lean

namespace TernaryPeriodPolynomials.Argument.PolynomialLiteral

/-- Ascribe the type `T` to every `X i` and the type `ℕ` to every numeral exponent inside `stx`. -/
partial def ascribeLeaves (T : Term) (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `($x:ident $n:num) =>
    if x.getId == `X then `(($x $n : $T)) else return stx
  | `($a ^ $n:num) => do
    let a' ← ascribeLeaves T a
    `($(⟨a'⟩) ^ ($n : ℕ))
  | _ =>
    match stx with
    | .node info k args => return .node info k (← args.mapM (ascribeLeaves T))
    | _ => return stx

/-- Ascribe the leaves of the literal `stx` and give its outermost sum or difference the result
type `T`. -/
partial def ascribe (T : Term) (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(($e)) => ascribe T e
  | `($a + $b) =>
    `(@HAdd.hAdd _ _ $T _ $(⟨← ascribeLeaves T a⟩) $(⟨← ascribeLeaves T b⟩))
  | `($a - $b) =>
    `(@HSub.hSub _ _ $T _ $(⟨← ascribeLeaves T a⟩) $(⟨← ascribeLeaves T b⟩))
  | _ => ascribeLeaves T stx

/-- `poly_literal% T p` is the polynomial literal `p` of expected type `T`, elaborated with every
variable `X i` of type `T`, every numeral exponent in `ℕ`, and its outermost `+`/`-` of result type
`T`. -/
syntax (name := polyLiteral) "poly_literal% " term:max term:max : term

macro_rules
  | `(poly_literal% $T $p) => ascribe T p

end TernaryPeriodPolynomials.Argument.PolynomialLiteral
