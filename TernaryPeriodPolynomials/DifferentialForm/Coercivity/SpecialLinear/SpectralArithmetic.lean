module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Control.Basic
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


/-! Arithmetic in the proposed Casimir spectral calculation.
No statement in this file supplies the representation-theoretic spectral
hypotheses or asserts a bound for the actual algebraic Hodge operator. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

/-- The scalar from Saper's formula with trace normalization and proposed spin labels. -/
def casimirScalar (n l m j : ℝ) : ℝ :=
  2 * n * (n + 3) / 3 - m * (m + 1) / 4 + l * (l + 1) / 4 - j * (j + 1) / 4

theorem casimirScalar_lower_bound {n l m j : ℝ}
    (hn : 0 ≤ n) (hl : 0 ≤ l) (hl3 : l ≤ 3) (hm : 0 ≤ m)
    (hmn : m ≤ n) (hj : 0 ≤ j) (hjml : j ≤ m + l) :
    n ^ 2 / 6 ≤ casimirScalar n l m j := by
  have hmquad : m * (m + 1) ≤ n * (n + 1) := by nlinarith [mul_nonneg (show 0 ≤ n-m by linarith) (show 0 ≤ n+m+1 by linarith)]
  have hjquad : j * (j + 1) ≤ (n + l) * (n + l + 1) := by
    have hjn : j ≤ n + l := by linarith
    nlinarith [mul_nonneg (show 0 ≤ n+l-j by linarith) (show 0 ≤ n+l+j+1 by linarith)]
  have hn3 : 0 ≤ n * (3-l) := mul_nonneg hn (by linarith)
  unfold casimirScalar
  nlinarith

theorem killingNormalized_casimirScalar_pos {n l m j : ℝ}
    (hn : 0 < n) (hl : 0 ≤ l) (hl3 : l ≤ 3) (hm : 0 ≤ m)
    (hmn : m ≤ n) (hj : 0 ≤ j) (hjml : j ≤ m + l) :
    0 < casimirScalar n l m j / 6 := by
  have h := casimirScalar_lower_bound hn.le hl hl3 hm hmn hj hjml
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
  linarith

end TernaryPoly.SL3PolynomialCoercivity
