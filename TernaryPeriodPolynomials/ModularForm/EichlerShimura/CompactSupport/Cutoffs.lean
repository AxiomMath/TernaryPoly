module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
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
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# One-variable cutoffs for the cusp surgery

`chi` is a smooth height cutoff, `0` for `t ≤ 3/2` and `1` for `t ≥ 2`; `eta` is a smooth function
supported in `[-1, 1]` whose integer translates form a partition of unity (`eta_finsum`).

Formalized by Claude Sonnet 5.5.
-/

open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport

/-- The height cutoff: `0` for `t ≤ 3/2`, `1` for `t ≥ 2`. -/
def chi (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 3)

theorem contDiff_chi : ContDiff ℝ ∞ chi :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem chi_eq_zero {t : ℝ} (h : t ≤ 3 / 2) : chi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem chi_eq_one {t : ℝ} (h : 2 ≤ t) : chi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The width cutoff: supported in `[-1, 1]`, with `∑_{j ∈ ℤ} eta (x - j) = 1`. -/
def eta (x : ℝ) : ℝ := Real.smoothTransition (x + 1) * (1 - Real.smoothTransition x)

theorem contDiff_eta : ContDiff ℝ ∞ eta :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub Real.smoothTransition.contDiff)

theorem eta_eq_zero_of_le {x : ℝ} (h : x ≤ -1) : eta x = 0 := by
  rw [eta, Real.smoothTransition.zero_of_nonpos (by linarith : x + 1 ≤ 0), zero_mul]

theorem eta_eq_zero_of_ge {x : ℝ} (h : 1 ≤ x) : eta x = 0 := by
  rw [eta, Real.smoothTransition.one_of_one_le h, sub_self, mul_zero]

theorem abs_lt_of_eta_ne_zero {x : ℝ} (h : eta x ≠ 0) : |x| < 1 := by
  rw [abs_lt]
  constructor
  · by_contra h'
    exact h (eta_eq_zero_of_le (not_lt.mp h'))
  · by_contra h'
    exact h (eta_eq_zero_of_ge (not_lt.mp h'))

theorem eta_finsum (x : ℝ) : ∑ᶠ j : ℤ, eta (x - j) = 1 := by
  set n : ℤ := ⌊x⌋ with hn
  have h1 : (n : ℝ) ≤ x := Int.floor_le x
  have h2 : x < n + 1 := Int.lt_floor_add_one x
  have hsupp : Function.support (fun j : ℤ => eta (x - j)) ⊆ ↑({n, n + 1} : Finset ℤ) := by
    intro j hj
    have := abs_lt_of_eta_ne_zero hj
    rw [abs_lt] at this
    have hj1 : (j : ℝ) < n + 2 := by linarith [this.1]
    have hj2 : (n : ℝ) - 1 < j := by linarith [this.2]
    have hj1' : j < n + 2 := by exact_mod_cast hj1
    have hj2' : n - 1 < j := by exact_mod_cast hj2
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by omega)]
  have e1 : eta (x - n) = 1 - Real.smoothTransition (x - n) := by
    rw [eta, Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  have e2 : eta (x - ((n + 1 : ℤ) : ℝ)) = Real.smoothTransition (x - n) := by
    rw [eta]
    have : x - ((n + 1 : ℤ) : ℝ) + 1 = x - n := by push_cast; ring
    rw [this, Real.smoothTransition.zero_of_nonpos (by push_cast; linarith : x - ((n + 1 : ℤ) : ℝ) ≤ 0),
      sub_zero, mul_one]
  rw [e1, e2]; ring


end TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport
