module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.Choose.Cast
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
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# The weight factor `y ^ (wt / 2)` for an integer rotation weight

Original work by Claude Sonnet 5.5 (AxiomCode).

For an integer weight `wt` and a real `y`, `wtFactor wt y = exp (wt / 2 * log y)`, which equals
`y ^ (wt / 2)` for `0 < y`.  This is the weight-generic replacement of the integer power
`y ^ halfWeight`, valid for odd as well as even weights.
-/

namespace TernaryPeriodPolynomials.EvenLevelThree

/-- The weight factor `y ^ (wt / 2)`, defined through `exp` and `log`. -/
noncomputable def wtFactor (wt : ℤ) (y : ℝ) : ℝ := Real.exp ((wt : ℝ) / 2 * Real.log y)

theorem wtFactor_pos (wt : ℤ) (y : ℝ) : 0 < wtFactor wt y := Real.exp_pos _

theorem wtFactor_ne_zero (wt : ℤ) (y : ℝ) : wtFactor wt y ≠ 0 := (wtFactor_pos wt y).ne'

theorem wtFactor_add (a b : ℤ) (y : ℝ) :
    wtFactor (a + b) y = wtFactor a y * wtFactor b y := by
  unfold wtFactor
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem wtFactor_zero (y : ℝ) : wtFactor 0 y = 1 := by
  unfold wtFactor
  rw [Int.cast_zero, zero_div, zero_mul, Real.exp_zero]

theorem wtFactor_neg (wt : ℤ) (y : ℝ) : wtFactor (-wt) y = (wtFactor wt y)⁻¹ := by
  unfold wtFactor
  rw [← Real.exp_neg]
  congr 1
  push_cast
  ring

theorem wtFactor_sub (a b : ℤ) (y : ℝ) :
    wtFactor (a - b) y = wtFactor a y * (wtFactor b y)⁻¹ := by
  rw [sub_eq_add_neg, wtFactor_add, wtFactor_neg]

theorem wtFactor_one (wt : ℤ) : wtFactor wt 1 = 1 := by
  unfold wtFactor
  rw [Real.log_one, mul_zero, Real.exp_zero]

theorem wtFactor_mul (wt : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    wtFactor wt (a * b) = wtFactor wt a * wtFactor wt b := by
  unfold wtFactor
  rw [Real.log_mul ha.ne' hb.ne', mul_add, Real.exp_add]

theorem wtFactor_inv (wt : ℤ) {y : ℝ} (_hy : 0 < y) :
    wtFactor wt y⁻¹ = (wtFactor wt y)⁻¹ := by
  unfold wtFactor
  rw [Real.log_inv, mul_neg, Real.exp_neg]

theorem wtFactor_div (wt : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    wtFactor wt (a / b) = wtFactor wt a / wtFactor wt b := by
  rw [div_eq_mul_inv, wtFactor_mul wt ha (inv_pos.mpr hb), wtFactor_inv wt hb, div_eq_mul_inv]

theorem wtFactor_eq_rpow (wt : ℤ) {y : ℝ} (hy : 0 < y) :
    wtFactor wt y = y ^ ((wt : ℝ) / 2) := by
  unfold wtFactor
  rw [Real.rpow_def_of_pos hy]
  congr 1
  ring

theorem wtFactor_two {y : ℝ} (hy : 0 < y) : wtFactor 2 y = y := by
  rw [wtFactor_eq_rpow 2 hy]
  have h : ((2 : ℤ) : ℝ) / 2 = 1 := by norm_num
  rw [h, Real.rpow_one]

theorem wtFactor_eq_mul_sub_two (wt : ℤ) {y : ℝ} (hy : 0 < y) :
    wtFactor wt y = wtFactor (wt - 2) y * y := by
  have h := wtFactor_add (wt - 2) 2 y
  rw [sub_add_cancel, wtFactor_two hy] at h
  exact h

theorem wtFactor_even (h : ℤ) {y : ℝ} (hy : 0 < y) : wtFactor (2 * h) y = y ^ h := by
  rw [wtFactor_eq_rpow (2 * h) hy]
  have h2 : ((2 * h : ℤ) : ℝ) / 2 = (h : ℝ) := by
    push_cast
    ring
  rw [h2, Real.rpow_intCast]

theorem wtFactor_eq_sqrt_zpow (wt : ℤ) {y : ℝ} (hy : 0 < y) :
    wtFactor wt y = Real.sqrt y ^ wt := by
  rw [wtFactor_eq_rpow wt hy, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hy.le]
  congr 1
  ring

theorem hasDerivAt_wtFactor (wt : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (wtFactor wt) (((wt : ℝ) / 2) * wtFactor (wt - 2) y) y := by
  have h1 : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.ne'
  have h2 : HasDerivAt (wtFactor wt) (wtFactor wt y * (((wt : ℝ) / 2) * y⁻¹)) y :=
    (h1.const_mul ((wt : ℝ) / 2)).exp
  have hyy : y * y⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
  have h3 : wtFactor wt y * (((wt : ℝ) / 2) * y⁻¹) = ((wt : ℝ) / 2) * wtFactor (wt - 2) y := by
    rw [wtFactor_eq_mul_sub_two wt hy]
    linear_combination (((wt : ℝ) / 2) * wtFactor (wt - 2) y) * hyy
  exact h2.congr_deriv h3

theorem analyticAt_wtFactor (wt : ℤ) {y : ℝ} (hy : 0 < y) : AnalyticAt ℝ (wtFactor wt) y :=
  (analyticAt_const.mul (analyticAt_log hy)).rexp'

theorem wtFactor_continuousAt (wt : ℤ) {y : ℝ} (hy : 0 < y) : ContinuousAt (wtFactor wt) y :=
  (analyticAt_wtFactor wt hy).continuousAt

theorem wtFactor_contDiffAt (wt : ℤ) {y : ℝ} (hy : 0 < y) (m : WithTop ℕ∞) :
    ContDiffAt ℝ m (wtFactor wt) y :=
  (analyticAt_wtFactor wt hy).contDiffAt

theorem tendsto_wtFactor_atTop_of_neg {wt : ℤ} (h : wt < 0) :
    Filter.Tendsto (wtFactor wt) Filter.atTop (nhds 0) := by
  have hw : (wt : ℝ) < 0 := by exact_mod_cast h
  have hc : (wt : ℝ) / 2 < 0 := by linarith
  have h1 : Filter.Tendsto (fun y : ℝ => (wt : ℝ) / 2 * Real.log y) Filter.atTop Filter.atBot :=
    Real.tendsto_log_atTop.const_mul_atTop_of_neg hc
  exact Real.tendsto_exp_atBot.comp h1

theorem tendsto_wtFactor_atTop_of_pos {wt : ℤ} (h : 0 < wt) :
    Filter.Tendsto (wtFactor wt) Filter.atTop Filter.atTop := by
  have hw : (0 : ℝ) < wt := by exact_mod_cast h
  have hc : (0 : ℝ) < (wt : ℝ) / 2 := by linarith
  have h1 : Filter.Tendsto (fun y : ℝ => (wt : ℝ) / 2 * Real.log y) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hc
  exact Real.tendsto_exp_atTop.comp h1

theorem wtFactor_mul_self (wt : ℤ) {y : ℝ} (hy : 0 < y) :
    wtFactor wt y * wtFactor wt y = wtFactor (2 * wt) y := by
  rw [wtFactor_eq_rpow wt hy, wtFactor_eq_rpow (2 * wt) hy, ← Real.rpow_add hy]
  congr 1
  push_cast
  ring

theorem wtFactor_neg_mul (wt : ℤ) (y : ℝ) : wtFactor wt y * wtFactor (-wt) y = 1 := by
  rw [← wtFactor_add, add_neg_cancel, wtFactor_zero]

end TernaryPeriodPolynomials.EvenLevelThree
