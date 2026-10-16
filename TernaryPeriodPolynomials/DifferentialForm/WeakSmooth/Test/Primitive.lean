module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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


/-! Actual compact scalar test primitives on an interval. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped ContDiff Distributions

/-- A smooth scalar antiderivative written as an actual interval integral. -/
def scalarTestPrimitive (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in a..x, f t

theorem scalarTestPrimitive_hasDerivAt (a : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (scalarTestPrimitive a f) (f x) x :=
  (hf.integral_hasStrictDerivAt a x).hasDerivAt

theorem scalarTestPrimitive_contDiff (a : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarTestPrimitive a f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (scalarTestPrimitive_hasDerivAt a hf.continuous x).differentiableAt, ?_⟩
  have hd : deriv (scalarTestPrimitive a f) = f := by
    funext x
    exact (scalarTestPrimitive_hasDerivAt a hf.continuous x).deriv
  rw [hd]
  exact hf

/-- Vanishing total integral makes the antiderivative supported in the same closed interval. -/
theorem scalarTestPrimitive_tsupport {a b : ℝ} {f : ℝ → ℝ}
    (hs : Function.support f ⊆ Ioo a b) (hz : ∫ x, f x = 0) :
    tsupport (scalarTestPrimitive a f) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  rw [mem_Icc, not_and_or] at h
  rcases h with h | h
  · have hxa : x < a := lt_of_not_ge h
    apply hx
    change (∫ t in a..x, f t) = 0
    calc
      _ = ∫ t in a..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        have ht' : t ∈ Ioo x a := by simpa [uIoo, min_eq_right hxa.le, max_eq_left hxa.le] using ht
        by_contra hft
        exact (not_lt_of_ge (hs hft).1.le) ht'.2
      _ = 0 := by simp
  · have hbx : b < x := lt_of_not_ge h
    apply hx
    change (∫ t in a..x, f t) = 0
    exact (intervalIntegral.integral_eq_integral_of_support_subset
      (fun t ht => ⟨(hs ht).1, (hs ht).2.le.trans hbx.le⟩)).trans hz

/-- A zero-integral smooth scalar test has a genuine compact smooth antiderivative. -/
theorem exists_compact_scalar_test_primitive {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : Function.support f ⊆ Ioo a b)
    (hz : ∫ x, f x = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Icc a b ∧ ∀ x, deriv g x = f x := by
  refine ⟨scalarTestPrimitive a f, scalarTestPrimitive_contDiff a hf,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (scalarTestPrimitive_tsupport hs hz), scalarTestPrimitive_tsupport hs hz, ?_⟩
  intro x
  exact (scalarTestPrimitive_hasDerivAt a hf.continuous x).deriv

end TernaryPoly.PolynomialFormWeakSmooth
