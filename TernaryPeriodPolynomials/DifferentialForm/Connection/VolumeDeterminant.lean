module

public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Data.List.Enum
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Genuine determinant derivatives in the five-dimensional tangent metric calculation. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix ContinuousAlternatingMap
open scoped Matrix.Norms.Elementwise

/-- The ordinary determinant as a continuous alternating map of its actual rows. -/
def determinantRows (m : ℕ) : (Fin m → ℝ) [⋀^Fin m]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with cont := continuous_id.matrix_det }

@[simp] theorem determinantRows_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) : determinantRows m A = A.det := rfl

theorem det_updateRow_one (m : ℕ) (i : Fin m) (v : Fin m → ℝ) :
    ((1 : Matrix (Fin m) (Fin m) ℝ).updateRow i v).det = v i := by
  have hv : (∑ j : Fin m, v j • (1 : Matrix (Fin m) (Fin m) ℝ) j) = v := by
    funext j
    simp [Matrix.one_apply, Pi.smul_apply]
  have h := Matrix.det_updateRow_sum (1 : Matrix (Fin m) (Fin m) ℝ) i v
  rw [hv, Matrix.det_one, smul_eq_mul, mul_one] at h
  exact h

/-- Differentiating the literal determinant at identity gives exactly the trace. -/
theorem hasDerivAt_det_identity (m : ℕ) (A : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (hA : HasDerivAt A R 0) (h0 : A 0 = 1) :
    HasDerivAt (fun t => (A t).det) R.trace 0 := by
  have h := (determinantRows m).hasFDerivAt (A 0) |>.comp_hasDerivAt 0 hA
  have hd : (determinantRows m).toContinuousMultilinearMap.linearDeriv (A 0) R = R.trace := by
    have hs := ContinuousMultilinearMap.linearDeriv_apply
      (f := (determinantRows m).toContinuousMultilinearMap) (x := A 0) (y := R)
    convert! hs.trans ?_ using 1
    rw [h0]
    change (∑ i : Fin m, ((1 : Matrix (Fin m) (Fin m) ℝ).updateRow i (R i)).det) = _
    simp only [det_updateRow_one, Matrix.trace]
    rfl
  rw [hd] at h
  exact h

end TernaryPoly.PolynomialFormConnection
