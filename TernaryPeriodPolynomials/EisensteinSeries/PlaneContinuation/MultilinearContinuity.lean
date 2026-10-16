module

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.WithTopology

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MultilinearContinuity

/-- Finite dimensionality of the inputs turns pointwise continuity into operator-norm continuity. -/
theorem continuous_of_eval {Parameter Scalar Input Output : Type}
    [TopologicalSpace Parameter] [NontriviallyNormedField Scalar] [CompleteSpace Scalar]
    [NormedAddCommGroup Input] [NormedSpace Scalar Input] [FiniteDimensional Scalar Input]
    [NormedAddCommGroup Output] [NormedSpace Scalar Output]
    (order : ℕ) (family : Parameter → ContinuousMultilinearMap Scalar (fun _ : Fin order => Input) Output)
    (evaluationContinuous : ∀ directions, Continuous (fun parameter => family parameter directions)) :
    Continuous family := by
  induction order with
  | zero =>
    let curry := continuousMultilinearCurryFin0 Scalar Input Output
    have continuity : Continuous (fun parameter => curry (family parameter)) := evaluationContinuous 0
    exact (curry.symm.continuous.comp continuity).congr (fun parameter => curry.symm_apply_apply (family parameter))
  | succ order inductionHypothesis =>
    let curry := continuousMultilinearCurryLeftEquiv Scalar (fun _ : Fin (order + 1) => Input) Output
    have continuity : Continuous (fun parameter => curry (family parameter)) := by
      apply continuous_clm_apply.mpr
      intro first
      apply inductionHypothesis
      intro remaining
      exact evaluationContinuous (Fin.cons first remaining)
    exact (curry.symm.continuous.comp continuity).congr (fun parameter => curry.symm_apply_apply (family parameter))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MultilinearContinuity
