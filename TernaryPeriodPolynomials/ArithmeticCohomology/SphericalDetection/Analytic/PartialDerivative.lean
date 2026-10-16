module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
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
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem analyticAt_partialDeriv {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (function : P × ℝ → F) (point : P) (center : ℝ)
    (analytic : AnalyticAt ℝ function (point, center)) :
    AnalyticAt ℝ (fun parameter => deriv (fun sample => function (parameter, sample)) center) point := by
  let evaluation : ((P × ℝ) →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (0, 1)
  have full := (evaluation.analyticAt (fderiv ℝ function (point, center))).comp analytic.fderiv
  have embedding : AnalyticAt ℝ (fun parameter : P => (parameter, center)) point :=
    analyticAt_id.prod analyticAt_const
  have restricted := full.comp (f := fun parameter : P => (parameter, center)) (x := point) embedding
  apply restricted.congr
  have nearby : ∀ᶠ parameter in nhds point, AnalyticAt ℝ function (parameter, center) :=
    Filter.Tendsto.eventually embedding.continuousAt analytic.eventually_analyticAt
  filter_upwards [nearby] with parameter regular
  have derivative := regular.differentiableAt.hasFDerivAt.comp_hasDerivAt center
    ((hasDerivAt_const center parameter).prodMk (hasDerivAt_id center))
  exact derivative.deriv.symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
