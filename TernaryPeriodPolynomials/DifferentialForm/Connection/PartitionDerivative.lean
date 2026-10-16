module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.TangentCone.DimOne
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


/-! Finite partition derivatives cancel along an actual continuous vector field. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Set Filter
open scoped Topology

/-- The partition only needs to sum to one near the nonzero vector field. -/
theorem finite_partition_derivative_cancel {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (ψ : ι → E → ℝ) (V : E → E) (x : E)
    (hψ : ∀ i, DifferentiableAt ℝ (ψ i) x) (hV : ContinuousAt V x)
    (hpart : ∀ᶠ y in 𝓝 x, V y ≠ 0 → ∑ i, ψ i y = 1) :
    (∑ i, fderiv ℝ (ψ i) x (V x)) = 0 := by
  by_cases hx : V x = 0
  · simp only [hx, map_zero, Finset.sum_const_zero]
  · have hnear : ∀ᶠ y in 𝓝 x, V y ≠ 0 :=
      hV.eventually (isClosed_singleton.isOpen_compl.mem_nhds hx)
    have he : (fun y => ∑ i, ψ i y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hnear, hpart] with y hy hp
      exact hp hy
    have hd : fderiv ℝ (fun y => ∑ i, ψ i y) x = ∑ i, fderiv ℝ (ψ i) x :=
      fderiv_fun_sum (fun i _ => hψ i)
    have hz : (∑ i, fderiv ℝ (ψ i) x) = 0 :=
      hd.symm.trans (he.fderiv_eq.trans (fderiv_const_apply 1))
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (V x)) hz
    simpa only [_root_.sum_apply, _root_.zero_apply] using h

end TernaryPoly.PolynomialFormConnection
