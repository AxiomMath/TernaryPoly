module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Continuous lifts of smooth maps through a local diffeomorphism are smooth. -/
namespace TernaryPoly.LocalDiffeomorphLiftSmooth

open Manifold Filter
open scoped Manifold ContDiff Topology

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' K : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ F K}
  {M M' N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [TopologicalSpace N] [ChartedSpace K N]
  {n : WithTop ℕ∞}

/-- Lower the differentiability order of the actual local inverse data. -/
theorem isLocalDiffeomorph_of_le {m : WithTop ℕ∞} {p : M → M'}
    (hp : IsLocalDiffeomorph I I' m p) (hn : n ≤ m) : IsLocalDiffeomorph I I' n p := by
  intro x
  obtain ⟨e, he, heq⟩ := hp x
  exact ⟨{ e with
    contMDiffOn_toFun := e.contMDiffOn_toFun.of_le hn
    contMDiffOn_invFun := e.contMDiffOn_invFun.of_le hn }, he, heq⟩

/-- Smoothness is recovered using the actual smooth local inverses. -/
theorem contMDiff_lift {p : M → M'} (hp : IsLocalDiffeomorph I I' n p)
    {f : N → M'} (hf : ContMDiff J I' n f) {l : N → M}
    (hl : Continuous l) (he : p ∘ l = f) : ContMDiff J I n l := by
  intro x
  have hp0 : p (l x) = f x := congrFun he x
  have hi : ContMDiffAt I' I n (hp (l x)).localInverse (f x) := by
    rw [← hp0]
    exact (hp (l x)).contMDiffAt_localInverse
  have hcomp := hi.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  have hev := hl.continuousAt.eventually ((hp (l x)).localInverse_eventuallyEq_left)
  filter_upwards [hev] with y hy
  change (hp (l x)).localInverse (p (l y)) = l y at hy
  change l y = (hp (l x)).localInverse (f y)
  rw [← congrFun he y]
  exact hy.symm

end TernaryPoly.LocalDiffeomorphLiftSmooth
