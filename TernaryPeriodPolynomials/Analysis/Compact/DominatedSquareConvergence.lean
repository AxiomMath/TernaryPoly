module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
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
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Square-integral convergence from actual pointwise convergence and a common finite support. -/
namespace TernaryPoly.CompactDominatedSquareConvergence
open MeasureTheory Filter
variable {X F ι : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  {μ : Measure X} {l : Filter ι} [l.IsCountablyGenerated]

theorem integral_norm_square_tendsto_zero (u : ι → X → F) (K : Set X)
    (hK : MeasurableSet K) (hKfinite : μ K ≠ ⊤) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ᶠ i in l, AEStronglyMeasurable (u i) μ)
    (hbound : ∀ᶠ i in l, ∀ x, ‖u i x‖ ≤ C)
    (hsupport : ∀ᶠ i in l, ∀ x, x ∉ K → u i x = 0)
    (ht : ∀ x, Tendsto (fun i => u i x) l (nhds 0)) :
    Tendsto (fun i => ∫ x, ‖u i x‖ ^ 2 ∂μ) l (nhds 0) := by
  let bound : X → ℝ := K.indicator (fun _ => C ^ 2)
  have hi : Integrable bound μ :=
    (integrable_indicator_iff hK).mpr (integrableOn_const hKfinite)
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖‖u i x‖ ^ 2‖ ≤ bound x := by
    filter_upwards [hbound, hsupport] with i hbi hsi
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ K
    · simp only [bound, Set.indicator_of_mem hx, Real.norm_of_nonneg (sq_nonneg _)]
      have hn := norm_nonneg (u i x)
      have h := hbi x
      nlinarith
    · simp [bound, Set.indicator_of_notMem hx, hsi x hx]
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (fun x => ‖u i x‖ ^ 2) μ := by
    filter_upwards [hu] with i hi
    exact hi.norm.pow 2
  have ht' : ∀ᵐ x ∂μ, Tendsto (fun i => ‖u i x‖ ^ 2) l (nhds (0 : ℝ)) :=
    Eventually.of_forall (fun x => by simpa using ((ht x).norm.pow 2))
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence bound hm hb hi ht'

end TernaryPoly.CompactDominatedSquareConvergence
