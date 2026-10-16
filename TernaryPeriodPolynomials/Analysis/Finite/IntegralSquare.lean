module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Multiset.Fintype
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
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Finite-sum square integral bounds for actual matrix regularizers. -/
namespace TernaryPoly.FiniteIntegralSquare
open MeasureTheory Filter
variable {X I : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The square integral of a finite sum is controlled by the sum of square integrals. -/
theorem integral_sum_square_le (s : Finset I) (f : I → X → ℝ)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ)
    (h2 : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ) :
    ∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ ≤ (s.card : ℝ) * ∑ i ∈ s, ∫ x, f i x ^ 2 ∂μ := by
  have hmaj : Integrable (fun x => (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2) μ :=
    (integrable_finsetSum s (fun i hi => h2 i hi)).const_mul _
  have hm : AEStronglyMeasurable (fun x => (∑ i ∈ s, f i x) ^ 2) μ := by
    have he : (fun x => (∑ i ∈ s, f i x) ^ 2) = (∑ i ∈ s, f i) ^ 2 := by
      funext x
      simp only [Pi.pow_apply, Finset.sum_apply]
    rw [he]
    exact (Finset.aestronglyMeasurable_sum s hf).pow 2
  have hi : Integrable (fun x => (∑ i ∈ s, f i x) ^ 2) μ := by
    apply hmaj.mono' hm
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_sum_le_card_mul_sum_sq)
  calc
    _ ≤ ∫ x, (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2 ∂μ :=
      integral_mono hi hmaj (fun x => sq_sum_le_card_mul_sum_sq)
    _ = _ := by rw [integral_const_mul, integral_finsetSum _ (fun i hi => h2 i hi)]

/-- Finite sums preserve actual square-integral convergence to zero. -/
theorem integral_sum_square_tendsto_zero {ι : Type*} {l : Filter ι}
    (s : Finset I) (f : I → ι → X → ℝ)
    (hf : ∀ i ∈ s, ∀ᶠ c in l, AEStronglyMeasurable (f i c) μ)
    (h2 : ∀ i ∈ s, ∀ᶠ c in l, Integrable (fun x => f i c x ^ 2) μ)
    (ht : ∀ i ∈ s, Tendsto (fun c => ∫ x, f i c x ^ 2 ∂μ) l (nhds 0)) :
    Tendsto (fun c => ∫ x, (∑ i ∈ s, f i c x) ^ 2 ∂μ) l (nhds 0) := by
  have hm := (eventually_all_finset s).mpr hf
  have hi := (eventually_all_finset s).mpr h2
  have hb : ∀ᶠ c in l, (∫ x, (∑ i ∈ s, f i c x) ^ 2 ∂μ) ≤
      (s.card : ℝ) * ∑ i ∈ s, ∫ x, f i c x ^ 2 ∂μ := by
    filter_upwards [hm, hi] with c hmc hic
    exact integral_sum_square_le s (fun i => f i c) hmc hic
  have hlim : Tendsto (fun c => (s.card : ℝ) * ∑ i ∈ s, ∫ x, f i c x ^ 2 ∂μ) l (nhds 0) := by
    simpa using (tendsto_finsetSum s ht).const_mul (s.card : ℝ)
  exact squeeze_zero' (Eventually.of_forall (fun c => integral_nonneg (fun x => sq_nonneg _))) hb hlim

end TernaryPoly.FiniteIntegralSquare
