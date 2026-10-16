module

public import TernaryPeriodPolynomials.Analysis.ChartLocalMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section


/-! Integration in the actual chart-local measure agrees with coordinate integration. -/
noncomputable section
namespace TernaryPoly.ChartLocalMeasure
open MeasureTheory Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- The actual source-embedding measure has the expected coordinate integral formula. -/
theorem integral_localMeasure (e : OpenPartialHomeomorph X Y) (μ : Measure Y) (f : X → ℝ) :
    ∫ x, f x ∂localMeasure e μ = ∫ y in e.target, f (e.symm y) ∂μ := by
  have hr : range (fun x : e.source => e x) = e.target := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact e.map_source x.property
    · intro hy
      exact ⟨⟨e.symm y, e.map_target hy⟩, e.right_inv hy⟩
  have hm := (chart_measurableEmbedding e).map_comap μ
  rw [hr] at hm
  unfold localMeasure
  rw [(MeasurableEmbedding.subtype_coe e.open_source.measurableSet).integral_map,
    ← hm, (chart_measurableEmbedding e).integral_map]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [e.left_inv x.property]

end TernaryPoly.ChartLocalMeasure
