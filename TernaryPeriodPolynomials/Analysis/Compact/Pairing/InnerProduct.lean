module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.Algebra
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
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Integrating compact continuous positive scalar pairings gives a genuine inner product. -/
noncomputable section
namespace TernaryPoly.CompactPairingInnerProduct

open MeasureTheory
variable {X V : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
  [AddCommGroup V] [Module ℝ V]

/-- The actual integral of the pointwise scalar pairing. -/
def pairing (B : V →ₗ[ℝ] V →ₗ[ℝ] C(X, ℝ)) (v w : V) : ℝ := ∫ x, B v w x ∂μ

omit [μ.IsOpenPosMeasure] in
theorem pairing_integrable (B : V →ₗ[ℝ] V →ₗ[ℝ] C(X, ℝ))
    (hc : ∀ v w, HasCompactSupport (B v w)) (v w : V) : Integrable (B v w) μ :=
  (B v w).continuous.integrable_of_hasCompactSupport (hc v w)

/-- The hypotheses concern the literal continuous scalar pairing and its compact support. -/
@[instance_reducible] def innerCore (B : V →ₗ[ℝ] V →ₗ[ℝ] C(X, ℝ))
    (hc : ∀ v w, HasCompactSupport (B v w))
    (hs : ∀ v w x, B v w x = B w v x)
    (hn : ∀ v x, 0 ≤ B v v x)
    (hp : ∀ v, v ≠ 0 → ∃ x, 0 < B v v x) : InnerProductSpace.Core ℝ V where
  inner := pairing (μ := μ) B
  conj_inner_symm v w := by
    simp only [pairing, conj_trivial]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => hs w v x)
  re_inner_nonneg v := integral_nonneg (hn v)
  add_left v w z := by
    simp only [pairing, map_add, LinearMap.add_apply, ContinuousMap.add_apply]
    exact integral_add (pairing_integrable B hc v z) (pairing_integrable B hc w z)
  smul_left v w c := by
    simp only [pairing, map_smul, LinearMap.smul_apply, ContinuousMap.smul_apply,
      smul_eq_mul, conj_trivial]
    exact integral_const_mul c _
  definite v h := by
    by_contra hv
    obtain ⟨x, hx⟩ := hp v hv
    have hpos := (B v v).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (μ := μ) (hc v v) (hn v) (ne_of_gt hx)
    exact (ne_of_gt hpos) h

end TernaryPoly.CompactPairingInnerProduct
