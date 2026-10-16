module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

/-! Quantitative positivity in the existing topology, without replacing its norm. -/
namespace TernaryPoly.PositiveBilinearFinite

open Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous positive definite bilinear form dominates the square of the original norm. -/
theorem exists_pos_lower_bound (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v := by
  by_cases hE : Subsingleton E
  · let := hE
    exact ⟨1, zero_lt_one, fun v => by simp [Subsingleton.elim v 0]⟩
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one)
    ((B.continuous.clm_apply continuous_id).continuousOn)
  have hunorm : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hunorm
  refine ⟨B u u, hB u hu0, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hz : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
    simpa using norm_smul_inv_norm (𝕜 := ℝ) hv
  have hh := mul_le_mul_of_nonneg_right (hmin hz) (sq_nonneg ‖v‖)
  calc
    B u u * ‖v‖ ^ 2 ≤ B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 := hh
    _ = B v v := by simp [map_smul, smul_eq_mul, field]

/-- Its open unit ball is bounded in the preexisting locally convex topology. -/
theorem isVonNBounded_unitBall (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_lower_bound B hB
  apply NormedSpace.isVonNBounded_of_isBounded
  apply (isBounded_closedBall (x := (0 : E)) (r := max 1 c⁻¹)).subset
  intro v hv
  rw [mem_closedBall, dist_zero_right]
  by_contra! h
  have hn : 1 < ‖v‖ := lt_of_le_of_lt (le_max_left _ _) h
  have hi : c⁻¹ < ‖v‖ := lt_of_le_of_lt (le_max_right _ _) h
  have hcv : 1 < c * ‖v‖ := by
    simpa [hc.ne'] using mul_lt_mul_of_pos_left hi hc
  have hsq : ‖v‖ ≤ ‖v‖ ^ 2 := by nlinarith
  have hvv : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hbound v) hv
  nlinarith

end TernaryPoly.PositiveBilinearFinite
