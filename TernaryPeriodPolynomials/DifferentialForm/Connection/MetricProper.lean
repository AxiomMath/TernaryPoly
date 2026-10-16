module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Fintype.Option
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
public import Mathlib.Order.Filter.AtTopBot.Map
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Properness from a uniform compact metric radius and a genuine short-path splitting property. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Metric Set

variable {X : Type*} [MetricSpace X]

theorem uniform_compact_radius_of_transitive_isometries [LocallyCompactSpace X] [Nonempty X]
    (htrans : ∀ x y : X, ∃ g : X ≃ᵢ X, g x = y) :
    ∃ ε > 0, ∀ x : X, IsCompact (closedBall x ε) := by
  let x : X := Classical.choice inferInstance
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hKn
  have hc : IsCompact (closedBall x (r / 2)) := hK.of_isClosed_subset isClosed_closedBall
    ((closedBall_subset_ball (half_lt_self hr)).trans hball)
  refine ⟨r / 2, half_pos hr, fun y => ?_⟩
  obtain ⟨g, hg⟩ := htrans x y
  have h := hc.image g.continuous
  simpa only [g.image_closedBall, hg] using h

theorem compact_ball_step_of_split (ε : ℝ) (hε : 0 < ε)
    (hc : ∀ x : X, IsCompact (closedBall x ε))
    (hsplit : ∀ x y : X, ∀ r s : ℝ, 0 ≤ r → 0 < s → dist x y < r + s →
      ∃ z, dist x z ≤ r ∧ dist z y < s)
    (x : X) (r : ℝ) (hr : 0 ≤ r) (hball : IsCompact (closedBall x r)) :
    IsCompact (closedBall x (r + ε / 4)) := by
  obtain ⟨t, ht⟩ := hball.elim_finite_subcover (fun z : X => ball z (ε / 4))
    (fun _ => isOpen_ball) (by intro z _; exact mem_iUnion.mpr ⟨z, mem_ball_self (by positivity)⟩)
  have hfinite : IsCompact (⋃ z ∈ t, closedBall z ε) :=
    t.finite_toSet.isCompact_biUnion (fun z _ => hc z)
  apply hfinite.of_isClosed_subset isClosed_closedBall
  intro y hy
  have hxy : dist x y < r + ε / 2 := by
    have hy' : dist x y ≤ r + ε / 4 := by simpa only [mem_closedBall, dist_comm] using hy
    linarith
  obtain ⟨z, hz, hzy⟩ := hsplit x y r (ε / 2) hr (by positivity) hxy
  have hzmem : z ∈ closedBall x r := by simpa only [mem_closedBall, dist_comm] using hz
  obtain ⟨a, hat, hza⟩ := mem_iUnion₂.mp (ht hzmem)
  apply mem_iUnion₂.mpr
  refine ⟨a, hat, ?_⟩
  have hza' : dist z a < ε / 4 := hza
  have htri := dist_triangle y z a
  rw [dist_comm y z] at htri
  change dist y a ≤ ε
  linarith

/-- This proof uses compact neighborhoods, not an unproved Hopf--Rinow theorem. -/
theorem proper_of_uniform_compact_radius_and_split (ε : ℝ) (hε : 0 < ε)
    (hc : ∀ x : X, IsCompact (closedBall x ε))
    (hsplit : ∀ x y : X, ∀ r s : ℝ, 0 ≤ r → 0 < s → dist x y < r + s →
      ∃ z, dist x z ≤ r ∧ dist z y < s) : ProperSpace X := by
  have hballs (x : X) (n : ℕ) : IsCompact (closedBall x ((n : ℝ) * (ε / 4))) := by
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_mul, closedBall_zero] using isCompact_singleton (x := x)
    | succ n ih =>
      simpa only [Nat.cast_succ, add_mul, one_mul] using
        compact_ball_step_of_split ε hε hc hsplit x ((n : ℝ) * (ε / 4)) (by positivity) ih
  apply ProperSpace.of_isCompact_closedBall_of_le 0
  intro x r hr
  obtain ⟨n, hn⟩ := exists_nat_gt (r / (ε / 4))
  have hnr : r ≤ (n : ℝ) * (ε / 4) := by
    exact (div_lt_iff₀ (by positivity)).mp hn |>.le
  exact (hballs x n).of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hnr)

end TernaryPoly.PolynomialFormConnection
