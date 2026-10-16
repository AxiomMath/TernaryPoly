module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanCompactConvexNeighborhoods
open Set Metric

/-- Finite unions of closed Euclidean balls are cofinal among compact neighborhoods: an
arbitrary compact set K has such a neighborhood inside every prescribed open U containing K. -/
theorem exists_finite_closedBall_neighborhood (d : ℕ)
    (K U : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (s : Finset K) (r : K → ℝ),
      (∀ x, 0 < r x) ∧ K ⊆ ⋃ x ∈ s, ball x.val (r x) ∧
      (⋃ x ∈ s, closedBall x.val (r x)) ⊆ U := by
  classical
  have hex : ∀ x : K, ∃ r : ℝ, 0 < r ∧ closedBall x.val r ⊆ U := by
    intro x
    obtain ⟨e,he,hsub⟩ := Metric.isOpen_iff.mp hU x.val (hKU x.property)
    exact ⟨e/2,by linarith,(closedBall_subset_ball (by linarith)).trans hsub⟩
  choose r hr hsub using hex
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun x : K => ball x.val (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr ⟨x,hx⟩)⟩)
  refine ⟨s,r,hr,hs,?_⟩
  intro y hy
  obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
  exact hsub x hy

/-- The resulting finite union is compact and is a neighborhood of K in the interior sense. -/
theorem finite_closedBall_properties (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (s : Finset K) (r : K → ℝ) (hcover : K ⊆ ⋃ x ∈ s, ball x.val (r x)) :
    IsCompact (⋃ x ∈ s, closedBall x.val (r x)) ∧
      K ⊆ interior (⋃ x ∈ s, closedBall x.val (r x)) := by
  classical
  constructor
  · exact s.finite_toSet.isCompact_biUnion (fun _ _ => isCompact_closedBall _ _)
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds hxy)
    intro z hz
    exact mem_iUnion₂.mpr ⟨y,hy,ball_subset_closedBall hz⟩

/-- A cofinal compact neighborhood may be presented as a finite family of compact convex
sets, with the support literally their finite union. -/
theorem exists_finite_convex_neighborhood (d : ℕ)
    (K U : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (s : Finset K) (A : K → Set (EuclideanSpace ℝ (Fin d))),
      (∀ i, IsCompact (A i) ∧ Convex ℝ (A i)) ∧
      IsCompact (⋃ i ∈ s, A i) ∧ K ⊆ interior (⋃ i ∈ s, A i) ∧ (⋃ i ∈ s, A i) ⊆ U := by
  obtain ⟨s,r,_,hcover,hsub⟩ := exists_finite_closedBall_neighborhood d K U hK hU hKU
  exact ⟨s,fun i => closedBall i.val (r i),fun i => ⟨isCompact_closedBall _ _,convex_closedBall _ _⟩,
    (finite_closedBall_properties d K s r hcover).1,
    (finite_closedBall_properties d K s r hcover).2,hsub⟩


/-- A compact set covered by arbitrary open sets admits a finite convex compact refinement,
with each closed ball contained in one specified member of the original cover. -/
theorem exists_finite_convex_refinement (d : ℕ) {ι : Type*}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (U : ι → Set (EuclideanSpace ℝ (Fin d))) (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (s : Finset K) (A : K → Set (EuclideanSpace ℝ (Fin d))) (j : K → ι),
      (∀ x, IsCompact (A x) ∧ Convex ℝ (A x) ∧ A x ⊆ U (j x)) ∧
      IsCompact (⋃ x ∈ s, A x) ∧ K ⊆ interior (⋃ x ∈ s, A x) := by
  classical
  have hex : ∀ x : K, ∃ i : ι, ∃ r : ℝ, 0 < r ∧ closedBall x.val r ⊆ U i := by
    intro x
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover x.property)
    obtain ⟨e,he,hsub⟩ := Metric.isOpen_iff.mp (hU i) x.val hi
    exact ⟨i,e/2,by linarith,(closedBall_subset_ball (by linarith)).trans hsub⟩
  choose j r hr hsub using hex
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun x : K => ball x.val (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr ⟨x,hx⟩)⟩)
  exact ⟨s,fun x => closedBall x.val (r x),j,
    fun x => ⟨isCompact_closedBall _ _,convex_closedBall _ _,hsub x⟩,
    finite_closedBall_properties d K s r hs⟩

end TernaryPoly.EuclideanCompactConvexNeighborhoods
