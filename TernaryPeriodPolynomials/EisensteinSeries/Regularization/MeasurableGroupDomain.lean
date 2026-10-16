module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Normed.Module.FiniteDimension
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
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem subgroup_measurable_domain_of_cover
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (subgroup : Subgroup G) [Countable subgroup]
    (cover : ℕ → Set G) (measurable : ∀ index, MeasurableSet (cover index))
    (covers : ∀ point, ∃ index, point ∈ cover index)
    (separated : ∀ index, ∀ first ∈ cover index, ∀ second ∈ cover index,
      ∀ element : subgroup, element.val * first = second → element = 1) :
    ∃ domain : Set G, MeasurableSet domain ∧ ∀ point : G,
      ∃! element : subgroup, element.val * point ∈ domain := by
  classical
  let piece (index : ℕ) : Set G := cover index \ ⋃ earlier < index,
    ⋃ element : subgroup, (fun point : G => element.val * point) ⁻¹' cover earlier
  let domain := ⋃ index, piece index
  have piece_measurable (index : ℕ) : MeasurableSet (piece index) := by
    apply (measurable index).diff
    exact MeasurableSet.iUnion (fun earlier => MeasurableSet.iUnion (fun _ =>
      MeasurableSet.iUnion (fun element => (measurable earlier).preimage (measurable_const_mul element.val))))
  have piece_mem (point : G) (index : ℕ) : point ∈ piece index ↔
      point ∈ cover index ∧ ∀ earlier < index, ∀ element : subgroup,
        element.val * point ∉ cover earlier := by
    simp only [piece, Set.mem_sdiff, Set.mem_iUnion, Set.mem_preimage, not_exists]
  refine ⟨domain, MeasurableSet.iUnion piece_measurable, ?_⟩
  intro point
  have exists_index : ∃ index, ∃ element : subgroup, element.val * point ∈ cover index := by
    obtain ⟨index, member⟩ := covers point
    exact ⟨index, 1, by simpa using member⟩
  let index := Nat.find exists_index
  obtain ⟨element, member⟩ := Nat.find_spec exists_index
  have no_earlier (earlier : ℕ) (less : earlier < index) (other : subgroup) :
      other.val * point ∉ cover earlier := by
    intro earlier_member
    exact (Nat.find_min exists_index less) ⟨other, earlier_member⟩
  have selected : element.val * point ∈ piece index := by
    rw [piece_mem]
    refine ⟨member, ?_⟩
    intro earlier less other earlier_member
    apply no_earlier earlier less (other * element)
    simpa only [Subgroup.coe_mul, mul_assoc] using earlier_member
  refine ⟨element, Set.mem_iUnion.mpr ⟨index, selected⟩, ?_⟩
  intro other other_member
  obtain ⟨otherIndex, other_piece⟩ := Set.mem_iUnion.mp other_member
  obtain ⟨other_cover, other_minimal⟩ := (piece_mem _ _).mp other_piece
  have index_le : index ≤ otherIndex := Nat.find_min' exists_index ⟨other, other_cover⟩
  have other_le : otherIndex ≤ index := by
    by_contra! less
    apply other_minimal index less (element * other⁻¹)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left] using member
  have indices : otherIndex = index := le_antisymm other_le index_le
  rw [indices] at other_cover
  have equal := separated index (element.val * point) member (other.val * point) other_cover
    (other * element⁻¹) (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left])
  exact (mul_inv_eq_one.mp equal)

theorem discrete_subgroup_countable_separated_cover
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LindelofSpace G]
    (subgroup : Subgroup G) [DiscreteTopology subgroup] :
    ∃ cover : ℕ → Set G, (∀ index, IsOpen (cover index)) ∧
      (∀ point, ∃ index, point ∈ cover index) ∧
      ∀ index, ∀ first ∈ cover index, ∀ second ∈ cover index,
        ∀ element : subgroup, element.val * first = second → element = 1 := by
  obtain ⟨neighborhood, neighborhood_mem, _, separated⟩ :=
    IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty subgroup
      (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)
  obtain ⟨small, small_subset, small_open, one_mem⟩ := mem_nhds_iff.mp neighborhood_mem
  let chart (center : G) : Set G := (fun point => point * center⁻¹) ⁻¹' small
  have chart_open (center : G) : IsOpen (chart center) :=
    small_open.preimage (continuous_id.mul continuous_const)
  have cover_all : (Set.univ : Set G) ⊆ ⋃ center, chart center := by
    intro point _
    exact Set.mem_iUnion.mpr ⟨point, by simpa only [chart, Set.mem_preimage, mul_inv_cancel] using one_mem⟩
  obtain ⟨centers, cover_all⟩ := isLindelof_univ.indexed_countable_subcover chart chart_open cover_all
  refine ⟨fun index => chart (centers index), fun index => chart_open (centers index), ?_, ?_⟩
  · intro point
    exact Set.mem_iUnion.mp (cover_all (Set.mem_univ point))
  · intro index first first_member second second_member element relation
    apply Subtype.ext
    apply separated element.val element.property
    refine ⟨second * (centers index)⁻¹, ?_, small_subset second_member⟩
    refine ⟨first * (centers index)⁻¹, small_subset first_member, ?_⟩
    change element.val * (first * (centers index)⁻¹) = _
    rw [← mul_assoc, relation]

theorem discrete_subgroup_measurable_fundamental_domain
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LindelofSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (subgroup : Subgroup G) [DiscreteTopology subgroup] [Countable subgroup]
    (measure : Measure G) :
    ∃ domain : Set G, MeasurableSet domain ∧ IsFundamentalDomain subgroup domain measure := by
  obtain ⟨cover, open_cover, covers, separated⟩ := discrete_subgroup_countable_separated_cover subgroup
  obtain ⟨domain, measurable, unique⟩ := subgroup_measurable_domain_of_cover subgroup cover
    (fun index => (open_cover index).measurableSet) covers separated
  exact ⟨domain, measurable, IsFundamentalDomain.mk' measurable.nullMeasurableSet unique⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
