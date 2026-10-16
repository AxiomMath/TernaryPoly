module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProfiniteCharacter
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section


open Filter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfinitePeriodicity

variable {G Target : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_open_period (function : G → Target) (locallyConstant : IsLocallyConstant function) :
    ∃ subgroup : OpenAddSubgroup G, ∀ shift ∈ subgroup, ∀ point, function (shift + point) = function point := by
  have first : IsLocallyConstant (fun pair : G × G => function (pair.1 + pair.2)) :=
    locallyConstant.comp_continuous (continuous_fst.add continuous_snd)
  have second : IsLocallyConstant (fun pair : G × G => function pair.2) :=
    locallyConstant.comp_continuous continuous_snd
  have relation : IsOpen {pair : G × G | function (pair.1 + pair.2) = function pair.2} := by
    simpa using (first.comp₂ second (fun left right => left = right)).isOpen_fiber True
  have contains : ({0} : Set G) ×ˢ Set.univ ⊆ {pair : G × G | function (pair.1 + pair.2) = function pair.2} := by
    rintro ⟨shift, point⟩ ⟨rfl, _⟩
    simp
  obtain ⟨left, right, leftOpen, _, zeroIn, allIn, productIn⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ relation contains
  obtain ⟨subgroup, contained⟩ := ProfiniteGrp.exist_openNormalAddSubgroup_sub_open_nhds_of_zero
    leftOpen (zeroIn (Set.mem_singleton 0))
  refine ⟨subgroup.toOpenAddSubgroup, fun shift membership point => ?_⟩
  change shift ∈ (subgroup : Set G) at membership
  exact productIn (a := (shift, point)) ⟨contained membership, allIn (Set.mem_univ point)⟩

theorem exists_integer_period (function : G → Target) (locallyConstant : IsLocallyConstant function) :
    ∃ period : ℕ, period ≠ 0 ∧ ∀ shift point : G, function (period • shift + point) = function point := by
  obtain ⟨subgroup, invariant⟩ := exists_open_period function locallyConstant
  let _ : DiscreteTopology (G ⧸ subgroup.toAddSubgroup) := QuotientAddGroup.discreteTopology subgroup.isOpen
  let _ : Finite (G ⧸ subgroup.toAddSubgroup) := finite_of_compact_of_discrete
  let period := Nat.card (G ⧸ subgroup.toAddSubgroup)
  have positive : 0 < period := Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨period, positive.ne', fun shift point => invariant _ ?_ point⟩
  apply (QuotientAddGroup.eq_zero_iff (N := subgroup.toAddSubgroup) _).mp
  have equality := card_nsmul_eq_zero' (x := (QuotientAddGroup.mk' subgroup.toAddSubgroup) shift)
  change (QuotientAddGroup.mk' subgroup.toAddSubgroup) (period • shift) = 0
  rw [map_nsmul]
  exact equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfinitePeriodicity
