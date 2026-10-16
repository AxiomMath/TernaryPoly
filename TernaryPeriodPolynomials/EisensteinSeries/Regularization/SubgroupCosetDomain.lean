module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic
public import Mathlib.Basic.Countable.Basic
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
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance subgroupCoset_countable {G : Type*} [Group G] [Countable G] (subgroup : Subgroup G) :
    Countable (G ⧸ subgroup) := Function.Surjective.countable (QuotientGroup.mk_surjective (s := subgroup))

noncomputable def subgroupCosetDomain {G X : Type*} [Group G] [MulAction G X]
    (subgroup : Subgroup G) (domain : Set X) : Set X :=
  ⋃ coset : G ⧸ subgroup, (Quotient.out coset)⁻¹ • domain

theorem subgroupCosetDomain_measurable {G X : Type*} [Group G] [Countable G]
    [MulAction G X] [MeasurableSpace X] [MeasurableConstSMul G X]
    (subgroup : Subgroup G) {domain : Set X} (measurable : MeasurableSet domain) :
    MeasurableSet (subgroupCosetDomain subgroup domain) :=
  MeasurableSet.iUnion (fun _ => measurable.const_smul _)

theorem subgroupCosetDomain_parts_aedisjoint {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace X] (subgroup : Subgroup G) {domain : Set X} {measure : Measure X}
    (fundamental : IsFundamentalDomain G domain measure) :
    Pairwise (fun first second : G ⧸ subgroup =>
      AEDisjoint measure ((Quotient.out first)⁻¹ • domain) ((Quotient.out second)⁻¹ • domain)) := by
  intro first second different
  apply fundamental.aedisjoint
  intro equal
  apply different
  have out_equal := inv_injective equal
  have quot_equal := congrArg (fun element : G => (element : G ⧸ subgroup)) out_equal
  simpa only [QuotientGroup.out_eq'] using quot_equal

theorem subgroupCosetDomain_isFundamental {G X : Type*} [Group G] [Countable G]
    [MulAction G X] [MeasurableSpace X] [MeasurableConstSMul G X]
    (subgroup : Subgroup G) {domain : Set X} {measure : Measure X}
    [SMulInvariantMeasure G X measure]
    (measurable : MeasurableSet domain) (fundamental : IsFundamentalDomain G domain measure) :
    IsFundamentalDomain subgroup (subgroupCosetDomain subgroup domain) measure := by
  apply IsFundamentalDomain.mk'' (subgroupCosetDomain_measurable subgroup measurable).nullMeasurableSet
  · filter_upwards [fundamental.ae_covers] with point covered
    obtain ⟨element, member⟩ := covered
    let coset : G ⧸ subgroup := element
    have member_subgroup : (Quotient.out coset)⁻¹ * element ∈ subgroup := by
      apply QuotientGroup.eq.mp
      exact QuotientGroup.out_eq' coset
    refine ⟨⟨(Quotient.out coset)⁻¹ * element, member_subgroup⟩, Set.mem_iUnion.mpr ⟨coset, ?_⟩⟩
    exact ⟨element • point, member, by simp only [Subgroup.smul_def, smul_smul]⟩
  · intro element nonidentity
    change AEDisjoint measure (element.val • (⋃ coset : G ⧸ subgroup, (Quotient.out coset)⁻¹ • domain))
      (⋃ coset : G ⧸ subgroup, (Quotient.out coset)⁻¹ • domain)
    rw [Set.smul_set_iUnion]
    apply AEDisjoint.iUnion_left_iff.mpr
    intro first
    apply AEDisjoint.iUnion_right_iff.mpr
    intro second
    rw [smul_smul]
    apply fundamental.aedisjoint
    intro equal
    have element_eq : element.val = (Quotient.out second)⁻¹ * Quotient.out first :=
      mul_inv_eq_iff_eq_mul.mp equal
    have cosets_equal : second = first := by
      have equal' : ((Quotient.out second : G) : G ⧸ subgroup) =
          ((Quotient.out first : G) : G ⧸ subgroup) :=
        QuotientGroup.eq.mpr (element_eq ▸ element.property)
      simpa only [QuotientGroup.out_eq'] using equal'
    rw [cosets_equal, inv_mul_cancel] at element_eq
    exact nonidentity (Subtype.ext element_eq)
  · intro element
    exact (measurePreserving_smul (element.val : G) measure).quasiMeasurePreserving

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
