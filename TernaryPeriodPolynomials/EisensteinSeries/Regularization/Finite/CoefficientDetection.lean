module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.PowerSeries.Basic
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
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem finite_evaluation_detection {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (evaluation : I → V →ₗ[K] K)
    (separates : ∀ vector, (∀ index, evaluation index vector = 0) → vector = 0) :
    ∃ indices : Finset I, ∀ vector, (∀ index ∈ indices, evaluation index vector = 0) → vector = 0 := by
  classical
  let vanishing (indices : Finset I) : Submodule K V :=
    { carrier := {vector | ∀ index ∈ indices, evaluation index vector = 0}
      zero_mem' := by intro index _; exact map_zero _
      add_mem' := by
        intro first second first_zero second_zero index member
        rw [map_add, first_zero index member, second_zero index member, add_zero]
      smul_mem' := by
        intro scalar vector zero index member
        rw [map_smul, zero index member, smul_zero] }
  obtain ⟨_, ⟨indices, rfl⟩, minimal⟩ := IsArtinian.set_has_minimal (Set.range vanishing)
    ⟨vanishing ∅, ∅, rfl⟩
  refine ⟨indices, fun vector zero => separates vector ?_⟩
  intro index
  have le : vanishing (insert index indices) ≤ vanishing indices := by
    intro vector zero point member
    exact zero point (Finset.mem_insert_of_mem member)
  have equality : vanishing (insert index indices) = vanishing indices := by
    by_contra different
    exact minimal _ ⟨insert index indices, rfl⟩ (lt_of_le_of_ne le different)
  have member : vector ∈ vanishing indices := zero
  rw [← equality] at member
  exact member index (Finset.mem_insert_self _ _)

theorem finite_coefficient_detection {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (coefficient : ℕ → V →ₗ[K] K)
    (separates : ∀ vector, (∀ index, coefficient index vector = 0) → vector = 0) :
    ∃ length : ℕ, ∀ vector, (∀ index < length, coefficient index vector = 0) → vector = 0 := by
  let vanishing (length : ℕ) : Submodule K V :=
    { carrier := {vector | ∀ index < length, coefficient index vector = 0}
      zero_mem' := by intro index _; exact map_zero _
      add_mem' := by
        intro first second first_zero second_zero index before
        rw [map_add, first_zero index before, second_zero index before, add_zero]
      smul_mem' := by
        intro scalar vector zero index before
        rw [map_smul, zero index before, smul_zero] }
  have antitone : Antitone vanishing := by
    intro first second le vector zero index before
    exact zero index (lt_of_lt_of_le before le)
  let chain : ℕ →o (Submodule K V)ᵒᵈ := ⟨vanishing, antitone⟩
  obtain ⟨length, stable⟩ := IsArtinian.monotone_stabilizes chain
  refine ⟨length, fun vector zero => separates vector ?_⟩
  intro index
  have member : vector ∈ vanishing length := zero
  have equality : vanishing length = vanishing (max length (index + 1)) :=
    stable _ (le_max_left _ _)
  rw [equality] at member
  exact member index (lt_of_lt_of_le (Nat.lt_succ_self index) (le_max_right _ _))

theorem finite_powerSeries_detection {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (series : V →ₗ[K] PowerSeries K) (injective : Function.Injective series) :
    ∃ length : ℕ, ∀ vector, (∀ index < length, PowerSeries.coeff index (series vector) = 0) → vector = 0 := by
  let coefficient (index : ℕ) : V →ₗ[K] K :=
    { toFun := fun vector => PowerSeries.coeff index (series vector)
      map_add' := by intro first second; simp only [map_add]
      map_smul' := by intro scalar vector; simp only [map_smul, RingHom.id_apply] }
  apply finite_coefficient_detection coefficient
  intro vector zero
  apply injective
  rw [map_zero]
  ext index
  exact zero index

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
