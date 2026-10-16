module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A commuting family on a nonzero finite dimensional complex space has a common eigenvector. -/
theorem commuting_family_exists_eigenvector {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (operators : ι → Module.End ℂ V)
    (commutes : ∀ first second, Commute (operators first) (operators second)) :
    ∃ (vector : V) (eigenvalues : ι → ℂ), vector ≠ 0 ∧
      ∀ index, operators index vector = eigenvalues index • vector := by
  classical
  let invariant (space : Submodule ℂ V) : Prop :=
    ∀ index vector, vector ∈ space → operators index vector ∈ space
  have exists_rank : ∃ dimension : ℕ, ∃ space : Submodule ℂ V,
      space ≠ ⊥ ∧ invariant space ∧ Module.finrank ℂ space = dimension :=
    ⟨Module.finrank ℂ (⊤ : Submodule ℂ V), ⊤, top_ne_bot,
      fun _ _ _ => Submodule.mem_top, rfl⟩
  obtain ⟨space, nonzero, stable, rank_eq⟩ := Nat.find_spec exists_rank
  let : Nontrivial space := Submodule.nontrivial_iff_ne_bot.mpr nonzero
  have scalar_action (index : ι) : ∃ scalar : ℂ, ∀ vector ∈ space,
      operators index vector = scalar • vector := by
    let restricted : Module.End ℂ space := (operators index).restrict (stable index)
    obtain ⟨scalar, eigenvalue⟩ := restricted.exists_eigenvalue
    obtain ⟨eigenvector, eigen⟩ := eigenvalue.exists_hasEigenvector
    let smaller := space ⊓ (operators index).eigenspace scalar
    have smaller_nonzero : smaller ≠ ⊥ := by
      intro zero
      have member : eigenvector.val ∈ smaller := ⟨eigenvector.property,
        Module.End.mem_eigenspace_iff.mpr (congrArg Subtype.val eigen.apply_eq_smul)⟩
      rw [zero, Submodule.mem_bot] at member
      exact eigen.2 (Subtype.ext member)
    have smaller_stable : invariant smaller := by
      intro other vector member
      refine ⟨stable other vector member.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
      have equal := DFunLike.congr_fun (commutes index other).eq vector
      change operators index (operators other vector) = operators other (operators index vector) at equal
      rw [equal, Module.End.mem_eigenspace_iff.mp member.2, map_smul]
    have rank_le : Module.finrank ℂ space ≤ Module.finrank ℂ smaller := by
      rw [rank_eq]
      exact Nat.find_min' exists_rank ⟨smaller, smaller_nonzero, smaller_stable, rfl⟩
    have smaller_eq : smaller = space := Submodule.eq_of_le_of_finrank_le inf_le_left rank_le
    refine ⟨scalar, fun vector member => Module.End.mem_eigenspace_iff.mp ?_⟩
    exact ((show vector ∈ smaller from smaller_eq.symm ▸ member)).2
  choose eigenvalues action using scalar_action
  obtain ⟨vector, vector_nonzero⟩ := exists_ne (0 : space)
  exact ⟨vector.val, eigenvalues, fun zero => vector_nonzero (Subtype.ext zero),
    fun index => action index vector.val vector.property⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
