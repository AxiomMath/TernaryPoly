module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteEvaluationMap {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (realize : V →ₗ[ℂ] (ι → ℂ)) (points : Finset ι) : V →ₗ[ℂ] (points → ℂ) where
  toFun vector point := realize vector point.val
  map_add' first second := by ext point; simp
  map_smul' scalar vector := by ext point; simp

theorem finiteEvaluationMap_exists_injective {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (realize : V →ₗ[ℂ] (ι → ℂ)) (injective : Function.Injective realize) :
    ∃ points : Finset ι, Function.Injective (finiteEvaluationMap realize points) := by
  classical
  have exists_rank : ∃ rank : ℕ, ∃ points : Finset ι,
      Module.finrank ℂ (finiteEvaluationMap realize points).ker = rank :=
    ⟨_, ∅, rfl⟩
  obtain ⟨points, rank_eq⟩ := Nat.find_spec exists_rank
  refine ⟨points, LinearMap.ker_eq_bot.mp ?_⟩
  apply le_antisymm ?_ bot_le
  intro vector member
  change vector = 0
  apply injective
  rw [map_zero]
  funext point
  have inclusion : (finiteEvaluationMap realize (insert point points)).ker ≤
      (finiteEvaluationMap realize points).ker := by
    intro value value_mem
    apply LinearMap.mem_ker.mpr
    ext index
    exact congrFun (LinearMap.mem_ker.mp value_mem) ⟨index.val, Finset.mem_insert_of_mem index.property⟩
  have rank_le : Module.finrank ℂ (finiteEvaluationMap realize points).ker ≤
      Module.finrank ℂ (finiteEvaluationMap realize (insert point points)).ker := by
    rw [rank_eq]
    exact Nat.find_min' exists_rank ⟨insert point points, rfl⟩
  have equal := Submodule.eq_of_le_of_finrank_le inclusion rank_le
  have inserted : vector ∈ (finiteEvaluationMap realize (insert point points)).ker := equal.symm ▸ member
  exact congrFun (LinearMap.mem_ker.mp inserted) ⟨point, Finset.mem_insert_self _ _⟩

theorem analyticAt_of_separating_evaluations {V ι E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (realize : V →ₗ[ℂ] (ι → ℂ)) (injective : Function.Injective realize)
    (function : E → V) (point : E)
    (analytic : ∀ index : ι, AnalyticAt ℂ (fun input => realize (function input) index) point) :
    AnalyticAt ℂ function point := by
  obtain ⟨points, sample_injective⟩ := finiteEvaluationMap_exists_injective realize injective
  let sample := finiteEvaluationMap realize points
  have sample_analytic : AnalyticAt ℂ (fun input => sample (function input)) point :=
    analyticAt_pi_iff.mpr (fun index => analytic index.val)
  have equality : (fun input => (LinearMap.toContinuousLinearMap sample.leftInverse) (sample (function input))) =
      function := by
    funext input
    exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr sample_injective) (function input)
  rw [← equality]
  exact ((LinearMap.toContinuousLinearMap sample.leftInverse).analyticAt _).comp sample_analytic

end TernaryPeriodPolynomials.SphericalDetection.Helpers
