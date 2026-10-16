module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteEvaluation

/-- A finite-dimensional function space is determined by finitely many evaluations. -/
theorem exists_samples {Scalars Vector Point : Type*} [Field Scalars]
    [AddCommGroup Vector] [Module Scalars Vector] [FiniteDimensional Scalars Vector]
    (realization : Vector →ₗ[Scalars] (Point → Scalars)) (injective : Function.Injective realization) :
    ∃ samples : Finset Point, ∀ vector : Vector,
      (∀ point ∈ samples, realization vector point = 0) → vector = 0 := by
  classical
  let evaluation : Point → Module.Dual Scalars Vector := fun point => (LinearMap.proj point).comp realization
  obtain ⟨functionals, contained, _, spanEquality, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn Scalars (Set.range evaluation)
  have representatives (functional : ↥functionals) : ∃ point, evaluation point = functional.val :=
    contained functional.property
  choose points pointsEquality using representatives
  let samples := functionals.attach.image points
  refine ⟨samples, ?_⟩
  intro vector vanishing
  have generatorsVanish : ∀ functional ∈ functionals, functional vector = 0 := by
    intro functional membership
    have pointMember : points ⟨functional, membership⟩ ∈ samples :=
      Finset.mem_image.mpr ⟨⟨functional, membership⟩, Finset.mem_attach _ _, rfl⟩
    have equality := vanishing _ pointMember
    change evaluation (points ⟨functional, membership⟩) vector = 0 at equality
    rw [pointsEquality] at equality
    exact equality
  have spanVanish : Submodule.span Scalars (functionals : Set (Module.Dual Scalars Vector)) ≤
      LinearMap.ker (LinearMap.applyₗ vector) :=
    Submodule.span_le.mpr generatorsVanish
  apply injective
  funext point
  have membership : evaluation point ∈ Submodule.span Scalars (Set.range evaluation) :=
    Submodule.subset_span ⟨point, rfl⟩
  rw [← spanEquality] at membership
  have equality := spanVanish membership
  change realization vector point = 0 at equality
  simpa only [map_zero, Pi.zero_apply] using equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteEvaluation
