module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G]

def shiftCocycle (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (primitive : representation) :
    groupCohomology.cocycles₁ representation :=
  ⟨fun element => cycle element - (representation.ρ element primitive - primitive), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    have identity := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first second
    change cycle (first * second) = representation.ρ first (cycle second) + cycle first at identity
    simp only [identity, map_mul, Module.End.mul_apply, map_sub]
    abel⟩

theorem shiftCocycle_apply (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (primitive : representation) (element : G) :
    shiftCocycle representation cycle primitive element =
      cycle element - (representation.ρ element primitive - primitive) := rfl

theorem shiftCocycle_H1 (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (primitive : representation) :
    groupCohomology.H1π representation (shiftCocycle representation cycle primitive) =
      groupCohomology.H1π representation cycle := by
  symm
  apply sub_eq_zero.mp
  rw [← map_sub, groupCohomology.H1π_eq_zero_iff]
  refine ⟨primitive, ?_⟩
  funext element
  change representation.ρ element primitive - primitive =
    cycle element - (cycle element - (representation.ρ element primitive - primitive))
  abel

theorem shiftCocycle_involution (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (element : G) (involution : element * element = 1) :
    shiftCocycle representation cycle (-(2 : ℂ)⁻¹ • cycle element) element = 0 := by
  have identity := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property element element
  change cycle (element * element) = representation.ρ element (cycle element) + cycle element at identity
  rw [involution, groupCohomology.cocycles₁_map_one] at identity
  have negative : representation.ρ element (cycle element) = -cycle element :=
    eq_neg_of_add_eq_zero_left identity.symm
  rw [shiftCocycle_apply, map_smul, negative]
  module

theorem cocycle_normalizer_fixed (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation)
    (first normalizer second : G) (commutation : first * normalizer = normalizer * second)
    (first_zero : cycle first = 0) (second_zero : cycle second = 0) :
    representation.ρ first (cycle normalizer) = cycle normalizer := by
  have left := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first normalizer
  have right := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property normalizer second
  change cycle (first * normalizer) = representation.ρ first (cycle normalizer) + cycle first at left
  change cycle (normalizer * second) = representation.ρ normalizer (cycle second) + cycle normalizer at right
  rw [commutation, first_zero, add_zero] at left
  rw [second_zero, map_zero, zero_add] at right
  exact left.symm.trans right

theorem shiftCocycle_zero_of_fixed (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (primitive : representation) (element : G)
    (cycle_zero : cycle element = 0) (fixed : representation.ρ element primitive = primitive) :
    shiftCocycle representation cycle primitive element = 0 := by
  rw [shiftCocycle_apply, cycle_zero, fixed, sub_self, sub_self]

theorem cocycle_right_eq_of_zero (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (first second : G)
    (second_zero : cycle second = 0) : cycle (first * second) = cycle first := by
  have identity := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property first second
  change cycle (first * second) = representation.ρ first (cycle second) + cycle first at identity
  simpa only [second_zero, map_zero, zero_add] using identity

theorem cocycle_mul_eq_zero (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (first second : G)
    (first_zero : cycle first = 0) (second_zero : cycle second = 0) : cycle (first * second) = 0 :=
  (cocycle_right_eq_of_zero representation cycle first second second_zero).trans first_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
