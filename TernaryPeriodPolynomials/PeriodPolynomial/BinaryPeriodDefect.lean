module

public import TernaryPeriodPolynomials.PeriodPolynomial.ComplexPeriod.Space
public import Mathlib.Tactic
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryComplexPeriod

variable (K : Type*) [Field K]
abbrev Poly := MvPolynomial (Fin 2) K

/-- Five literal linear defects encode homogeneity and all four period equations. -/
def defect (d : ℕ) : Poly K →ₗ[K] (Fin 5 → Poly K) :=
  LinearMap.pi ![LinearMap.id-homogeneousComponent d,
    (bind₁ ![X 1,X 0]).toLinearMap-LinearMap.id,
    (bind₁ ![-X 0,X 1]).toLinearMap+LinearMap.id,
    (bind₁ ![X 0,-X 1]).toLinearMap+LinearMap.id,
    LinearMap.id-(bind₁ ![X 0-X 1,X 1]).toLinearMap+
      (bind₁ ![X 0,X 0-X 1]).toLinearMap]

/-- The kernel is exactly the original actual homogeneous period subspace. -/
theorem ker_defect (d : ℕ) : (defect K d).ker=space K d := by
  ext p
  have hh : p-homogeneousComponent d p=0 ↔ p.IsHomogeneous d := by
    constructor
    · intro h
      rw [sub_eq_zero] at h
      rw [h]
      exact homogeneousComponent_isHomogeneous d p
    · intro hp
      rw [homogeneousComponent_eq_self hp,sub_self]
  change defect K d p=0 ↔ p.IsHomogeneous d ∧ Relations K p
  simp only [defect,LinearMap.pi_apply,funext_iff,Pi.zero_apply,
    Fin.forall_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    LinearMap.sub_apply,LinearMap.add_apply,LinearMap.id_apply,AlgHom.toLinearMap_apply,
    hh,Relations,sub_eq_zero,add_eq_zero_iff_eq_neg]
  simp

/-- Homogeneous components commute with actual coefficient extension. -/
theorem map_component {F : Type*} [Field F] (φ : K →+* F) (d : ℕ) (p : Poly K) :
    map φ (homogeneousComponent d p)=homogeneousComponent d (map φ p) := by
  ext m
  simp only [coeff_map,coeff_homogeneousComponent]
  split_ifs <;> simp

private theorem map_tuple {F : Type*} [Field F] (φ : K →+* F) (a b : Poly K) :
    (fun i => map φ (![a,b] i))=![map φ a,map φ b] := by
  funext i
  fin_cases i <;> rfl

/-- The entire literal defect map commutes with coefficient extension, component by component. -/
theorem defect_map {F : Type*} [Field F] (φ : K →+* F) (d : ℕ) (p : Poly K) (i : Fin 5) :
    defect F d (map φ p) i=map φ (defect K d p i) := by
  fin_cases i
  · change map φ p-homogeneousComponent d (map φ p)=map φ (p-homogeneousComponent d p)
    rw [map_sub,map_component]
  · change bind₁ ![X 1,X 0] (map φ p)-map φ p=map φ (bind₁ ![X 1,X 0] p-p)
    simp only [map_sub,map_bind₁,map_tuple,map_X]
  · change bind₁ ![-X 0,X 1] (map φ p)+map φ p=map φ (bind₁ ![-X 0,X 1] p+p)
    simp only [map_add,map_bind₁,map_tuple,map_X,map_neg]
  · change bind₁ ![X 0,-X 1] (map φ p)+map φ p=map φ (bind₁ ![X 0,-X 1] p+p)
    simp only [map_add,map_bind₁,map_tuple,map_X,map_neg]
  · change map φ p-bind₁ ![X 0-X 1,X 1] (map φ p)+bind₁ ![X 0,X 0-X 1] (map φ p)=
      map φ (p-bind₁ ![X 0-X 1,X 1] p+bind₁ ![X 0,X 0-X 1] p)
    simp only [map_add,map_sub,map_bind₁,map_tuple,map_X]

end TernaryPoly.BinaryComplexPeriod
