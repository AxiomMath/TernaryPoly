module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryHomogeneous

variable (K : Type*) [Field K]
abbrev H (d : ℕ) := homogeneousSubmodule (Fin 2) K d

/-- The exponent of X^i Y^(d-i), with the index bound built into its type. -/
def exponent (d : ℕ) (i : Fin (d+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.val+Finsupp.single 1 (d-i.val)

@[simp] theorem exponent_zero (d : ℕ) (i : Fin (d+1)) : exponent d i 0=i.val := by
  simp [exponent]
@[simp] theorem exponent_one (d : ℕ) (i : Fin (d+1)) : exponent d i 1=d-i.val := by
  simp [exponent]

theorem exponent_injective (d : ℕ) : Function.Injective (exponent d) := by
  intro i j h
  apply Fin.ext
  simpa using congrArg (fun m => m 0) h

theorem degree_two (m : Fin 2 →₀ ℕ) : m.degree=m 0+m 1 := by
  change m.sum (fun _ k => k)=_
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_succ]
  · intro i
    rfl

@[simp] theorem exponent_degree (d : ℕ) (i : Fin (d+1)) : (exponent d i).degree=d := by
  rw [degree_two,exponent_zero,exponent_one]
  omega

/-- Every binary homogeneous exponent has its unique bounded first-coordinate index. -/
theorem exponent_of_degree (d : ℕ) (m : Fin 2 →₀ ℕ) (hm : m.degree=d) :
    ∃ i : Fin (d+1),exponent d i=m := by
  have hd := degree_two m
  let i : Fin (d+1) := ⟨m 0,by omega⟩
  refine ⟨i,?_⟩
  ext j
  fin_cases j
  · simp [i]
  · simp [exponent,i]
    omega

/-- Literal coefficient coordinates on the fixed homogeneous space. -/
def coordinates (d : ℕ) : H K d →ₗ[K] (Fin (d+1) → K) where
  toFun q i := q.val.coeff (exponent d i)
  map_add' q r := by funext i; exact rfl
  map_smul' a q := by funext i; exact coeff_smul _ _ _

/-- The inverse monomial expansion is a homogeneous polynomial, for all degrees including zero. -/
def polynomial (d : ℕ) : (Fin (d+1) → K) →ₗ[K] H K d where
  toFun v := ⟨∑ i,monomial (exponent d i) (v i),by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_monomial _ (exponent_degree d i)⟩
  map_add' v w := by
    apply Subtype.ext
    simp only [Pi.add_apply,Submodule.coe_add,map_add,Finset.sum_add_distrib]
  map_smul' a v := by
    apply Subtype.ext
    simp only [Pi.smul_apply,Submodule.coe_smul,smul_monomial,Finset.smul_sum,RingHom.id_apply]

@[simp] theorem coordinates_polynomial (d : ℕ) (v : Fin (d+1) → K) :
    coordinates K d (polynomial K d v)=v := by
  classical
  funext i
  change (∑ j,monomial (exponent d j) (v j)).coeff (exponent d i)=v i
  rw [coeff_sum,Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [coeff_monomial,ite_eq_right (fun h => hj (exponent_injective d h))]
  · simp

@[simp] theorem polynomial_coordinates (d : ℕ) (q : H K d) :
    polynomial K d (coordinates K d q)=q := by
  apply Subtype.ext
  ext m
  by_cases hm : m.degree=d
  · obtain ⟨i,rfl⟩ := exponent_of_degree d m hm
    exact congrFun (coordinates_polynomial K d (coordinates K d q)) i
  · rw [(polynomial K d (coordinates K d q)).property.coeff_eq_zero hm,q.property.coeff_eq_zero hm]

/-- The actual homogeneous polynomial coefficient equivalence. -/
def coefficientEquiv (d : ℕ) : H K d ≃ₗ[K] (Fin (d+1) → K) where
  toFun := coordinates K d
  invFun := polynomial K d
  left_inv := polynomial_coordinates K d
  right_inv := coordinates_polynomial K d
  map_add' := (coordinates K d).map_add
  map_smul' := (coordinates K d).map_smul

end TernaryPoly.BinaryHomogeneous
