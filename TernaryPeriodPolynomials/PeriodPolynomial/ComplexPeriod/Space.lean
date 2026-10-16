module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination
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
namespace TernaryPoly.BinaryComplexPeriod

/-- The literal four period equations, over any coefficient field. -/
def Relations (K : Type*) [Field K] (q : MvPolynomial (Fin 2) K) : Prop :=
  bind₁ ![X 1,X 0] q=q ∧ bind₁ ![-X 0,X 1] q=-q ∧
    bind₁ ![X 0,-X 1] q=-q ∧ q-bind₁ ![X 0-X 1,X 1] q+bind₁ ![X 0,X 0-X 1] q=0

/-- The equations define an actual linear subspace; no period-map surjectivity is built into it. -/
def periods (K : Type*) [Field K] : Submodule K (MvPolynomial (Fin 2) K) where
  carrier := {q | Relations K q}
  zero_mem' := by simp [Relations]
  add_mem' := by
    intro p q hp hq
    refine ⟨?_,?_,?_,?_⟩
    · rw [map_add,hp.1,hq.1]
    · rw [map_add,hp.2.1,hq.2.1,neg_add]
    · rw [map_add,hp.2.2.1,hq.2.2.1,neg_add]
    · simp only [map_add]
      linear_combination hp.2.2.2 + hq.2.2.2
  smul_mem' := by
    intro c p hp
    refine ⟨?_,?_,?_,?_⟩
    · rw [map_smul,hp.1]
    · rw [map_smul,hp.2.1,smul_neg]
    · rw [map_smul,hp.2.2.1,smul_neg]
    · rw [map_smul,map_smul,←smul_sub,←smul_add,hp.2.2.2,smul_zero]

/-- The degree-d period space consists of actual homogeneous binary polynomials. -/
def space (K : Type*) [Field K] (d : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  homogeneousSubmodule (Fin 2) K d ⊓ periods K

instance (K : Type*) [Field K] (d : ℕ) : FiniteDimensional K (space K d) := by
  let : FiniteDimensional K (homogeneousSubmodule (Fin 2) K d) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) K d)
  exact Submodule.finiteDimensional_of_le (show space K d ≤ homogeneousSubmodule (Fin 2) K d from inf_le_left)

private theorem map_vec2 {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    (a b : MvPolynomial (Fin 2) K) :
    (fun i => map φ (![a,b] i))=![map φ a,map φ b] := by
  funext i
  fin_cases i <;> rfl

/-- Literal period equations survive coefficient extension. -/
theorem map_relations {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    (q : MvPolynomial (Fin 2) K) (hq : Relations K q) : Relations F (map φ q) := by
  refine ⟨?_,?_,?_,?_⟩
  · have h := congrArg (map φ) hq.1
    simpa only [map_bind₁,map_vec2,map_X] using h
  · have h := congrArg (map φ) hq.2.1
    simpa only [map_bind₁,map_vec2,map_X,map_neg] using h
  · have h := congrArg (map φ) hq.2.2.1
    simpa only [map_bind₁,map_vec2,map_X,map_neg] using h
  · have h := congrArg (map φ) hq.2.2.2
    simpa only [map_bind₁,map_vec2,map_X,map_sub,map_add,map_zero] using h

/-- Coefficient extension is an actual map into the literal homogeneous period space. -/
def extend {K F : Type*} [Field K] [Field F] (φ : K →+* F) (d : ℕ)
    (q : space K d) : space F d :=
  ⟨map φ q.val,q.property.1.map φ,map_relations φ q.val q.property.2⟩

/-- Coefficient extension over fields is faithful on the actual period polynomials. -/
theorem extend_injective {K F : Type*} [Field K] [Field F] (φ : K →+* F) (d : ℕ) :
    Function.Injective (extend φ d) := by
  intro q r h
  apply Subtype.ext
  exact map_injective φ φ.injective (congrArg Subtype.val h)

/-- The extreme coefficient is a genuine linear functional on the fixed-degree period space. -/
def extreme (K : Type*) [Field K] (d : ℕ) : space K d →ₗ[K] K :=
  (lcoeff K (Finsupp.single 0 1+Finsupp.single 1 (d-1))).comp (space K d).subtype

@[simp] theorem extreme_extend {K F : Type*} [Field K] [Field F]
    (φ : K →+* F) (d : ℕ) (q : space K d) :
    extreme F d (extend φ d q)=φ (extreme K d q) := coeff_map _ _ _

end TernaryPoly.BinaryComplexPeriod
