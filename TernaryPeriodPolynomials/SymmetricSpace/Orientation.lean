module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceOrientation
open Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Coordinates := Fin 6 → ℝ

/-- The actual real symmetric matrices as a linear subspace of all 3x3 matrices. -/
def symmetricSubmodule : Submodule ℝ Mat3 where
  carrier := {S | S.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun r _ hS => hS.smul r

abbrev Symmetric := symmetricSubmodule

/-- Lexicographic entries, with the diagonal in positions 0,3,5. -/
def coordinates : Symmetric →ₗ[ℝ] Coordinates where
  toFun S := ![S.val 0 0,S.val 0 1,S.val 0 2,S.val 1 1,S.val 1 2,S.val 2 2]
  map_add' S T := by ext i; fin_cases i <;> rfl
  map_smul' r S := by ext i; fin_cases i <;> rfl

/-- Every coordinate, including all three off-diagonal coordinates, enters literally. -/
def fromCoordinates : Coordinates →ₗ[ℝ] Symmetric where
  toFun x := ⟨!![x 0,x 1,x 2;x 1,x 3,x 4;x 2,x 4,x 5], by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  map_add' x y := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' r x := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem coordinates_from (x : Coordinates) : coordinates (fromCoordinates x) = x := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem from_coordinates (S : Symmetric) : fromCoordinates (coordinates S) = S := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first | rfl | exact S.property.apply _ _

/-- The six-dimensional coordinate equivalence of the actual symmetric-matrix space. -/
def coordinatesEquiv : Symmetric ≃ₗ[ℝ] Coordinates :=
  LinearEquiv.ofLinearMap coordinates fromCoordinates
    (by apply LinearMap.ext; intro x; exact coordinates_from x) (by apply LinearMap.ext; intro x; exact from_coordinates x)

/-- Actual congruence by any real 3x3 matrix, defined before assuming invertibility. -/
def congruence (g : Mat3) : Symmetric →ₗ[ℝ] Symmetric where
  toFun S := ⟨g*S.val*g.transpose,by
    change (g*S.val*g.transpose).transpose = g*S.val*g.transpose
    rw [transpose_mul,transpose_mul,transpose_transpose,S.property]
    exact (Matrix.mul_assoc _ _ _).symm⟩
  map_add' S T := by
    apply Subtype.ext
    change g*(S.val+T.val)*g.transpose = g*S.val*g.transpose+g*T.val*g.transpose
    rw [Matrix.mul_add,Matrix.add_mul]
  map_smul' r S := by
    apply Subtype.ext
    change g*(r • S.val)*g.transpose = r • (g*S.val*g.transpose)
    rw [Matrix.mul_smul,Matrix.smul_mul]

@[simp] theorem congruence_apply (g : Mat3) (S : Symmetric) :
    (congruence g S).val = g*S.val*g.transpose := rfl

@[simp] theorem congruence_one : congruence (1 : Mat3) = LinearMap.id := by
  ext S : 1
  apply Subtype.ext
  simp only [congruence_apply,transpose_one,Matrix.one_mul,Matrix.mul_one,LinearMap.id_apply]

theorem congruence_mul (g h : Mat3) : congruence (g*h) = (congruence g).comp (congruence h) := by
  ext S : 1
  apply Subtype.ext
  change (g*h)*S.val*(g*h).transpose = g*(h*S.val*h.transpose)*g.transpose
  rw [transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The actual action transported through the explicit six-coordinate equivalence. -/
def coordinateAction (g : Mat3) : Coordinates →ₗ[ℝ] Coordinates :=
  coordinates.comp ((congruence g).comp fromCoordinates)

@[simp] theorem coordinateAction_one : coordinateAction (1 : Mat3) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change coordinates (congruence 1 (fromCoordinates x)) = x
  rw [congruence_one,LinearMap.id_apply,coordinates_from]

theorem coordinateAction_mul (g h : Mat3) :
    coordinateAction (g*h) = (coordinateAction g).comp (coordinateAction h) := by
  apply LinearMap.ext
  intro x
  change coordinates (congruence (g*h) (fromCoordinates x)) =
    coordinates (congruence g (fromCoordinates (coordinates (congruence h (fromCoordinates x)))))
  rw [from_coordinates,congruence_mul]
  rfl

/-- The genuine GL3 action on symmetric matrices. -/
def symmetricAction : Matrix.GeneralLinearGroup (Fin 3) ℝ →* Module.End ℝ Symmetric where
  toFun g := congruence g.val
  map_one' := congruence_one
  map_mul' g h := congruence_mul g.val h.val

/-- The same genuine action in six explicit coordinates. -/
def action : Matrix.GeneralLinearGroup (Fin 3) ℝ →* Module.End ℝ Coordinates where
  toFun g := coordinateAction g.val
  map_one' := coordinateAction_one
  map_mul' g h := coordinateAction_mul g.val h.val

end TernaryPoly.SymmetricSpaceOrientation
