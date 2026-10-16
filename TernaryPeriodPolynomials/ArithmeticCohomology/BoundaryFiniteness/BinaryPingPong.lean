module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.BinaryPingPong

open scoped Pointwise

variable {A B G X : Type} [Group A] [Group B] [Group G] [MulAction G X]

abbrev family (A B : Type) : Bool → Type
  | false => A
  | true => B

instance familyGroup : (i : Bool) → Group (family A B i)
  | false => inferInstanceAs (Group A)
  | true => inferInstanceAs (Group B)

def toIndexed : Monoid.Coprod A B →* Monoid.CoprodI (family A B) :=
  Monoid.Coprod.lift (Monoid.CoprodI.of (M := family A B) (i := false))
    (Monoid.CoprodI.of (M := family A B) (i := true))

def fromIndexed : Monoid.CoprodI (family A B) →* Monoid.Coprod A B :=
  Monoid.CoprodI.lift fun i => match i with
    | false => Monoid.Coprod.inl
    | true => Monoid.Coprod.inr

theorem fromIndexed_toIndexed :
    (fromIndexed (A := A) (B := B)).comp toIndexed = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext <;> ext x <;> simp [fromIndexed, toIndexed]

theorem toIndexed_injective : Function.Injective (toIndexed (A := A) (B := B)) := by
  have inverse : Function.LeftInverse (fromIndexed (A := A) (B := B)) toIndexed :=
    fun x => DFunLike.congr_fun fromIndexed_toIndexed x
  exact inverse.injective

def indexedMap (left : A →* G) (right : B →* G) :
    (i : Bool) → family A B i →* G
  | false => left
  | true => right

theorem indexedMap_comp (left : A →* G) (right : B →* G) :
    (Monoid.CoprodI.lift (indexedMap left right)).comp toIndexed =
      Monoid.Coprod.lift left right := by
  apply Monoid.Coprod.hom_ext <;> ext x <;> simp [toIndexed, indexedMap]

theorem lift_injective (left : A →* G) (right : B →* G)
    (cardinal : 3 ≤ Cardinal.mk B) (positive negative : Set X)
    (positive_nonempty : positive.Nonempty) (negative_nonempty : negative.Nonempty)
    (disjoint : Disjoint positive negative)
    (left_action : ∀ a : A, a ≠ 1 → left a • negative ⊆ positive)
    (right_action : ∀ b : B, b ≠ 1 → right b • positive ⊆ negative) :
    Function.Injective (Monoid.Coprod.lift left right) := by
  let domains : Bool → Set X := fun i => if i then negative else positive
  have nonempty : ∀ i, (domains i).Nonempty := by
    intro i
    cases i
    · exact positive_nonempty
    · exact negative_nonempty
  have pairwise : Pairwise (Function.onFun Disjoint domains) := by
    intro i j different
    cases i <;> cases j
    · exact (different rfl).elim
    · exact disjoint
    · exact disjoint.symm
    · exact (different rfl).elim
  have pingpong : Pairwise fun i j => ∀ h : family A B i, h ≠ 1 →
      indexedMap left right i h • domains j ⊆ domains i := by
    intro i j different
    cases i <;> cases j
    · exact (different rfl).elim
    · exact left_action
    · exact right_action
    · exact (different rfl).elim
  have injective := Monoid.CoprodI.lift_injective_of_ping_pong
    (indexedMap left right) (Or.inr ⟨true, cardinal⟩) domains nonempty pairwise pingpong
  rw [← indexedMap_comp]
  exact injective.comp toIndexed_injective

end TernaryPeriodPolynomials.BoundaryFiniteness.BinaryPingPong
