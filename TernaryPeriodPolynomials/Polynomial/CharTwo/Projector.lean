module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
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
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoProjector

abbrev Poly := MvPolynomial (Fin 3) (ZMod 2)

def sub (f a b c : Poly) : Poly := bind₁ ![a,b,c] f

def form : ℕ → Poly
  | 1 => X 0
  | 2 => X 1
  | 3 => X 0+X 1
  | 4 => X 2
  | 5 => X 0+X 2
  | 6 => X 1+X 2
  | 7 => X 0+X 1+X 2
  | _ => 0

def atom (f : Poly) (a b c : ℕ) : Poly := sub f (form a) (form b) (form c)

def norm (f : Poly) : Poly := f + sub f (X 1) (X 0+X 1) (X 2) +
  sub f (X 0+X 1) (X 0) (X 2)

private theorem sub_comp (f a b c x y z : Poly) :
    sub (sub f a b c) x y z = sub f (sub a x y z) (sub b x y z) (sub c x y z) := by
  simp only [sub, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- The literal norm equation can be evaluated in arbitrary polynomial arguments. -/
theorem sub_norm_zero {f : Poly} (hn : norm f = 0) (a b c : Poly) :
    sub f a b c + sub f b (a+b) c + sub f (a+b) a c = 0 := by
  have h := congrArg (fun p => sub p a b c) hn
  have hadd (p q : Poly) : sub (p+q) a b c = sub p a b c+sub q a b c := by
    exact map_add (bind₁ ![a,b,c]) p q
  simp only [norm, hadd, sub_comp] at h
  simpa [sub] using h

/-- Full symmetry is expressed by the two generating coordinate substitutions. -/
structure Symmetric (f : Poly) : Prop where
  cyclic : sub f (X 1) (X 2) (X 0) = f
  swap : sub f (X 1) (X 0) (X 2) = f

theorem sub_cycle {f : Poly} (hs : Symmetric f) (a b c : Poly) :
    sub f b c a = sub f a b c := by
  have h := congrArg (fun p => sub p a b c) hs.cyclic
  rw [sub_comp] at h
  simpa [sub] using h

theorem sub_swap {f : Poly} (hs : Symmetric f) (a b c : Poly) :
    sub f b a c = sub f a b c := by
  have h := congrArg (fun p => sub p a b c) hs.swap
  rw [sub_comp] at h
  simpa [sub] using h

/-- The six literal argument permutations leave a symmetric polynomial unchanged. -/
theorem sub_permutations {f : Poly} (hs : Symmetric f) (a b c : Poly) :
    sub f b a c = sub f a b c ∧ sub f b c a = sub f a b c ∧
    sub f c a b = sub f a b c ∧ sub f a c b = sub f a b c ∧
    sub f c b a = sub f a b c := by
  refine ⟨sub_swap hs a b c, sub_cycle hs a b c, ?_, ?_, ?_⟩
  · exact (sub_cycle hs b c a).trans (sub_cycle hs a b c)
  · exact (sub_cycle hs b a c).trans (sub_swap hs a b c)
  · exact (sub_swap hs b c a).trans (sub_cycle hs a b c)










/-- Symmetry applied to the seven nonzero binary linear forms. -/
theorem atom_permutations {f : Poly} (hs : Symmetric f) (a b c : ℕ) :
    atom f b a c = atom f a b c ∧ atom f b c a = atom f a b c ∧
    atom f c a b = atom f a b c ∧ atom f a c b = atom f a b c ∧
    atom f c b a = atom f a b c :=
  sub_permutations hs (form a) (form b) (form c)

/-- A substituted norm equation, with the binary sum of its two rows explicit. -/
theorem atom_norm_zero {f : Poly} (hn : norm f = 0) (a b c d : ℕ)
    (hab : form a+form b = form d) :
    atom f a b c+atom f b d c+atom f d a c = 0 := by
  have h := sub_norm_zero hn (form a) (form b) (form c)
  rw [hab] at h
  exact h

/-- The literal eighteen-substitution operator, using sorted row representatives. -/
def projector (f : Poly) : Poly :=
  atom f 1 2 5 +
  atom f 1 2 6 +
  atom f 1 3 4 +
  atom f 1 3 6 +
  atom f 1 3 7 +
  atom f 1 4 6 +
  atom f 1 5 6 +
  atom f 1 5 7 +
  atom f 2 3 4 +
  atom f 2 3 5 +
  atom f 2 3 7 +
  atom f 2 4 5 +
  atom f 2 5 6 +
  atom f 2 6 7 +
  atom f 3 4 5 +
  atom f 3 4 6 +
  atom f 4 5 7 +
  atom f 4 6 7

/-- Eleven literal translated norm equations prove that the projector fixes the norm kernel. -/
theorem projector_eq_of_norm {f : Poly} (hs : Symmetric f) (hn : norm f = 0) :
    projector f = f := by
  have h143 : atom f 1 4 3 = atom f 1 3 4 :=
    (atom_permutations hs 1 3 4).2.2.2.1
  have h162 : atom f 1 6 2 = atom f 1 2 6 :=
    (atom_permutations hs 1 2 6).2.2.2.1
  have h164 : atom f 1 6 4 = atom f 1 4 6 :=
    (atom_permutations hs 1 4 6).2.2.2.1
  have h241 : atom f 2 4 1 = atom f 1 2 4 :=
    (atom_permutations hs 1 2 4).2.1
  have h243 : atom f 2 4 3 = atom f 2 3 4 :=
    (atom_permutations hs 2 3 4).2.2.2.1
  have h315 : atom f 3 1 5 = atom f 1 3 5 :=
    (atom_permutations hs 1 3 5).1
  have h316 : atom f 3 1 6 = atom f 1 3 6 :=
    (atom_permutations hs 1 3 6).1
  have h317 : atom f 3 1 7 = atom f 1 3 7 :=
    (atom_permutations hs 1 3 7).1
  have h453 : atom f 4 5 3 = atom f 3 4 5 :=
    (atom_permutations hs 3 4 5).2.1
  have h461 : atom f 4 6 1 = atom f 1 4 6 :=
    (atom_permutations hs 1 4 6).2.1
  have h463 : atom f 4 6 3 = atom f 3 4 6 :=
    (atom_permutations hs 3 4 6).2.1
  have h465 : atom f 4 6 5 = atom f 4 5 6 :=
    (atom_permutations hs 4 5 6).2.2.2.1
  have h513 : atom f 5 1 3 = atom f 1 3 5 :=
    (atom_permutations hs 1 3 5).2.2.1
  have h516 : atom f 5 1 6 = atom f 1 5 6 :=
    (atom_permutations hs 1 5 6).1
  have h517 : atom f 5 1 7 = atom f 1 5 7 :=
    (atom_permutations hs 1 5 7).1
  have h621 : atom f 6 2 1 = atom f 1 2 6 :=
    (atom_permutations hs 1 2 6).2.2.2.2
  have h623 : atom f 6 2 3 = atom f 2 3 6 :=
    (atom_permutations hs 2 3 6).2.2.1
  have h625 : atom f 6 2 5 = atom f 2 5 6 :=
    (atom_permutations hs 2 5 6).2.2.1
  have h672 : atom f 6 7 2 = atom f 2 6 7 :=
    (atom_permutations hs 2 6 7).2.1
  have h674 : atom f 6 7 4 = atom f 4 6 7 :=
    (atom_permutations hs 4 6 7).2.1
  have h712 : atom f 7 1 2 = atom f 1 2 7 :=
    (atom_permutations hs 1 2 7).2.2.1
  have h714 : atom f 7 1 4 = atom f 1 4 7 :=
    (atom_permutations hs 1 4 7).2.2.1
  have e0 := atom_norm_zero hn 1 2 5 3 (by simp [form])
  simp only [h315] at e0
  have e1 := atom_norm_zero hn 1 2 6 3 (by simp [form])
  simp only [h316] at e1
  have e2 := atom_norm_zero hn 1 2 7 3 (by simp [form])
  simp only [h317] at e2
  have e3 := atom_norm_zero hn 1 4 3 5 (by simp [form])
  simp only [h143, h453, h513] at e3
  have e4 := atom_norm_zero hn 1 4 6 5 (by simp [form])
  simp only [h516] at e4
  have e5 := atom_norm_zero hn 1 4 7 5 (by simp [form])
  simp only [h517] at e5
  have e6 := atom_norm_zero hn 1 6 2 7 (by simp [form]; ring)
  simp only [h162, h672, h712] at e6
  have e7 := atom_norm_zero hn 1 6 4 7 (by simp [form]; ring)
  simp only [h164, h674, h714] at e7
  have e8 := atom_norm_zero hn 2 4 1 6 (by simp [form])
  simp only [h241, h461, h621] at e8
  have e9 := atom_norm_zero hn 2 4 3 6 (by simp [form])
  simp only [h243, h463, h623] at e9
  have e10 := atom_norm_zero hn 2 4 5 6 (by simp [form])
  simp only [h465, h625] at e10
  have hi : atom f 1 2 4 = f := by
    simp only [atom, form, sub]
    have hv : (![X 0,X 1,X 2] : Fin 3 → Poly) = X := by funext i; fin_cases i <;> rfl
    simp only [hv, bind₁_X_left, AlgHom.id_apply]
  unfold projector
  conv_rhs => rw [← hi]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10


private theorem sub_add (f g a b c : Poly) :
    sub (f+g) a b c = sub f a b c+sub g a b c := map_add (bind₁ ![a,b,c]) f g

private def rowMap_norm1 (i : Fin 8) : ℕ := ![0, 2, 3, 1, 4, 6, 7, 5] i

private theorem form_sub_norm1 (i : Fin 8) :
    sub (form i) (form 2) (form 3) (form 4) = form (rowMap_norm1 i) := by
  fin_cases i <;> simp [form, sub, rowMap_norm1] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem atom_sub_norm1 (f : Poly) (a b c : Fin 8) :
    sub (atom f a b c) (form 2) (form 3) (form 4) = atom f (rowMap_norm1 a) (rowMap_norm1 b) (rowMap_norm1 c) := by
  unfold atom
  rw [sub_comp, form_sub_norm1, form_sub_norm1, form_sub_norm1]

private theorem projector_sub_norm1 (f : Poly) :
    sub (projector f) (form 2) (form 3) (form 4) =
      atom f 2 3 6 +
      atom f 2 3 7 +
      atom f 2 1 4 +
      atom f 2 1 7 +
      atom f 2 1 5 +
      atom f 2 4 7 +
      atom f 2 6 7 +
      atom f 2 6 5 +
      atom f 3 1 4 +
      atom f 3 1 6 +
      atom f 3 1 5 +
      atom f 3 4 6 +
      atom f 3 6 7 +
      atom f 3 7 5 +
      atom f 1 4 6 +
      atom f 1 4 7 +
      atom f 4 6 5 +
      atom f 4 7 5 := by
  have e0 : sub (atom f 1 2 5) (form 2) (form 3) (form 4) = atom f 2 3 6 := atom_sub_norm1 f 1 2 5
  have e1 : sub (atom f 1 2 6) (form 2) (form 3) (form 4) = atom f 2 3 7 := atom_sub_norm1 f 1 2 6
  have e2 : sub (atom f 1 3 4) (form 2) (form 3) (form 4) = atom f 2 1 4 := atom_sub_norm1 f 1 3 4
  have e3 : sub (atom f 1 3 6) (form 2) (form 3) (form 4) = atom f 2 1 7 := atom_sub_norm1 f 1 3 6
  have e4 : sub (atom f 1 3 7) (form 2) (form 3) (form 4) = atom f 2 1 5 := atom_sub_norm1 f 1 3 7
  have e5 : sub (atom f 1 4 6) (form 2) (form 3) (form 4) = atom f 2 4 7 := atom_sub_norm1 f 1 4 6
  have e6 : sub (atom f 1 5 6) (form 2) (form 3) (form 4) = atom f 2 6 7 := atom_sub_norm1 f 1 5 6
  have e7 : sub (atom f 1 5 7) (form 2) (form 3) (form 4) = atom f 2 6 5 := atom_sub_norm1 f 1 5 7
  have e8 : sub (atom f 2 3 4) (form 2) (form 3) (form 4) = atom f 3 1 4 := atom_sub_norm1 f 2 3 4
  have e9 : sub (atom f 2 3 5) (form 2) (form 3) (form 4) = atom f 3 1 6 := atom_sub_norm1 f 2 3 5
  have e10 : sub (atom f 2 3 7) (form 2) (form 3) (form 4) = atom f 3 1 5 := atom_sub_norm1 f 2 3 7
  have e11 : sub (atom f 2 4 5) (form 2) (form 3) (form 4) = atom f 3 4 6 := atom_sub_norm1 f 2 4 5
  have e12 : sub (atom f 2 5 6) (form 2) (form 3) (form 4) = atom f 3 6 7 := atom_sub_norm1 f 2 5 6
  have e13 : sub (atom f 2 6 7) (form 2) (form 3) (form 4) = atom f 3 7 5 := atom_sub_norm1 f 2 6 7
  have e14 : sub (atom f 3 4 5) (form 2) (form 3) (form 4) = atom f 1 4 6 := atom_sub_norm1 f 3 4 5
  have e15 : sub (atom f 3 4 6) (form 2) (form 3) (form 4) = atom f 1 4 7 := atom_sub_norm1 f 3 4 6
  have e16 : sub (atom f 4 5 7) (form 2) (form 3) (form 4) = atom f 4 6 5 := atom_sub_norm1 f 4 5 7
  have e17 : sub (atom f 4 6 7) (form 2) (form 3) (form 4) = atom f 4 7 5 := atom_sub_norm1 f 4 6 7
  simp only [projector, sub_add, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]

private def rowMap_norm2 (i : Fin 8) : ℕ := ![0, 3, 1, 2, 4, 7, 5, 6] i

private theorem form_sub_norm2 (i : Fin 8) :
    sub (form i) (form 3) (form 1) (form 4) = form (rowMap_norm2 i) := by
  fin_cases i <;> simp [form, sub, rowMap_norm2] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem atom_sub_norm2 (f : Poly) (a b c : Fin 8) :
    sub (atom f a b c) (form 3) (form 1) (form 4) = atom f (rowMap_norm2 a) (rowMap_norm2 b) (rowMap_norm2 c) := by
  unfold atom
  rw [sub_comp, form_sub_norm2, form_sub_norm2, form_sub_norm2]

private theorem projector_sub_norm2 (f : Poly) :
    sub (projector f) (form 3) (form 1) (form 4) =
      atom f 3 1 7 +
      atom f 3 1 5 +
      atom f 3 2 4 +
      atom f 3 2 5 +
      atom f 3 2 6 +
      atom f 3 4 5 +
      atom f 3 7 5 +
      atom f 3 7 6 +
      atom f 1 2 4 +
      atom f 1 2 7 +
      atom f 1 2 6 +
      atom f 1 4 7 +
      atom f 1 7 5 +
      atom f 1 5 6 +
      atom f 2 4 7 +
      atom f 2 4 5 +
      atom f 4 7 6 +
      atom f 4 5 6 := by
  have e0 : sub (atom f 1 2 5) (form 3) (form 1) (form 4) = atom f 3 1 7 := atom_sub_norm2 f 1 2 5
  have e1 : sub (atom f 1 2 6) (form 3) (form 1) (form 4) = atom f 3 1 5 := atom_sub_norm2 f 1 2 6
  have e2 : sub (atom f 1 3 4) (form 3) (form 1) (form 4) = atom f 3 2 4 := atom_sub_norm2 f 1 3 4
  have e3 : sub (atom f 1 3 6) (form 3) (form 1) (form 4) = atom f 3 2 5 := atom_sub_norm2 f 1 3 6
  have e4 : sub (atom f 1 3 7) (form 3) (form 1) (form 4) = atom f 3 2 6 := atom_sub_norm2 f 1 3 7
  have e5 : sub (atom f 1 4 6) (form 3) (form 1) (form 4) = atom f 3 4 5 := atom_sub_norm2 f 1 4 6
  have e6 : sub (atom f 1 5 6) (form 3) (form 1) (form 4) = atom f 3 7 5 := atom_sub_norm2 f 1 5 6
  have e7 : sub (atom f 1 5 7) (form 3) (form 1) (form 4) = atom f 3 7 6 := atom_sub_norm2 f 1 5 7
  have e8 : sub (atom f 2 3 4) (form 3) (form 1) (form 4) = atom f 1 2 4 := atom_sub_norm2 f 2 3 4
  have e9 : sub (atom f 2 3 5) (form 3) (form 1) (form 4) = atom f 1 2 7 := atom_sub_norm2 f 2 3 5
  have e10 : sub (atom f 2 3 7) (form 3) (form 1) (form 4) = atom f 1 2 6 := atom_sub_norm2 f 2 3 7
  have e11 : sub (atom f 2 4 5) (form 3) (form 1) (form 4) = atom f 1 4 7 := atom_sub_norm2 f 2 4 5
  have e12 : sub (atom f 2 5 6) (form 3) (form 1) (form 4) = atom f 1 7 5 := atom_sub_norm2 f 2 5 6
  have e13 : sub (atom f 2 6 7) (form 3) (form 1) (form 4) = atom f 1 5 6 := atom_sub_norm2 f 2 6 7
  have e14 : sub (atom f 3 4 5) (form 3) (form 1) (form 4) = atom f 2 4 7 := atom_sub_norm2 f 3 4 5
  have e15 : sub (atom f 3 4 6) (form 3) (form 1) (form 4) = atom f 2 4 5 := atom_sub_norm2 f 3 4 6
  have e16 : sub (atom f 4 5 7) (form 3) (form 1) (form 4) = atom f 4 7 6 := atom_sub_norm2 f 4 5 7
  have e17 : sub (atom f 4 6 7) (form 3) (form 1) (form 4) = atom f 4 5 6 := atom_sub_norm2 f 4 6 7
  simp only [projector, sub_add, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]

private def rowMap_cycle (i : Fin 8) : ℕ := ![0, 2, 4, 6, 1, 3, 5, 7] i

private theorem form_sub_cycle (i : Fin 8) :
    sub (form i) (form 2) (form 4) (form 1) = form (rowMap_cycle i) := by
  fin_cases i <;> simp [form, sub, rowMap_cycle] <;> ring_nf

private theorem atom_sub_cycle (f : Poly) (a b c : Fin 8) :
    sub (atom f a b c) (form 2) (form 4) (form 1) = atom f (rowMap_cycle a) (rowMap_cycle b) (rowMap_cycle c) := by
  unfold atom
  rw [sub_comp, form_sub_cycle, form_sub_cycle, form_sub_cycle]

private theorem projector_sub_cycle (f : Poly) :
    sub (projector f) (form 2) (form 4) (form 1) =
      atom f 2 4 3 +
      atom f 2 4 5 +
      atom f 2 6 1 +
      atom f 2 6 5 +
      atom f 2 6 7 +
      atom f 2 1 5 +
      atom f 2 3 5 +
      atom f 2 3 7 +
      atom f 4 6 1 +
      atom f 4 6 3 +
      atom f 4 6 7 +
      atom f 4 1 3 +
      atom f 4 3 5 +
      atom f 4 5 7 +
      atom f 6 1 3 +
      atom f 6 1 5 +
      atom f 1 3 7 +
      atom f 1 5 7 := by
  have e0 : sub (atom f 1 2 5) (form 2) (form 4) (form 1) = atom f 2 4 3 := atom_sub_cycle f 1 2 5
  have e1 : sub (atom f 1 2 6) (form 2) (form 4) (form 1) = atom f 2 4 5 := atom_sub_cycle f 1 2 6
  have e2 : sub (atom f 1 3 4) (form 2) (form 4) (form 1) = atom f 2 6 1 := atom_sub_cycle f 1 3 4
  have e3 : sub (atom f 1 3 6) (form 2) (form 4) (form 1) = atom f 2 6 5 := atom_sub_cycle f 1 3 6
  have e4 : sub (atom f 1 3 7) (form 2) (form 4) (form 1) = atom f 2 6 7 := atom_sub_cycle f 1 3 7
  have e5 : sub (atom f 1 4 6) (form 2) (form 4) (form 1) = atom f 2 1 5 := atom_sub_cycle f 1 4 6
  have e6 : sub (atom f 1 5 6) (form 2) (form 4) (form 1) = atom f 2 3 5 := atom_sub_cycle f 1 5 6
  have e7 : sub (atom f 1 5 7) (form 2) (form 4) (form 1) = atom f 2 3 7 := atom_sub_cycle f 1 5 7
  have e8 : sub (atom f 2 3 4) (form 2) (form 4) (form 1) = atom f 4 6 1 := atom_sub_cycle f 2 3 4
  have e9 : sub (atom f 2 3 5) (form 2) (form 4) (form 1) = atom f 4 6 3 := atom_sub_cycle f 2 3 5
  have e10 : sub (atom f 2 3 7) (form 2) (form 4) (form 1) = atom f 4 6 7 := atom_sub_cycle f 2 3 7
  have e11 : sub (atom f 2 4 5) (form 2) (form 4) (form 1) = atom f 4 1 3 := atom_sub_cycle f 2 4 5
  have e12 : sub (atom f 2 5 6) (form 2) (form 4) (form 1) = atom f 4 3 5 := atom_sub_cycle f 2 5 6
  have e13 : sub (atom f 2 6 7) (form 2) (form 4) (form 1) = atom f 4 5 7 := atom_sub_cycle f 2 6 7
  have e14 : sub (atom f 3 4 5) (form 2) (form 4) (form 1) = atom f 6 1 3 := atom_sub_cycle f 3 4 5
  have e15 : sub (atom f 3 4 6) (form 2) (form 4) (form 1) = atom f 6 1 5 := atom_sub_cycle f 3 4 6
  have e16 : sub (atom f 4 5 7) (form 2) (form 4) (form 1) = atom f 1 3 7 := atom_sub_cycle f 4 5 7
  have e17 : sub (atom f 4 6 7) (form 2) (form 4) (form 1) = atom f 1 5 7 := atom_sub_cycle f 4 6 7
  simp only [projector, sub_add, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]

private def rowMap_swap (i : Fin 8) : ℕ := ![0, 2, 1, 3, 4, 6, 5, 7] i

private theorem form_sub_swap (i : Fin 8) :
    sub (form i) (form 2) (form 1) (form 4) = form (rowMap_swap i) := by
  fin_cases i <;> simp [form, sub, rowMap_swap] <;> ring_nf

private theorem atom_sub_swap (f : Poly) (a b c : Fin 8) :
    sub (atom f a b c) (form 2) (form 1) (form 4) = atom f (rowMap_swap a) (rowMap_swap b) (rowMap_swap c) := by
  unfold atom
  rw [sub_comp, form_sub_swap, form_sub_swap, form_sub_swap]

private theorem projector_sub_swap (f : Poly) :
    sub (projector f) (form 2) (form 1) (form 4) =
      atom f 2 1 6 +
      atom f 2 1 5 +
      atom f 2 3 4 +
      atom f 2 3 5 +
      atom f 2 3 7 +
      atom f 2 4 5 +
      atom f 2 6 5 +
      atom f 2 6 7 +
      atom f 1 3 4 +
      atom f 1 3 6 +
      atom f 1 3 7 +
      atom f 1 4 6 +
      atom f 1 6 5 +
      atom f 1 5 7 +
      atom f 3 4 6 +
      atom f 3 4 5 +
      atom f 4 6 7 +
      atom f 4 5 7 := by
  have e0 : sub (atom f 1 2 5) (form 2) (form 1) (form 4) = atom f 2 1 6 := atom_sub_swap f 1 2 5
  have e1 : sub (atom f 1 2 6) (form 2) (form 1) (form 4) = atom f 2 1 5 := atom_sub_swap f 1 2 6
  have e2 : sub (atom f 1 3 4) (form 2) (form 1) (form 4) = atom f 2 3 4 := atom_sub_swap f 1 3 4
  have e3 : sub (atom f 1 3 6) (form 2) (form 1) (form 4) = atom f 2 3 5 := atom_sub_swap f 1 3 6
  have e4 : sub (atom f 1 3 7) (form 2) (form 1) (form 4) = atom f 2 3 7 := atom_sub_swap f 1 3 7
  have e5 : sub (atom f 1 4 6) (form 2) (form 1) (form 4) = atom f 2 4 5 := atom_sub_swap f 1 4 6
  have e6 : sub (atom f 1 5 6) (form 2) (form 1) (form 4) = atom f 2 6 5 := atom_sub_swap f 1 5 6
  have e7 : sub (atom f 1 5 7) (form 2) (form 1) (form 4) = atom f 2 6 7 := atom_sub_swap f 1 5 7
  have e8 : sub (atom f 2 3 4) (form 2) (form 1) (form 4) = atom f 1 3 4 := atom_sub_swap f 2 3 4
  have e9 : sub (atom f 2 3 5) (form 2) (form 1) (form 4) = atom f 1 3 6 := atom_sub_swap f 2 3 5
  have e10 : sub (atom f 2 3 7) (form 2) (form 1) (form 4) = atom f 1 3 7 := atom_sub_swap f 2 3 7
  have e11 : sub (atom f 2 4 5) (form 2) (form 1) (form 4) = atom f 1 4 6 := atom_sub_swap f 2 4 5
  have e12 : sub (atom f 2 5 6) (form 2) (form 1) (form 4) = atom f 1 6 5 := atom_sub_swap f 2 5 6
  have e13 : sub (atom f 2 6 7) (form 2) (form 1) (form 4) = atom f 1 5 7 := atom_sub_swap f 2 6 7
  have e14 : sub (atom f 3 4 5) (form 2) (form 1) (form 4) = atom f 3 4 6 := atom_sub_swap f 3 4 5
  have e15 : sub (atom f 3 4 6) (form 2) (form 1) (form 4) = atom f 3 4 5 := atom_sub_swap f 3 4 6
  have e16 : sub (atom f 4 5 7) (form 2) (form 1) (form 4) = atom f 4 6 7 := atom_sub_swap f 4 5 7
  have e17 : sub (atom f 4 6 7) (form 2) (form 1) (form 4) = atom f 4 5 7 := atom_sub_swap f 4 6 7
  simp only [projector, sub_add, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]

/-- Every output satisfies the exact characteristic-two norm equation. -/
theorem norm_projector {f : Poly} (hs : Symmetric f) : norm (projector f) = 0 := by
  have h175 : atom f 1 7 5 = atom f 1 5 7 :=
    (atom_permutations hs 1 5 7).2.2.2.1
  have h214 : atom f 2 1 4 = atom f 1 2 4 :=
    (atom_permutations hs 1 2 4).1
  have h215 : atom f 2 1 5 = atom f 1 2 5 :=
    (atom_permutations hs 1 2 5).1
  have h217 : atom f 2 1 7 = atom f 1 2 7 :=
    (atom_permutations hs 1 2 7).1
  have h265 : atom f 2 6 5 = atom f 2 5 6 :=
    (atom_permutations hs 2 5 6).2.2.2.1
  have h314 : atom f 3 1 4 = atom f 1 3 4 :=
    (atom_permutations hs 1 3 4).1
  have h315 : atom f 3 1 5 = atom f 1 3 5 :=
    (atom_permutations hs 1 3 5).1
  have h316 : atom f 3 1 6 = atom f 1 3 6 :=
    (atom_permutations hs 1 3 6).1
  have h317 : atom f 3 1 7 = atom f 1 3 7 :=
    (atom_permutations hs 1 3 7).1
  have h324 : atom f 3 2 4 = atom f 2 3 4 :=
    (atom_permutations hs 2 3 4).1
  have h325 : atom f 3 2 5 = atom f 2 3 5 :=
    (atom_permutations hs 2 3 5).1
  have h326 : atom f 3 2 6 = atom f 2 3 6 :=
    (atom_permutations hs 2 3 6).1
  have h375 : atom f 3 7 5 = atom f 3 5 7 :=
    (atom_permutations hs 3 5 7).2.2.2.1
  have h376 : atom f 3 7 6 = atom f 3 6 7 :=
    (atom_permutations hs 3 6 7).2.2.2.1
  have h465 : atom f 4 6 5 = atom f 4 5 6 :=
    (atom_permutations hs 4 5 6).2.2.2.1
  have h475 : atom f 4 7 5 = atom f 4 5 7 :=
    (atom_permutations hs 4 5 7).2.2.2.1
  have h476 : atom f 4 7 6 = atom f 4 6 7 :=
    (atom_permutations hs 4 6 7).2.2.2.1
  change projector f + sub (projector f) (form 2) (form 3) (form 4) +
    sub (projector f) (form 3) (form 1) (form 4) = 0
  rw [projector_sub_norm1, projector_sub_norm2]
  simp only [projector, h175, h214, h215, h217, h265, h314, h315, h316, h317, h324, h325, h326, h375, h376, h465, h475, h476]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The eighteen-term output retains both generating symmetries. -/
theorem symmetric_projector {f : Poly} (hs : Symmetric f) : Symmetric (projector f) := by
  constructor
  · have h215 : atom f 2 1 5 = atom f 1 2 5 :=
      (atom_permutations hs 1 2 5).1
    have h243 : atom f 2 4 3 = atom f 2 3 4 :=
      (atom_permutations hs 2 3 4).2.2.2.1
    have h261 : atom f 2 6 1 = atom f 1 2 6 :=
      (atom_permutations hs 1 2 6).2.1
    have h265 : atom f 2 6 5 = atom f 2 5 6 :=
      (atom_permutations hs 2 5 6).2.2.2.1
    have h413 : atom f 4 1 3 = atom f 1 3 4 :=
      (atom_permutations hs 1 3 4).2.2.1
    have h435 : atom f 4 3 5 = atom f 3 4 5 :=
      (atom_permutations hs 3 4 5).1
    have h461 : atom f 4 6 1 = atom f 1 4 6 :=
      (atom_permutations hs 1 4 6).2.1
    have h463 : atom f 4 6 3 = atom f 3 4 6 :=
      (atom_permutations hs 3 4 6).2.1
    have h613 : atom f 6 1 3 = atom f 1 3 6 :=
      (atom_permutations hs 1 3 6).2.2.1
    have h615 : atom f 6 1 5 = atom f 1 5 6 :=
      (atom_permutations hs 1 5 6).2.2.1
    change sub (projector f) (form 2) (form 4) (form 1) = projector f
    rw [projector_sub_cycle]
    simp only [projector, h215, h243, h261, h265, h413, h435, h461, h463, h613, h615]
    ring
  · have h165 : atom f 1 6 5 = atom f 1 5 6 :=
      (atom_permutations hs 1 5 6).2.2.2.1
    have h215 : atom f 2 1 5 = atom f 1 2 5 :=
      (atom_permutations hs 1 2 5).1
    have h216 : atom f 2 1 6 = atom f 1 2 6 :=
      (atom_permutations hs 1 2 6).1
    have h265 : atom f 2 6 5 = atom f 2 5 6 :=
      (atom_permutations hs 2 5 6).2.2.2.1
    change sub (projector f) (form 2) (form 1) (form 4) = projector f
    rw [projector_sub_swap]
    simp only [projector, h165, h215, h216, h265]
    ring

/-- The actual polynomial projector is idempotent on symmetric inputs. -/
theorem projector_idempotent {f : Poly} (hs : Symmetric f) :
    projector (projector f) = projector f :=
  projector_eq_of_norm (symmetric_projector hs) (norm_projector hs)

end TernaryPoly.CharTwoProjector
