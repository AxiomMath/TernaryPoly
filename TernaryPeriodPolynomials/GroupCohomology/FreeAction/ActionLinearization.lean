module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
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


noncomputable section
namespace TernaryPoly.FreeActionLinearization

universe v w
variable (G : Type v) (X : Type w) [Group G] [MulAction G X]

abbrev Orbits := Quotient (MulAction.orbitRel G X)

/-- The literal orbit-representative parametrization. -/
def orbitProductMap (p : Orbits G X × G) : X := p.2 • p.1.out

@[simp] theorem orbitProductMap_orbit (p : Orbits G X × G) :
    (⟦orbitProductMap G X p⟧ : Orbits G X)=p.1 := by
  simp [orbitProductMap]

/-- Every point lies in the orbit of the chosen representative of its quotient class. -/
theorem orbitProductMap_surjective : Function.Surjective (orbitProductMap G X) := by
  intro x
  have h : (⟦(⟦x⟧ : Orbits G X).out⟧ : Orbits G X)=⟦x⟧ := Quotient.out_eq _
  obtain ⟨g,hg⟩ := Quotient.exact h
  exact ⟨(⟦x⟧,g⁻¹),by simpa [orbitProductMap] using (inv_smul_eq_iff.mpr hg.symm)⟩

variable [IsCancelSMul G X]

/-- Freeness makes the group coordinate uniquely determined after fixing the orbit. -/
theorem orbitProductMap_injective : Function.Injective (orbitProductMap G X) := by
  rintro ⟨q,g⟩ ⟨r,h⟩ heq
  have hqr : q=r := by
    simpa using congrArg (fun x : X => (⟦x⟧ : Orbits G X)) heq
  subst r
  have hgh : g=h := IsCancelSMul.right_cancel g h q.out heq
  subst h
  rfl

/-- A free action is the disjoint union of literal regular orbits. -/
def orbitProductEquiv : Orbits G X × G ≃ X :=
  Equiv.ofBijective (orbitProductMap G X)
    ⟨orbitProductMap_injective G X,orbitProductMap_surjective G X⟩

@[simp] theorem orbitProductEquiv_apply (q : Orbits G X) (g : G) :
    orbitProductEquiv G X (q,g)=g • q.out := rfl

/-- The group acts on the second coordinate by left multiplication, with orbit fixed. -/
theorem orbitProductEquiv_mul (g h : G) (q : Orbits G X) :
    orbitProductEquiv G X (q,g*h)=g • orbitProductEquiv G X (q,h) := by
  exact mul_smul g h q.out

end TernaryPoly.FreeActionLinearization
