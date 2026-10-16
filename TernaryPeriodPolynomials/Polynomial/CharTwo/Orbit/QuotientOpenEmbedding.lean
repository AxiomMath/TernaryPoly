module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.Topology.WithTopology

@[expose] public section


noncomputable section
namespace TernaryPoly.OrbitQuotientOpenEmbedding
open Topology

variable {G E F : Type*} [Group G] [MulAction G E] [MulAction G F]

/-- The actual map on orbit quotients induced by an equivariant map. -/
def descend (f : E → F) (heq : ∀ (g : G) (x : E), f (g • x) = g • f x) :
    Quotient (MulAction.orbitRel G E) → Quotient (MulAction.orbitRel G F) :=
  Quotient.map f fun x y h => by
    obtain ⟨g,hg⟩ := h
    exact ⟨g,(heq g y).symm.trans (congrArg f hg)⟩

@[simp] theorem descend_mk (f : E → F) (heq : ∀ (g : G) (x : E), f (g • x) = g • f x) (x : E) :
    descend f heq (Quotient.mk _ x) = Quotient.mk _ (f x) := rfl

theorem descend_injective {f : E → F} (heq : ∀ (g : G) (x : E), f (g • x) = g • f x)
    (hf : Function.Injective f) : Function.Injective (descend f heq) := by
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      intro h
      obtain ⟨g,hg⟩ := Quotient.exact h
      apply Quotient.sound
      exact ⟨g,hf ((heq g y).trans hg)⟩

variable [TopologicalSpace E] [TopologicalSpace F]

theorem descend_continuous {f : E → F} (heq : ∀ (g : G) (x : E), f (g • x) = g • f x)
    (hf : Continuous f) : Continuous (descend f heq) :=
  continuous_quot_lift _ (continuous_quot_mk.comp hf)

theorem descend_isOpenMap [ContinuousConstSMul G F] {f : E → F}
    (heq : ∀ (g : G) (x : E), f (g • x) = g • f x) (hf : IsOpenMap f) :
    IsOpenMap (descend f heq) := by
  intro U hU
  let qE : E → Quotient (MulAction.orbitRel G E) := Quotient.mk _
  let qF : F → Quotient (MulAction.orbitRel G F) := Quotient.mk _
  have he : descend f heq '' U = qF '' (f '' (qE ⁻¹' U)) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
      exact ⟨f x,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨qE x,hx,rfl⟩
  rw [he]
  exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap _
    (hf _ (continuous_quot_mk.isOpen_preimage U hU))

/-- Equivariant open embeddings induce genuine open embeddings of orbit spaces. -/
theorem descend_isOpenEmbedding [ContinuousConstSMul G F] {f : E → F}
    (heq : ∀ (g : G) (x : E), f (g • x) = g • f x) (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (descend f heq) :=
  .of_continuous_injective_isOpenMap (descend_continuous heq hf.continuous)
    (descend_injective heq hf.injective) (descend_isOpenMap heq hf.isOpenMap)

end TernaryPoly.OrbitQuotientOpenEmbedding
