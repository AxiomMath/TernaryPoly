module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
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


noncomputable section
namespace TernaryPoly.SelfAdjointProjection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A duality criterion for surjectivity of a projected subspace. No diagonalizability is assumed. -/
theorem rangeRestrict_comp_surjective
    (B : LinearMap.BilinForm K V)
    (hsep : ∀ p, (∀ q,B p q=0) → p=0) (hsurj : Function.Surjective B)
    (P Q : Module.End K V)
    (hP : ∀ p q,B (P p) q=B p (P q))
    (hQ : ∀ p q,B (Q p) q=B p (Q q))
    (hQQ : ∀ p,Q (Q p)=Q p)
    (hdisjoint : ∀ p,Q p=p → P p=0 → p=0) :
    Function.Surjective (Q.rangeRestrict.comp P) := by
  rw [←LinearMap.range_eq_top,←Submodule.dualAnnihilator_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro φ hφ
  obtain ⟨p,hp⟩ := hsurj (φ.comp Q.rangeRestrict)
  have he (v : V) : B p v=φ (Q.rangeRestrict v) := by
    exact congrArg (fun f : Module.Dual K V => f v) hp
  have hfix : Q p=p := by
    have hz : Q p-p=0 := by
      apply hsep
      intro v
      rw [map_sub,LinearMap.sub_apply,hQ,he,he]
      have hh : Q.rangeRestrict (Q v)=Q.rangeRestrict v := by
        apply Subtype.ext
        exact hQQ v
      rw [hh,sub_self]
    exact sub_eq_zero.mp hz
  have hker : P p=0 := by
    apply hsep
    intro v
    rw [hP,he]
    exact (Submodule.mem_dualAnnihilator _).mp hφ _ ⟨v,rfl⟩
  have hp0 := hdisjoint p hfix hker
  apply LinearMap.ext
  intro q
  obtain ⟨v,hv⟩ := q.property
  have hh : Q.rangeRestrict v=q := Subtype.ext hv
  have hz := he v
  rw [hp0,map_zero,LinearMap.zero_apply,hh] at hz
  exact hz.symm

end TernaryPoly.SelfAdjointProjection
