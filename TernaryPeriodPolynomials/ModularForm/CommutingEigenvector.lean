module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
namespace TernaryPoly.CommutingEigenvector

variable {K V I : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Every nonzero stable subspace of an arbitrary commuting family contains a common eigenvector.
The index type need not be finite, and no semisimplicity assumption is used. -/
theorem exists_common (T : I → Module.End K V) (hc : ∀ i j, Commute (T i) (T j))
    (L : Submodule K V) (hL : L ≠ ⊥) (hs : ∀ i x, x ∈ L → T i x ∈ L) :
    ∃ v : V, v ∈ L ∧ v ≠ 0 ∧ ∀ i, ∃ a : K, T i v = a • v := by
  classical
  let S : Set (Submodule K V) := {W | W ≠ ⊥ ∧ W ≤ L ∧ ∀ i x, x ∈ W → T i x ∈ W}
  obtain ⟨W,hW,hmin⟩ := IsArtinian.set_has_minimal S ⟨L,hL,le_rfl,hs⟩
  obtain ⟨hW0,hWL,hWT⟩ := hW
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  refine ⟨w.val,hWL w.property,?_,?_⟩
  · intro hz
    exact hw (Subtype.ext hz)
  · intro i
    let A : Module.End K W := (T i).restrict (hWT i)
    obtain ⟨a,ha⟩ := A.exists_eigenvalue
    obtain ⟨v,hv⟩ := ha.exists_hasEigenvector
    let Q : Submodule K V := W ⊓ (T i).eigenspace a
    have hv0 : v.val ≠ 0 := by
      intro h
      exact hv.2 (Subtype.ext h)
    have hvQ : v.val ∈ Q := by
      refine ⟨v.property,Module.End.mem_eigenspace_iff.mpr ?_⟩
      exact congrArg Subtype.val hv.apply_eq_smul
    have hQ : Q ∈ S := by
      refine ⟨?_,inf_le_left.trans hWL,?_⟩
      · intro hz
        rw [hz] at hvQ
        exact hv0 ((Submodule.mem_bot K).mp hvQ)
      · intro j x hx
        refine ⟨hWT j x hx.1,Module.End.mem_eigenspace_iff.mpr ?_⟩
        have he := Module.End.mem_eigenspace_iff.mp hx.2
        have hij : T i (T j x) = T j (T i x) := LinearMap.congr_fun (hc i j).eq x
        rw [hij,he,map_smul]
    have heq : Q=W := by
      apply le_antisymm inf_le_left
      by_contra h
      exact hmin Q hQ (lt_of_le_not_ge inf_le_left h)
    refine ⟨a,Module.End.mem_eigenspace_iff.mp ?_⟩
    have hwQ : w.val ∈ Q := heq.ge w.property
    exact hwQ.2

/-- Nonvanishing on common eigenvectors detects every stable subspace through a single functional. -/
theorem eq_bot_of_functional (T : I → Module.End K V) (hc : ∀ i j, Commute (T i) (T j))
    (ell : V →ₗ[K] K)
    (hdetect : ∀ v : V, v ≠ 0 → (∀ i, ∃ a : K, T i v = a • v) → ell v ≠ 0)
    (L : Submodule K V) (hs : ∀ i x, x ∈ L → T i x ∈ L)
    (hzero : ∀ x ∈ L, ell x = 0) : L=⊥ := by
  by_contra hL
  obtain ⟨v,hv,hv0,he⟩ := exists_common T hc L hL hs
  exact hdetect v hv0 he (hzero v hv)

end TernaryPoly.CommutingEigenvector
