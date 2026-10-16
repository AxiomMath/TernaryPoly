module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
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
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Linear selection of a section on a subspace

Let `coords : G →ₗ Y × X` be a linear map, `S ≤ X` a subspace and `P ≤ Y` a subspace, and suppose
that for every `x ∈ S` there is `g` with `coords g = (p, x)`, `p ∈ P`. Then there is one linear map
`T : X →ₗ Y` such that for every `x ∈ S`, `T x ∈ P` and `coords g = (T x, x)` for some `g`. (Choose
`g` on a basis of `S` and extend linearly; `x ↦ T x` is the first coordinate of the linear
extension.) Used to package the plane coordinates of the dual series into the single linear map
`T^∨` of `ar:eq:dualconstantterms`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

theorem exists_linear_selection {G X Y : Type} [AddCommGroup G] [Module ℂ G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (coords : G →ₗ[ℂ] Y × X) (S : Submodule ℂ X) (P : Submodule ℂ Y)
    (hex : ∀ x ∈ S, ∃ g : G, (coords g).1 ∈ P ∧ (coords g).2 = x) :
    ∃ T : X →ₗ[ℂ] Y, ∀ x ∈ S, T x ∈ P ∧ ∃ g : G, coords g = (T x, x) := by
  choose! ch hch1 hch2 using hex
  let b := Module.Basis.ofVectorSpace ℂ S
  let Λ : S →ₗ[ℂ] G := b.constr ℂ (fun i => ch (b i : X))
  let TS' : S →ₗ[ℂ] P := b.constr ℂ (fun i => (⟨(coords (ch (b i : X))).1, hch1 _ (b i).2⟩ : P))
  let TS : S →ₗ[ℂ] Y := P.subtype.comp TS'
  have hcoord : coords.comp Λ = LinearMap.prod TS S.subtype := by
    apply b.ext
    intro i
    have h1 : Λ (b i) = ch (b i : X) := b.constr_basis ℂ _ i
    have h2 : TS' (b i) = ⟨(coords (ch (b i : X))).1, hch1 _ (b i).2⟩ := b.constr_basis ℂ _ i
    change coords (Λ (b i)) = (P.subtype (TS' (b i)), (b i : X))
    rw [h1, h2]
    exact Prod.ext rfl (hch2 _ (b i).2)
  obtain ⟨T, hT⟩ := LinearMap.exists_extend TS
  refine ⟨T, fun x hx => ?_⟩
  have hTx : T x = TS ⟨x, hx⟩ := by
    rw [← hT]
    rfl
  refine ⟨?_, Λ ⟨x, hx⟩, ?_⟩
  · rw [hTx]
    exact (TS' ⟨x, hx⟩).2
  · rw [hTx]
    exact congrArg (fun f => f ⟨x, hx⟩) hcoord

end TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
