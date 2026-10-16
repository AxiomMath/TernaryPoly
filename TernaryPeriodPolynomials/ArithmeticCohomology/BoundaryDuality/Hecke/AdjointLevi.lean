module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.FiniteSupport.Basic
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
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Peel

@[expose] public section


/-!
# Hecke adjointness of a Levi pairing and the eigenvalue it forces on the dual side

Let `π : X × Y → ℂ` be a bilinear pairing of the Levi cohomology groups (for instance the parabolic
cup pairing on `H¹(Γ_M, Sym^m ⊗ det^e) × H¹(Γ_M, Sym^m ⊗ det^{e'})`), and `S`, `S'` Hecke operators
on `X`, `Y`. Say `S'` is a `κ`-adjoint of `S` if `π (S x) y = κ · π x (S' y)`. For the Hecke
operators `T_p` of a Levi quotient the double coset `Γ diag(1, p) Γ` is carried to itself, up to a
central scalar, by `g ↦ g⁻¹`; this is the source of the adjointness relation (with `κ` a power of
`p` determined by the weights).

The edge maps of the local cohomology at a cusp intertwine the local Hecke operator `A` with the
Levi operator through an affine relation `E(A y) = a · E y + s · S (E y)` (`a = 1` at the untwisted
cusps, `a = ±1` at the sign-twisted ones). If `x = E(y)` comes from an eigenvector, `A y = c y`,
then `a x + s S x = c x`, so `S x = ((c - a)/s) x`. On the dual side with edge `E'`,
`E'(A' w) = a' E' w + s' S' (E' w)`, the adjointness gives, for all `w`,

  `π x (E'(A' w)) = (a' + s' (c - a) / (s κ)) · π x (E' w)`:

the functional `π x (E' ·)` is an eigenfunctional of the dual local operator `A'` with the single
eigenvalue `a' + s' (c - a) / (s κ)`. For `a = a' = 1`, `s' = s / p` and `κ = p⁻¹` this eigenvalue is
`c` again, which is the consistency condition for the pair character.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLevi

/-- **`κ`-adjointness.** The operator `S'` on `Y` is a `κ`-adjoint of `S` on `X` for the pairing
`π`: `π (S x) y = κ · π x (S' y)`. -/
def IsHeckeAdjoint {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (π : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (S : Module.End ℂ X) (S' : Module.End ℂ Y) (κ : ℂ) : Prop :=
  ∀ x y, π (S x) y = κ * π x (S' y)

/-- **The dual eigenvalue.** If `a x + s S x = c x` on the line side, the dual operator acts on
the pairing functional by `a' + s' (c - a) / (s κ)`. -/
def dualEigenvalue (a s a' s' κ c : ℂ) : ℂ :=
  a' + s' * (c - a) / (s * κ)

/-- **Operator form.** If the dual local operator acts on the edge through an operator `Q'` on `Y`
(`g (A' w) = Q' (g w)`), `Q'` is adjoint to an operator `Q` on `X` for `π`, and `x` is an eigenvector
of `Q` with eigenvalue `μ`, then the functional `π x (g ·)` is an eigenfunctional of `A'` with
eigenvalue `μ`. This is the form to use for correspondences whose edge formula is a polynomial in
the Levi Hecke operator rather than an affine function of it. -/
theorem pairing_eigen_of_adjoint {X Y W : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] [AddCommGroup W] [Module ℂ W] (π : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (Q : Module.End ℂ X)
    (Q' : Module.End ℂ Y) (hadj : ∀ x y, π (Q x) y = π x (Q' y)) (g : W →ₗ[ℂ] Y)
    (A' : Module.End ℂ W) (hg : ∀ w, g (A' w) = Q' (g w)) {x : X} {μ : ℂ} (hx : Q x = μ • x)
    (w : W) : π x (g (A' w)) = μ * π x (g w) := by
  rw [hg w, ← hadj, hx]
  simp

/-- **An eigenvector has an eigen-edge.** If the edge map satisfies `f (A v) = a f(v) + s S (f v)`
and `A v = c v`, then `a f(v) + s S (f v) = c f(v)`. -/
theorem edge_eigen_relation {V X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup X]
    [Module ℂ X] (f : V →ₗ[ℂ] X) (A : Module.End ℂ V) (S : Module.End ℂ X) (a s c : ℂ)
    (hf : ∀ v, f (A v) = a • f v + s • S (f v)) {v : V} (hv : A v = c • v) :
    a • f v + s • S (f v) = c • f v := by
  rw [← hf, hv, map_smul]

/-- **The pairing functional of an eigen-edge is an eigenfunctional of the dual operator.**
Let `S'` be a `κ`-adjoint of `S` for `π`, `a x + s S x = c x`, and
`g (A' w) = a' g(w) + s' S' (g w)` for all `w`. Then
`π x (g (A' w)) = (a' + s' (c - a)/(s κ)) · π x (g w)`. -/
theorem pairing_eigen_of_edge {X Y W : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] [AddCommGroup W] [Module ℂ W] (π : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (S : Module.End ℂ X)
    (S' : Module.End ℂ Y) (κ : ℂ) (hadj : IsHeckeAdjoint π S S' κ) (g : W →ₗ[ℂ] Y)
    (A' : Module.End ℂ W) (a s a' s' c : ℂ) (hs : s ≠ 0) (hκ : κ ≠ 0)
    (hg : ∀ w, g (A' w) = a' • g w + s' • S' (g w)) {x : X} (hx : a • x + s • S x = c • x)
    (w : W) : π x (g (A' w)) = dualEigenvalue a s a' s' κ c * π x (g w) := by
  have h1 : a * π x (g w) + s * π (S x) (g w) = c * π x (g w) := by
    have h := congrArg (fun z => π z (g w)) hx
    simpa using h
  have h2 : π (S x) (g w) = κ * π x (S' (g w)) := hadj x (g w)
  have hQ : π x (S' (g w)) * (s * κ) = (c - a) * π x (g w) := by
    linear_combination h1 - s * h2
  have hQ' : π x (S' (g w)) = (c - a) * π x (g w) / (s * κ) := by
    rw [eq_div_iff (mul_ne_zero hs hκ)]
    exact hQ
  have e1 : π x (g (A' w)) = a' * π x (g w) + s' * π x (S' (g w)) := by
    rw [hg w]
    simp
  rw [e1, hQ']
  unfold dualEigenvalue
  ring

/-- **Consistency of the dual eigenvalue.** If `a = a'` and `s' = s κ`, the dual eigenvalue of `c`
is `a + (c - a) = c` itself. -/
theorem dualEigenvalue_self {a s s' κ : ℂ} (c : ℂ) (hs : s ≠ 0) (hκ : κ ≠ 0)
    (h : s' = s * κ) : dualEigenvalue a s a s' κ c = c := by
  have hsk : s * κ ≠ 0 := mul_ne_zero hs hκ
  have e : s * κ * (c - a) / (s * κ) = c - a := by
    rw [div_eq_iff hsk]
    ring
  unfold dualEigenvalue
  rw [h, e]
  ring

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLevi
