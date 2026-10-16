module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Analysis.Normed.MulAction
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
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Peel
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Change of generating matrices over `ℤ_p` (core of `IsLatticePerm`)

Formalized by Claude Haiku 5.5.

If the columns of `A` lie in the `ℤ_p`-span of the columns of `B`, and the columns of `B` lie in
the `ℤ_p`-span of the columns of `A`, and both determinants are units in `ℚ_p`, then `A = B · C`
for some `C ∈ GL₂(ℤ_p)`. This is the step that turns "`y · A_Λ` and `A_{yΛ}` generate the same
lattice" into "`y · A_Λ = A_{yΛ} · w` with `w ∈ GL₂(ℤ_p)`".

Proved here: `exists_gl_of_span`. Not proved here (remaining for item (1)): the lattice-level
input (that the columns of `A_Λ` generate `Λ`, and that `Λ ↦ kΛ` permutes the index-`p^r`
lattices), and the transport of `ι_p(C)` into `binaryIntegralFinite`.
-/

open PadicInt

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange

variable {p : ℕ} [Fact p.Prime]

/-- The coercion `ℤ_[p] → ℚ_[p]` as a ring homomorphism. -/
def cq : ℤ_[p] →+* ℚ_[p] where
  toFun x := (x : ℚ_[p])
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cq_injective : Function.Injective (cq (p := p)) :=
  fun _ _ h => PadicInt.ext h

/-- **Change of generating matrices.** The columns of `A` and `B` lie in each other's
`ℤ_p`-span, and `det A` is a unit. Then `A = B · C` for some `C ∈ GL₂(ℤ_p)`. -/
theorem exists_gl_of_span (A B : Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hA : IsUnit A.det)
    (hAB : ∀ j : Fin 2, ∃ c : Fin 2 → ℤ_[p], ∀ i : Fin 2, A i j = ∑ k, B i k * (c k : ℚ_[p]))
    (hBA : ∀ j : Fin 2, ∃ d : Fin 2 → ℤ_[p], ∀ i : Fin 2, B i j = ∑ k, A i k * (d k : ℚ_[p])) :
    ∃ C : (Matrix (Fin 2) (Fin 2) ℤ_[p])ˣ, A = B * C.val.map cq := by
  choose c hc using hAB
  choose d hd using hBA
  let C : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j => c j i
  let D : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j => d j i
  have hBC : A = B * C.map cq := by
    ext i j
    rw [hc j i, Matrix.mul_apply]
    rfl
  have hAD : B = A * D.map cq := by
    ext i j
    rw [hd j i, Matrix.mul_apply]
    rfl
  have hA' : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDC_q : (D * C).map cq = 1 := by
    have key : A = A * ((D * C).map cq) := by
      calc A = B * C.map cq := hBC
        _ = (A * D.map cq) * C.map cq := by rw [← hAD]
        _ = A * (D.map cq * C.map cq) := Matrix.mul_assoc _ _ _
        _ = A * ((D * C).map cq) := by rw [Matrix.map_mul]
    have h1 : A * 1 = A * ((D * C).map cq) := by
      rw [Matrix.mul_one]
      exact key
    exact (hA'.mul_left_cancel h1).symm
  have hDC : D * C = 1 := by
    apply Matrix.map_injective cq_injective
    show (D * C).map cq = (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map cq
    rw [hDC_q, Matrix.map_one _ (map_zero cq) (map_one cq)]
  have hCD : C * D = 1 := mul_eq_one_comm.mp hDC
  exact ⟨⟨C, D, hCD, hDC⟩, hBC⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange
