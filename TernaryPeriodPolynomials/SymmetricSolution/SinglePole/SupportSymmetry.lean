module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SupportSymmetry
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SinglePoleSupport
open ModThreeGoodAction OrdinaryResidueSupport PrimitiveLineHeight

/-- The three literal coordinate signs, encoded as integral diagonal entries. -/
def signEntry (s : Fin 3 → Bool) (i : Fin 3) : ℤ := if s i then -1 else 1

theorem sign_diagonal_square (s : Fin 3 → Bool) :
    diagonal (signEntry s) * diagonal (signEntry s) = (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  rw [diagonal_mul_diagonal]
  have h : (fun i => signEntry s i * signEntry s i) = fun _ => (1 : ℤ) := by
    funext i
    cases hs : s i <;> simp [signEntry,hs]
  rw [h,diagonal_one]

/-- Actual integral coordinate-sign matrix, with its literal inverse. -/
def signMatrix (s : Fin 3 → Bool) : IntegralGL :=
  ⟨diagonal (signEntry s),diagonal (signEntry s),sign_diagonal_square s,sign_diagonal_square s⟩

/-- Actual integral permutation matrix with v*P = v∘π for row vectors. -/
def permutationMatrix (π : Equiv.Perm (Fin 3)) : IntegralGL :=
  ⟨(π⁻¹).permMatrix ℤ,π.permMatrix ℤ,
    by rw [← permMatrix_mul,mul_inv_cancel,permMatrix_one],
    by rw [← permMatrix_mul,inv_mul_cancel,permMatrix_one]⟩

/-- The actual normal-line action of a diagonal sign matrix. -/
theorem rowAction_signMatrix (s : Fin 3 → Bool) (H : Normal) :
    rowAction (signMatrix s) H = signNormal s H := by
  apply (normalOfRow_eq_iff _ _).mpr
  left
  change Matrix.vecMul (primitiveGenerator H) (diagonal (signEntry s)) = signRow s (primitiveGenerator H)
  funext i
  rw [vecMul_diagonal]
  cases hs : s i <;> simp [signEntry,signRow,hs]

/-- The actual normal-line action of a permutation matrix, with the precise row convention. -/
theorem rowAction_permutationMatrix (π : Equiv.Perm (Fin 3)) (H : Normal) :
    rowAction (permutationMatrix π) H = permuteNormal π H := by
  apply (normalOfRow_eq_iff _ _).mpr
  left
  change Matrix.vecMul (primitiveGenerator H) ((π⁻¹).permMatrix ℤ) = permuteRow π (primitiveGenerator H)
  rw [vecMul_permMatrix]
  rfl

/-- The literal scalar by which a separately odd coefficient transforms under all coordinate signs. -/
def oddSign (s : Fin 3 → Bool) : ℚ := ∏ i, (signEntry s i : ℚ)

theorem oddSign_ne_zero (s : Fin 3 → Bool) : oddSign s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases hs : s i <;> simp [signEntry,hs]

end TernaryPoly.SinglePoleSupport
