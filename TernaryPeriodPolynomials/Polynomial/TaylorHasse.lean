module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
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
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.Field

@[expose] public section

open Polynomial

namespace TernaryPoly

variable {R : Type*} [CommRing R]

/-- Translation commutes with the ordinary polynomial derivative. -/
theorem derivative_taylor (u : R) (p : Polynomial R) :
    derivative (taylor u p) = taylor u (derivative p) := by
  simp [taylor_apply, derivative_comp]

/-- Translation commutes with every Hasse derivative, in arbitrary characteristic. -/
theorem hasseDeriv_taylor (u : R) (k : ℕ) (p : Polynomial R) :
    hasseDeriv k (taylor u p) = taylor u (hasseDeriv k p) := by
  ext n
  rw [hasseDeriv_coeff, taylor_coeff, taylor_coeff]
  have h := DFunLike.congr_fun (hasseDeriv_comp (R := R) n k) p
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h, eval_smul, nsmul_eq_mul, Nat.choose_symm_add]

/-- Taylor translation is a finite sum of Hasse derivatives at every valid cutoff. -/
theorem taylor_eq_hasse_sum (u : R) (p : Polynomial R) (N : ℕ)
    (hN : p.natDegree < N) :
    taylor u p = ∑ k ∈ Finset.range N, u^k • hasseDeriv k p := by
  ext n
  have hd : (hasseDeriv n p).natDegree < N :=
    lt_of_le_of_lt ((natDegree_hasseDeriv_le p n).trans (Nat.sub_le _ _)) hN
  rw [taylor_coeff, eval_eq_sum_range' hd]
  simp only [finsetSum_coeff, coeff_smul, hasseDeriv_coeff, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_comm k n, Nat.choose_symm_add]
  ac_rfl

end TernaryPoly
