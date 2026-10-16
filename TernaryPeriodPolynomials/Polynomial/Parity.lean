module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial

namespace TernaryPoly

/-- Uniformly scaling the variables scales a monomial by its total degree. -/
theorem bind_smul_monomial {σ R : Type*} [CommSemiring R]
    (a r : R) (d : σ →₀ ℕ) :
    bind₁ (fun i => a • X i) (monomial d r) =
      a ^ (∑ i ∈ d.support, d i) • monomial d r := by
  classical
  rw [bind₁_monomial, monomial_eq]
  simp only [Algebra.smul_def, algebraMap_eq, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, map_pow, Finsupp.prod]
  ac_rfl

/-- A homogeneous polynomial transforms under uniform scaling with its degree. -/
theorem homogeneous_bind_smul {σ R : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} {n : ℕ} (hf : f.IsHomogeneous n) (a : R) :
    bind₁ (fun i => a • X i) f = a ^ n • f := by
  classical
  calc
    bind₁ (fun i => a • X i) f =
        ∑ d ∈ f.support, bind₁ (fun i => a • X i) (monomial d (f.coeff d)) := by
      rw [← map_sum, ← as_sum]
    _ = ∑ d ∈ f.support, a ^ n • monomial d (f.coeff d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [bind_smul_monomial, ← hf.degree_eq_sum_deg_support hd]
    _ = a ^ n • f := by rw [← Finset.smul_sum, ← as_sum]

/-- The literal ternary negation substitution acts by the parity of the homogeneous degree. -/
theorem homogeneous_bind_neg {f : MvPolynomial (Fin 3) ℚ} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    bind₁ ![-X 0, -X 1, -X 2] f = ((-1 : ℚ) ^ n) • f := by
  have h := homogeneous_bind_smul hf (-1 : ℚ)
  have ht : (fun i : Fin 3 => (-1 : ℚ) • (X i : MvPolynomial (Fin 3) ℚ)) =
      ![-X 0, -X 1, -X 2] := by
    funext i
    fin_cases i <;> simp
  rwa [ht] at h

/-- Even homogeneous degree gives invariance under simultaneous negation. -/
theorem homogeneous_bind_neg_even {f : MvPolynomial (Fin 3) ℚ} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Even n) :
    bind₁ ![-X 0, -X 1, -X 2] f = f := by
  simpa only [hn.neg_one_pow, one_smul] using homogeneous_bind_neg hf

/-- Odd homogeneous degree gives anti-invariance under simultaneous negation. -/
theorem homogeneous_bind_neg_odd {f : MvPolynomial (Fin 3) ℚ} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n) :
    bind₁ ![-X 0, -X 1, -X 2] f = -f := by
  simpa only [hn.neg_one_pow, neg_one_smul] using homogeneous_bind_neg hf

end TernaryPoly
