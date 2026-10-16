module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
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

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial

/-- **STEP2b(iii) building block.** If `q` is `w`-weighted-homogeneous of degree `e`, then for
*any* `p` (not necessarily homogeneous) the weighted component of `p * q` at degree `k + e` is the
weighted component of `p` at degree `k`, multiplied by `q`. Proved by the standard induction
principle for weighted-homogeneous polynomials (on `q`), reducing to the single-monomial case via
`coeff_mul_monomial'`. -/
theorem weightedHomogeneousComponent_mul_of_homog {R : Type*} [CommSemiring R] {σ : Type*}
    {w : σ → ℕ} {q : MvPolynomial σ R} {e : ℕ} (hq : IsWeightedHomogeneous w q e) :
    ∀ (p : MvPolynomial σ R) (k : ℕ),
      weightedHomogeneousComponent w (k + e) (p * q) =
        weightedHomogeneousComponent w k p * q := by
  induction hq using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => intro p k; simp
  | add q1 q2 _ _ ih1 ih2 =>
      intro p k
      rw [mul_add, map_add, ih1, ih2, mul_add]
  | monomial d r hr =>
      intro p k
      classical
      ext x
      rw [coeff_weightedHomogeneousComponent, coeff_mul_monomial', coeff_mul_monomial']
      by_cases hdx : d ≤ x
      · simp only [hdx, ite_true]
        rw [coeff_weightedHomogeneousComponent]
        have hxd : Finsupp.weight w x = Finsupp.weight w (x - d) + e := by
          rw [← hr, ← map_add, tsub_add_cancel_of_le hdx]
        rw [hxd]
        by_cases hk : Finsupp.weight w (x - d) = k
        · simp [hk]
        · simp [hk]
      · simp [hdx]

/-- **STEP2b(iii) building block.** If `q` is `w`-weighted-homogeneous of degree `e`, then for any
`p` the weighted component of `p * q` at a degree `k < e` vanishes: a product with a homogeneous
factor of degree `e` cannot contribute below degree `e`. -/
theorem weightedHomogeneousComponent_mul_eq_zero_of_lt {R : Type*} [CommSemiring R] {σ : Type*}
    {w : σ → ℕ} {q : MvPolynomial σ R} {e : ℕ} (hq : IsWeightedHomogeneous w q e)
    (p : MvPolynomial σ R) {k : ℕ} (hk : k < e) :
    weightedHomogeneousComponent w k (p * q) = 0 := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with hx
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨x1, x2⟩ hmem
    rw [Finset.mem_antidiagonal] at hmem
    by_cases hz : q.coeff x2 = 0
    · simp [hz]
    · exfalso
      have hw2 : Finsupp.weight w x2 = e := hq hz
      have hwx : Finsupp.weight w x = Finsupp.weight w x1 + Finsupp.weight w x2 := by
        rw [← hmem, map_add]
      omega
  · rfl

end TernaryPeriodPolynomials.Argument.CharTwoKernel
