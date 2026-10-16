module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
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
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Derivative toolkit for Lemma C.3 (`ar:lem:seed`), clause (i) (closedness of the seed).

The coefficient `coeff m (L(c)ⁿ)` of a polynomial `L(c) = L0 + c • L1` affine in a real (or
complex) parameter `c` is itself a polynomial in `c` of degree `≤ n`; this file computes its
derivative in closed form by induction on `n`, via `MvPolynomial.coeff_mul`'s antidiagonal
expansion. Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- The coefficient `coeff m ((L0 + c • L1) ^ n)`, as a function of the scalar `c`, has
derivative `n * coeff m ((L0 + c₀ • L1) ^ (n - 1) * L1)` at every point `c₀`. Proved by
induction on `n` using the antidiagonal expansion of `coeff m (P * Q)`. -/
theorem coeff_affine_pow_hasDerivAt (L0 L1 : MvPolynomial (Fin 3) ℂ) :
    ∀ (n : ℕ) (c₀ : ℂ) (m : Fin 3 →₀ ℕ),
      HasDerivAt (fun c : ℂ => ((L0 + c • L1) ^ n).coeff m)
        ((n : ℂ) * ((L0 + c₀ • L1) ^ (n - 1) * L1).coeff m) c₀ := by
  intro n
  induction n with
  | zero =>
    intro c₀ m
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact hasDerivAt_const c₀ ((1 : MvPolynomial (Fin 3) ℂ).coeff m)
  | succ n ih =>
    intro c₀ m
    have hcoeff : ∀ c : ℂ, ((L0 + c • L1) ^ (n+1)).coeff m =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          ((L0+c•L1)^n).coeff x.1 * (L0 + c•L1).coeff x.2 := by
      intro c
      rw [show (L0+c•L1)^(n+1) = (L0+c•L1)^n * (L0+c•L1) by ring, coeff_mul]
    have hgoal : (fun c : ℂ => ((L0+c•L1)^(n+1)).coeff m) =
        (fun c : ℂ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          ((L0+c•L1)^n).coeff x.1 * (L0+c•L1).coeff x.2) := funext hcoeff
    have hderiv2 : ∀ x : (Fin 3 →₀ ℕ) × (Fin 3 →₀ ℕ),
        HasDerivAt (fun c : ℂ => (L0 + c • L1).coeff x.2) (L1.coeff x.2) c₀ := by
      intro x
      have heq : (fun c : ℂ => (L0 + c • L1).coeff x.2) =
          fun c => L0.coeff x.2 + c * L1.coeff x.2 := by
        funext c
        rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_smul, smul_eq_mul]
      rw [heq]
      have hmul : HasDerivAt (fun c : ℂ => c * L1.coeff x.2) (L1.coeff x.2) c₀ := by
        simpa using (hasDerivAt_id c₀).mul_const (L1.coeff x.2)
      exact hmul.const_add (L0.coeff x.2)
    have hsum0 : HasDerivAt
        (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          (fun c : ℂ => ((L0+c•L1)^n).coeff x.1 * (L0+c•L1).coeff x.2))
        (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          ((n:ℂ) * ((L0+c₀•L1)^(n-1)*L1).coeff x.1 * (L0+c₀•L1).coeff x.2
            + ((L0+c₀•L1)^n).coeff x.1 * L1.coeff x.2))
        c₀ :=
      HasDerivAt.sum (fun x _ => (ih c₀ x.1).mul (hderiv2 x))
    have hfe : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (fun c : ℂ => ((L0+c•L1)^n).coeff x.1 * (L0+c•L1).coeff x.2))
      = (fun c : ℂ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        ((L0+c•L1)^n).coeff x.1 * (L0+c•L1).coeff x.2) := by
      funext c
      exact Finset.sum_apply c _ _
    rw [hfe] at hsum0
    have hfinal : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          ((n:ℂ) * ((L0+c₀•L1)^(n-1)*L1).coeff x.1 * (L0+c₀•L1).coeff x.2
            + ((L0+c₀•L1)^n).coeff x.1 * L1.coeff x.2))
        = ((n+1 : ℕ):ℂ) * ((L0+c₀•L1)^((n+1)-1) * L1).coeff m := by
      rw [Finset.sum_add_distrib]
      have hA : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
            (n:ℂ) * ((L0+c₀•L1)^(n-1)*L1).coeff x.1 * (L0+c₀•L1).coeff x.2
          = (n:ℂ) * (((L0+c₀•L1)^(n-1)*L1) * (L0+c₀•L1)).coeff m := by
        rw [coeff_mul, Finset.mul_sum]
        congr 1; funext x; ring
      have hB : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
            ((L0+c₀•L1)^n).coeff x.1 * L1.coeff x.2
          = ((L0+c₀•L1)^n * L1).coeff m := by
        rw [coeff_mul]
      rw [hA, hB, Nat.succ_sub_one]
      rcases n with _ | k
      · simp
      · have hpoly : (L0+c₀•L1)^(k+1-1) * L1 * (L0+c₀•L1) = (L0+c₀•L1)^(k+1) * L1 := by
          rw [Nat.succ_sub_one]; ring
        rw [hpoly]
        push_cast
        ring
    rw [hfinal] at hsum0
    rw [hgoal]
    convert hsum0 using 2

end TernaryPeriodPolynomials.Argument
