module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Polynomial.Eval.SMul
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


/-!
# Taylor coordinates of a family of polynomials, and the Bol recursion

For polynomials `P_w = ∑_{p ≤ m} q_p(w) X^p` depending on a parameter `w`, the *Taylor coordinates*
`a_i(w) = ∑_p q_p(w) C(p, i) w^{p-i}` are the coefficients of `P_w(X + w)`
(`taylorCoeff_eq_coeff_taylor`). If each `q_p` has derivative `F · C(m, p) (-w)^{m-p}` (that is,
`P_w' = F · (X - w)^m` coefficientwise), then

`a_i' = (i + 1) a_{i+1} + [i = m] F`   (`hasDerivAt_taylorCoeff`),

which is the recursion of Bol's identity: all `a_i` are determined by `a_0` and its derivatives, and
`a_0^{(m+1)} = m! F`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Polynomial

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodTaylor

/-- The polynomial `∑_{p ≤ m} q_p X^p`. -/
def polyOf (m : ℕ) (q : ℕ → ℂ) : ℂ[X] := ∑ p ∈ Finset.range (m + 1), C (q p) * X ^ p

/-- The Taylor coordinates `a_i(w) = ∑_p q_p(w) C(p, i) w^{p-i}`. -/
def taylorCoeff (m : ℕ) (q : ℕ → ℂ → ℂ) (i : ℕ) (w : ℂ) : ℂ :=
  ∑ p ∈ Finset.range (m + 1), q p w * ((p.choose i : ℂ) * w ^ (p - i))

/-- The Taylor coordinates are the coefficients of `P_w(X + w)`. -/
theorem taylorCoeff_eq_coeff_taylor (m : ℕ) (q : ℕ → ℂ → ℂ) (i : ℕ) (w : ℂ) :
    taylorCoeff m q i w = (taylor w (polyOf m (fun p => q p w))).coeff i := by
  unfold taylorCoeff polyOf
  rw [map_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  show _ = (taylor w (C (q p w) * X ^ p)).coeff i
  rw [taylor_mul, taylor_C, taylor_pow, taylor_X, coeff_C_mul, coeff_X_add_C_pow]
  ring

/-- `∑_p C(m,p) (-z)^{m-p} C(p,i) z^{p-i} = [i = m]`. -/
theorem alt_sum (m i : ℕ) (z : ℂ) :
    ∑ p ∈ Finset.range (m + 1),
      ((m.choose p : ℂ) * (-z) ^ (m - p)) * ((p.choose i : ℂ) * z ^ (p - i)) =
      if i = m then 1 else 0 := by
  have hX : taylor z (X + C (-z) : ℂ[X]) = X := by
    simp [taylor_X, taylor_C]
  have hpow : taylor z ((X + C (-z)) ^ m : ℂ[X]) = X ^ m := by
    rw [taylor_pow, hX]
  have h1 : (taylor z ((X + C (-z)) ^ m : ℂ[X])).coeff i = if i = m then 1 else 0 := by
    rw [hpow, coeff_X_pow]
  rw [taylor_coeff] at h1
  rw [← h1, add_pow, map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hterm : (X ^ p * C (-z) ^ (m - p) * (m.choose p : ℂ[X]) : ℂ[X]) =
      C ((-z) ^ (m - p) * (m.choose p : ℂ)) * X ^ p := by
    rw [map_mul, map_pow, map_natCast]
    ring
  rw [hterm, C_mul_X_pow_eq_monomial, hasseDeriv_monomial, eval_monomial]
  ring

/-- **The Bol recursion.** -/
theorem hasDerivAt_taylorCoeff (m : ℕ) (q : ℕ → ℂ → ℂ) (F z : ℂ) (i : ℕ)
    (hq : ∀ p ≤ m, HasDerivAt (q p) (F * ((m.choose p : ℂ) * (-z) ^ (m - p))) z) :
    HasDerivAt (taylorCoeff m q i)
      (((i : ℂ) + 1) * taylorCoeff m q (i + 1) z + F * (if i = m then 1 else 0)) z := by
  have hterm : ∀ p ∈ Finset.range (m + 1),
      HasDerivAt (fun w => q p w * ((p.choose i : ℂ) * w ^ (p - i)))
        (F * ((m.choose p : ℂ) * (-z) ^ (m - p)) * ((p.choose i : ℂ) * z ^ (p - i)) +
          q p z * ((p.choose i : ℂ) * (((p - i : ℕ) : ℂ) * z ^ (p - i - 1)))) z := by
    intro p hp
    have hp' : p ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    exact (hq p hp').mul ((hasDerivAt_pow (p - i) z).const_mul (p.choose i : ℂ))
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : taylorCoeff m q i =
      fun w => ∑ p ∈ Finset.range (m + 1), q p w * ((p.choose i : ℂ) * w ^ (p - i)) := rfl
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ p ∈ Finset.range (m + 1),
      F * ((m.choose p : ℂ) * (-z) ^ (m - p)) * ((p.choose i : ℂ) * z ^ (p - i)) =
        F * (if i = m then 1 else 0) := by
    rw [← alt_sum m i z, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h2 : ∑ p ∈ Finset.range (m + 1),
      q p z * ((p.choose i : ℂ) * (((p - i : ℕ) : ℂ) * z ^ (p - i - 1))) =
        ((i : ℂ) + 1) * taylorCoeff m q (i + 1) z := by
    unfold taylorCoeff
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hc : (p.choose (i + 1) : ℂ) * ((i : ℂ) + 1) = (p.choose i : ℂ) * ((p - i : ℕ) : ℂ) := by
      exact_mod_cast Nat.choose_succ_right_eq p i
    rw [Nat.sub_sub p i 1]
    linear_combination (-(q p z * z ^ (p - (i + 1)))) * hc
  rw [h1, h2]
  ring

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodTaylor
