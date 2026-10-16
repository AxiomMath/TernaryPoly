module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
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
# Polynomial calculus for parametrized polynomial families

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3.Calc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Type} [Fintype σ]
  [DecidableEq σ]

/-- Specialization of the parameter variables of `Fin 3 ⊕ σ` to complex numbers. -/
def spec (z : σ → ℂ) : MvPolynomial (Fin 3 ⊕ σ) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  aeval (Sum.elim X (fun a => C (z a)))

omit [Fintype σ] [DecidableEq σ] in
theorem spec_X_inl (z : σ → ℂ) (i : Fin 3) : spec z (X (Sum.inl i)) = X i := by
  simp [spec]

omit [Fintype σ] [DecidableEq σ] in
theorem spec_X_inr (z : σ → ℂ) (a : σ) : spec z (X (Sum.inr a)) = C (z a) := by
  simp [spec]

omit [Fintype σ] [DecidableEq σ] in
theorem spec_C (z : σ → ℂ) (c : ℂ) : spec z (C c) = C c := by
  simp [spec]

/-- **Scalar chain rule.** The coefficient of `X^e` in a specialized polynomial is differentiable
in the parameters, with the formal partial derivatives. -/
theorem hasFDerivAt_coeff_spec (s : σ → E → ℂ) (Ds : σ → E →L[ℝ] ℂ) (x : E)
    (hs : ∀ a, HasFDerivAt (s a) (Ds a) x) (Q : MvPolynomial (Fin 3 ⊕ σ) ℂ) (e : Fin 3 →₀ ℕ) :
    HasFDerivAt (fun y => (spec (fun a => s a y) Q).coeff e)
      (∑ a, ((spec (fun a => s a x) (pderiv (Sum.inr a) Q)).coeff e) • Ds a) x := by
  induction Q using MvPolynomial.induction_on generalizing e with
  | C c =>
    have h0 : (∑ a, ((spec (fun a => s a x) (pderiv (Sum.inr a) (C c))).coeff e) • Ds a) = 0 := by
      simp only [pderiv_C, map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      exact Finset.sum_eq_zero fun a _ => zero_smul ℂ (Ds a)
    simp only [spec_C]
    exact (hasFDerivAt_const ((C c).coeff e : ℂ) x).congr_fderiv h0.symm
  | add p q hp hq =>
    have key := (hp e).add (hq e)
    have hfun : (fun y => (spec (fun a => s a y) (p + q)).coeff e) =
        (fun y => (spec (fun a => s a y) p).coeff e) +
          (fun y => (spec (fun a => s a y) q).coeff e) := by
      funext y
      simp
    rw [hfun]
    refine key.congr_fderiv ?_
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (add_smul _ _ _).symm
  | mul_X p k hp =>
    rcases k with i | b
    · have hder : ∀ a : σ, pderiv (Sum.inr a) (p * X (Sum.inl i)) =
          pderiv (Sum.inr a) p * X (Sum.inl i) := by
        intro a
        rw [Derivation.leibniz, pderiv_X_of_ne (by simp : (Sum.inl i : Fin 3 ⊕ σ) ≠ Sum.inr a)]
        simp only [smul_eq_mul, mul_zero]
        ring
      simp only [hder, map_mul, spec_X_inl, coeff_mul_X']
      by_cases hi : i ∈ e.support
      · simp only [hi, ite_true]
        exact hp _
      · simp only [hi, ite_false]
        exact (hasFDerivAt_const (0 : ℂ) x).congr_fderiv
          (Finset.sum_eq_zero fun a _ => zero_smul ℂ (Ds a)).symm
    · have hder : ∀ a : σ, pderiv (Sum.inr a) (p * X (Sum.inr b)) =
          pderiv (Sum.inr a) p * X (Sum.inr b) + if a = b then p else 0 := by
        intro a
        rw [Derivation.leibniz]
        by_cases hab : a = b
        · subst hab; simp only [smul_eq_mul, pderiv_X_self, mul_one, ite_true]; ring
        · have hne : (Sum.inr b : Fin 3 ⊕ σ) ≠ Sum.inr a := by simpa using Ne.symm hab
          simp only [smul_eq_mul, hab, pderiv_X_of_ne hne, mul_zero, add_zero, ite_false]
          ring
      have hco : ∀ (P : MvPolynomial (Fin 3) ℂ) (c : ℂ) (e' : Fin 3 →₀ ℕ),
          (P * C c).coeff e' = P.coeff e' * c := fun P c e' => by
        rw [mul_comm, coeff_C_mul, mul_comm]
      have hprod := (hp e).mul (hs b)
      simp only [hder, map_add, map_mul, spec_X_inr, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hco]
      refine hprod.congr_fderiv ?_
      ext v
      have h2 : ∑ a, (spec (fun a => s a x) (if a = b then p else 0)).coeff e * Ds a v =
          (spec (fun a => s a x) p).coeff e * Ds b v := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro a _ hab
          simp [hab]
        · simp
      simp only [add_apply, smul_apply,
        FunLike.coe_sum, Finset.sum_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, h2, Finset.mul_sum]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      ring

omit [Fintype σ] [DecidableEq σ] in
/-- Smoothness of the coefficient functions of a specialized polynomial. -/
theorem contDiffOn_coeff_spec (U : Set E) (s : σ → E → ℂ) (hs : ∀ a, ContDiffOn ℝ ∞ (s a) U)
    (Q : MvPolynomial (Fin 3 ⊕ σ) ℂ) (e : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ∞ (fun y => (spec (fun a => s a y) Q).coeff e) U := by
  induction Q using MvPolynomial.induction_on generalizing e with
  | C c =>
    simp only [spec_C]
    exact contDiffOn_const
  | add p q hp hq =>
    have hfun : (fun y => (spec (fun a => s a y) (p + q)).coeff e) =
        (fun y => (spec (fun a => s a y) p).coeff e) +
          (fun y => (spec (fun a => s a y) q).coeff e) := by
      funext y
      simp
    rw [hfun]
    exact (hp e).add (hq e)
  | mul_X p k hp =>
    rcases k with i | b
    · simp only [map_mul, spec_X_inl, coeff_mul_X']
      by_cases hi : i ∈ e.support
      · simp only [hi, ite_true]
        exact hp _
      · simp only [hi, ite_false]
        exact contDiffOn_const
    · have hco : ∀ (P : MvPolynomial (Fin 3) ℂ) (c : ℂ) (e' : Fin 3 →₀ ℕ),
          (P * C c).coeff e' = P.coeff e' * c := fun P c e' => by
        rw [mul_comm, coeff_C_mul, mul_comm]
      simp only [map_mul, spec_X_inr, hco]
      exact (hp e).mul (hs b)

end TernaryPeriodPolynomials.Argument.SeedC3.Calc
