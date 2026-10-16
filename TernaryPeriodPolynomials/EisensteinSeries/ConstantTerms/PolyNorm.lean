module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Pow
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
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# The coefficient `ℓ¹`-norm on `ℂ[X, Y, Z]`

The sum of the absolute values of the coefficients is a submultiplicative seminorm on
`MvPolynomial (Fin 3) ℂ`, used to bound the coefficients of the polynomial-valued summands of the
series `ar:eq:Eseries` of Appendix C.3.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- The `ℓ¹` norm of the coefficient vector. -/
def l1 (q : MvPolynomial (Fin 3) ℂ) : ℝ := ∑ m ∈ q.support, ‖q.coeff m‖

theorem l1_nonneg (q : MvPolynomial (Fin 3) ℂ) : 0 ≤ l1 q :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem l1_eq_sum_of_support_subset {q : MvPolynomial (Fin 3) ℂ} {s : Finset (Fin 3 →₀ ℕ)}
    (h : q.support ⊆ s) : l1 q = ∑ m ∈ s, ‖q.coeff m‖ := by
  unfold l1
  apply Finset.sum_subset h
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.1 hm]; simp

theorem norm_coeff_le_l1 (q : MvPolynomial (Fin 3) ℂ) (m : Fin 3 →₀ ℕ) : ‖q.coeff m‖ ≤ l1 q := by
  by_cases hm : m ∈ q.support
  · exact Finset.single_le_sum (f := fun m => ‖q.coeff m‖) (fun _ _ => norm_nonneg _) hm
  · rw [MvPolynomial.notMem_support_iff.1 hm]; simpa using l1_nonneg q

theorem l1_zero : l1 (0 : MvPolynomial (Fin 3) ℂ) = 0 := by simp [l1]

theorem l1_add_le (p q : MvPolynomial (Fin 3) ℂ) : l1 (p + q) ≤ l1 p + l1 q := by
  have hsub : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  rw [l1_eq_sum_of_support_subset hsub,
    l1_eq_sum_of_support_subset (Finset.subset_union_left : p.support ⊆ p.support ∪ q.support),
    l1_eq_sum_of_support_subset (Finset.subset_union_right : q.support ⊆ p.support ∪ q.support),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact norm_add_le _ _

theorem l1_sum_le {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin 3) ℂ) :
    l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1_add_le _ _).trans (by linarith)

theorem l1_monomial_le (m : Fin 3 →₀ ℕ) (c : ℂ) : l1 (monomial m c) ≤ ‖c‖ := by
  by_cases hc : c = 0
  · simp [hc, l1_zero]
  · unfold l1
    rw [MvPolynomial.support_monomial, ite_eq_right hc]
    simp

theorem l1_C_mul (c : ℂ) (q : MvPolynomial (Fin 3) ℂ) : l1 (C c * q) = ‖c‖ * l1 q := by
  by_cases hc : c = 0
  · simp [hc, l1_zero]
  · unfold l1
    have hs : (C c * q).support = q.support := by
      ext m
      simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul, hc]
    rw [hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_C_mul, norm_mul]

theorem l1_mul_le (f g : MvPolynomial (Fin 3) ℂ) : l1 (f * g) ≤ l1 f * l1 g := by
  conv_lhs => rw [f.as_sum, g.as_sum]
  rw [Finset.sum_mul_sum]
  refine (l1_sum_le _ _).trans ?_
  unfold l1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (l1_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b _ => ?_
  rw [MvPolynomial.monomial_mul_monomial]
  refine (l1_monomial_le _ _).trans ?_
  rw [norm_mul]

theorem l1_one : l1 (1 : MvPolynomial (Fin 3) ℂ) = 1 := by
  simp [l1]

theorem l1_pow_le (q : MvPolynomial (Fin 3) ℂ) (n : ℕ) : l1 (q ^ n) ≤ l1 q ^ n := by
  induction n with
  | zero => simp [l1_one]
  | succ n ih =>
    rw [pow_succ]
    exact (l1_mul_le _ _).trans (by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right ih (l1_nonneg _))

theorem l1_linear_le (c : Fin 3 → ℂ) :
    l1 (∑ j : Fin 3, C (c j) * X j) ≤ ∑ j : Fin 3, ‖c j‖ := by
  refine (l1_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [l1_C_mul]
  have : l1 (X j : MvPolynomial (Fin 3) ℂ) ≤ 1 := by
    unfold l1
    rw [MvPolynomial.X, MvPolynomial.support_monomial]
    simp
  simpa using mul_le_mul_of_nonneg_left this (norm_nonneg (c j))

end TernaryPeriodPolynomials.Argument.ConvergenceC4
