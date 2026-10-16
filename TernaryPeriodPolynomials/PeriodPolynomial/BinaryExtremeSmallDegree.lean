module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryExtreme

private theorem monomial_two (m : Fin 2 →₀ ℕ) (r : ℚ) :
    monomial m r = C r * X 0 ^ m 0 * X 1 ^ m 1 := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_succ, mul_assoc]
  · intro i
    exact pow_zero _

/-- Literal diagonal substitution multiplies each coefficient by its monomial weight. -/
theorem coeff_diagonal (q : MvPolynomial (Fin 2) ℚ) (a b : ℚ) (m : Fin 2 →₀ ℕ) :
    (bind₁ ![C a * X 0,C b * X 1] q).coeff m = a ^ m 0 * b ^ m 1 * q.coeff m := by
  induction q using MvPolynomial.induction_on' with
  | monomial k r =>
    have h : bind₁ (![C a * X 0,C b * X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)
        (monomial k r) = (a ^ k 0 * b ^ k 1) • monomial k r := by
      rw [monomial_two]
      simp only [map_mul,map_pow,bind₁_C_right,bind₁_X_right,
        Matrix.cons_val_zero,Matrix.cons_val_one,
        Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,map_pow,mul_pow]
      ring
    rw [h,coeff_smul]
    simp only [coeff_monomial,smul_eq_mul]
    split_ifs with he
    · subst k
      rfl
    · simp
  | add q r hq hr => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hq,hr,mul_add]

/-- A separately odd binary polynomial has no coefficient with an even coordinate exponent. -/
theorem even_coeff_zero (q : MvPolynomial (Fin 2) ℚ)
    (h0 : bind₁ ![-X 0,X 1] q = -q) (h1 : bind₁ ![X 0,-X 1] q = -q)
    (m : Fin 2 →₀ ℕ) (h : Even (m 0) ∨ Even (m 1)) : q.coeff m = 0 := by
  rcases h with h | h
  · have he := coeff_diagonal q (-1) 1 m
    simp only [map_neg,map_one,neg_one_mul,one_mul,h0,coeff_neg,one_pow,mul_one,
      h.neg_one_pow,one_mul] at he
    linarith
  · have he := coeff_diagonal q 1 (-1) m
    simp only [map_neg,map_one,neg_one_mul,one_mul,h1,coeff_neg,one_pow,
      h.neg_one_pow,one_mul] at he
    linarith

/-- Symmetry transports a coefficient without changing its value. -/
theorem swap_coeff (q : MvPolynomial (Fin 2) ℚ) (h : bind₁ ![X 1,X 0] q = q)
    (m : Fin 2 →₀ ℕ) : q.coeff (m.mapDomain (Equiv.swap 0 1)) = q.coeff m := by
  have hr : rename (Equiv.swap (0 : Fin 2) 1) q = q := by
    have he : rename (Equiv.swap (0 : Fin 2) 1) =
        bind₁ (![X 1,X 0] : Fin 2 → MvPolynomial (Fin 2) ℚ) := by
      apply algHom_ext
      intro i
      fin_cases i <;> simp
    rw [he,h]
  simpa only [hr] using coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 2) 1).injective q m

/-- Below degree six, symmetry and separate oddness make the extreme coefficient detect all terms.
The coefficient vanishing hypothesis covers every first-exponent-one coefficient. -/
theorem eq_zero_of_degree_lt_six (q : MvPolynomial (Fin 2) ℚ) (d : ℕ)
    (hd : d < 6) (hq : q.IsHomogeneous d)
    (hs : bind₁ ![X 1,X 0] q = q)
    (h0 : bind₁ ![-X 0,X 1] q = -q) (h1 : bind₁ ![X 0,-X 1] q = -q)
    (he : ∀ m : Fin 2 →₀ ℕ, m 0 = 1 → q.coeff m = 0) : q = 0 := by
  ext m
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_cases hm : m.degree = d
  · have hdg : m.degree = m 0 + m 1 := by
      change m.sum (fun _ k => k) = _
      rw [Finsupp.sum_fintype]
      · simp [Fin.sum_univ_succ]
      · intro i
        rfl
    by_cases hz : Even (m 0) ∨ Even (m 1)
    · exact even_coeff_zero q h0 h1 m hz
    · have ha : Odd (m 0) := Nat.not_even_iff_odd.mp (not_or.mp hz).1
      have hb : Odd (m 1) := Nat.not_even_iff_odd.mp (not_or.mp hz).2
      have hor : m 0 = 1 ∨ m 1 = 1 := by
        obtain ⟨a,ha⟩ := ha
        obtain ⟨b,hb⟩ := hb
        omega
      rcases hor with hor | hor
      · exact he m hor
      · rw [← swap_coeff q hs m]
        apply he
        simpa only [Finsupp.mapDomain_equiv_apply,Equiv.symm_swap,Equiv.swap_apply_left] using hor
  · exact hq.coeff_eq_zero hm

end TernaryPoly.BinaryExtreme
