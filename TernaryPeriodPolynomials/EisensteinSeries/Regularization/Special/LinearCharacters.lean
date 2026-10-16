module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
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


open Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem specialLinear_transvection_add {R : Type*} [CommRing R]
    {first second : Fin 3} (distinct : first ≠ second) (a b : R) :
    SpecialLinearGroup.transvection distinct a * SpecialLinearGroup.transvection distinct b =
      SpecialLinearGroup.transvection distinct (a + b) := by
  apply Subtype.ext
  exact Matrix.transvection_mul_transvection_same first second distinct a b

theorem specialLinear_transvection_inverse {R : Type*} [CommRing R]
    {first second : Fin 3} (distinct : first ≠ second) (a : R) :
    (SpecialLinearGroup.transvection distinct a)⁻¹ =
      SpecialLinearGroup.transvection distinct (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [specialLinear_transvection_add, add_neg_cancel]
  apply Subtype.ext
  exact Matrix.transvection_zero first second

theorem ternary_transvection_commutator {R : Type*} [CommRing R]
    {first middle last : Fin 3} (first_middle : first ≠ middle)
    (middle_last : middle ≠ last) (first_last : first ≠ last) (a : R) :
    SpecialLinearGroup.transvection first_middle a * SpecialLinearGroup.transvection middle_last 1 *
      (SpecialLinearGroup.transvection first_middle a)⁻¹ *
        (SpecialLinearGroup.transvection middle_last 1)⁻¹ =
          SpecialLinearGroup.transvection first_last a := by
  rw [specialLinear_transvection_inverse, specialLinear_transvection_inverse]
  apply Subtype.ext
  change Matrix.transvection first middle a * Matrix.transvection middle last 1 *
    Matrix.transvection first middle (-a) * Matrix.transvection middle last (-1) =
      Matrix.transvection first last a
  ext row column
  fin_cases first <;> fin_cases middle <;> fin_cases last <;>
    try contradiction
  all_goals
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.transvection, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.single]

theorem ternary_character_transvection {C : Type*} [CommGroup C]
    (character : SpecialLinearGroup (Fin 3) ℝ →* C)
    {first last : Fin 3} (distinct : first ≠ last) (a : ℝ) :
    character (SpecialLinearGroup.transvection distinct a) = 1 := by
  have third : ∃ middle : Fin 3, first ≠ middle ∧ middle ≠ last := by
    fin_cases first <;> fin_cases last <;> simp_all <;> decide
  obtain ⟨middle, first_middle, middle_last⟩ := third
  rw [← ternary_transvection_commutator first_middle middle_last distinct a]
  simp [mul_assoc]

/-- The case `first = 0`, `last = 1` of `ternary_diag2n_transvections`. -/
private theorem diag2n_transvections_01 {F : Type*} [Field F] (a : F) (nonzero : a ≠ 0) :
    SpecialLinearGroup.diag2n (show (0 : Fin 3) ≠ 1 by decide) a nonzero =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-a⁻¹) *
          SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a *
            SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (-1) *
              SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) 1 *
                SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (-1) := by
  apply Subtype.ext
  change (SpecialLinearGroup.diag2n (show (0 : Fin 3) ≠ 1 by decide) a nonzero).val =
    Matrix.transvection (0 : Fin 3) 1 a * Matrix.transvection (1 : Fin 3) 0 (-a⁻¹) *
      Matrix.transvection (0 : Fin 3) 1 a * Matrix.transvection (0 : Fin 3) 1 (-1) *
        Matrix.transvection (1 : Fin 3) 0 1 * Matrix.transvection (0 : Fin 3) 1 (-1)
  rw [SpecialLinearGroup.diag2n_coe]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, diagonal_apply_eq, diagonal_apply_ne,
      transvection, single, Matrix.mul_apply, Matrix.add_apply, of_apply, true_and, false_and,
      and_true, and_false, Fin.sum_univ_three, one_apply_eq, one_apply_ne, ↓reduceIte, add_zero,
      zero_add, one_mul, mul_one, zero_mul, mul_zero, neg_mul, mul_neg, nonzero, mul_inv_cancel₀,
      inv_mul_cancel₀, add_neg_cancel, neg_add_cancel, neg_zero, Finset.sum_neg_distrib,
      neg_add_rev, neg_neg]

/-- The case `first = 0`, `last = 2` of `ternary_diag2n_transvections`. -/
private theorem diag2n_transvections_02 {F : Type*} [Field F] (a : F) (nonzero : a ≠ 0) :
    SpecialLinearGroup.diag2n (show (0 : Fin 3) ≠ 2 by decide) a nonzero =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a *
        SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (-a⁻¹) *
          SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a *
            SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (-1) *
              SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) 1 *
                SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (-1) := by
  apply Subtype.ext
  change (SpecialLinearGroup.diag2n (show (0 : Fin 3) ≠ 2 by decide) a nonzero).val =
    Matrix.transvection (0 : Fin 3) 2 a * Matrix.transvection (2 : Fin 3) 0 (-a⁻¹) *
      Matrix.transvection (0 : Fin 3) 2 a * Matrix.transvection (0 : Fin 3) 2 (-1) *
        Matrix.transvection (2 : Fin 3) 0 1 * Matrix.transvection (0 : Fin 3) 2 (-1)
  rw [SpecialLinearGroup.diag2n_coe]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, diagonal_apply_eq, diagonal_apply_ne,
      transvection, single, Matrix.mul_apply, Matrix.add_apply, of_apply, true_and, false_and,
      and_true, and_false, Fin.sum_univ_three, one_apply_eq, one_apply_ne, ↓reduceIte, add_zero,
      zero_add, one_mul, mul_one, zero_mul, mul_zero, neg_mul, mul_neg, nonzero, mul_inv_cancel₀,
      inv_mul_cancel₀, add_neg_cancel, neg_add_cancel, neg_zero, Finset.sum_neg_distrib,
      neg_add_rev, neg_neg]

/-- The case `first = 1`, `last = 0` of `ternary_diag2n_transvections`. -/
private theorem diag2n_transvections_10 {F : Type*} [Field F] (a : F) (nonzero : a ≠ 0) :
    SpecialLinearGroup.diag2n (show (1 : Fin 3) ≠ 0 by decide) a nonzero =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) a *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (-a⁻¹) *
          SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) a *
            SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) *
              SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 *
                SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) := by
  apply Subtype.ext
  change (SpecialLinearGroup.diag2n (show (1 : Fin 3) ≠ 0 by decide) a nonzero).val =
    Matrix.transvection (1 : Fin 3) 0 a * Matrix.transvection (0 : Fin 3) 1 (-a⁻¹) *
      Matrix.transvection (1 : Fin 3) 0 a * Matrix.transvection (1 : Fin 3) 0 (-1) *
        Matrix.transvection (0 : Fin 3) 1 1 * Matrix.transvection (1 : Fin 3) 0 (-1)
  rw [SpecialLinearGroup.diag2n_coe]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, diagonal_apply_eq, diagonal_apply_ne,
      transvection, single, Matrix.mul_apply, Matrix.add_apply, of_apply, true_and, false_and,
      and_true, and_false, Fin.sum_univ_three, one_apply_eq, one_apply_ne, ↓reduceIte, add_zero,
      zero_add, one_mul, mul_one, zero_mul, mul_zero, neg_mul, mul_neg, nonzero, mul_inv_cancel₀,
      inv_mul_cancel₀, add_neg_cancel, neg_add_cancel, neg_zero, Finset.sum_neg_distrib,
      neg_add_rev, neg_neg]

/-- The case `first = 1`, `last = 2` of `ternary_diag2n_transvections`. -/
private theorem diag2n_transvections_12 {F : Type*} [Field F] (a : F) (nonzero : a ≠ 0) :
    SpecialLinearGroup.diag2n (show (1 : Fin 3) ≠ 2 by decide) a nonzero =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a *
        SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-a⁻¹) *
          SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a *
            SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (-1) *
              SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) 1 *
                SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (-1) := by
  apply Subtype.ext
  change (SpecialLinearGroup.diag2n (show (1 : Fin 3) ≠ 2 by decide) a nonzero).val =
    Matrix.transvection (1 : Fin 3) 2 a * Matrix.transvection (2 : Fin 3) 1 (-a⁻¹) *
      Matrix.transvection (1 : Fin 3) 2 a * Matrix.transvection (1 : Fin 3) 2 (-1) *
        Matrix.transvection (2 : Fin 3) 1 1 * Matrix.transvection (1 : Fin 3) 2 (-1)
  rw [SpecialLinearGroup.diag2n_coe]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, diagonal_apply_eq, diagonal_apply_ne,
      transvection, single, Matrix.mul_apply, Matrix.add_apply, of_apply, true_and, false_and,
      and_true, and_false, Fin.sum_univ_three, one_apply_eq, one_apply_ne, ↓reduceIte, add_zero,
      zero_add, one_mul, mul_one, zero_mul, mul_zero, neg_mul, mul_neg, nonzero, mul_inv_cancel₀,
      inv_mul_cancel₀, add_neg_cancel, neg_add_cancel, neg_zero, Finset.sum_neg_distrib,
      neg_add_rev, neg_neg]

/-- The case `first = 2`, `last = 0` of `ternary_diag2n_transvections`. -/
private theorem diag2n_transvections_20 {F : Type*} [Field F] (a : F) (nonzero : a ≠ 0) :
    SpecialLinearGroup.diag2n (show (2 : Fin 3) ≠ 0 by decide) a nonzero =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (-a⁻¹) *
          SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a *
            SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (-1) *
              SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) 1 *
                SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (-1) := by
  apply Subtype.ext
  change (SpecialLinearGroup.diag2n (show (2 : Fin 3) ≠ 0 by decide) a nonzero).val =
    Matrix.transvection (2 : Fin 3) 0 a * Matrix.transvection (0 : Fin 3) 2 (-a⁻¹) *
      Matrix.transvection (2 : Fin 3) 0 a * Matrix.transvection (2 : Fin 3) 0 (-1) *
        Matrix.transvection (0 : Fin 3) 2 1 * Matrix.transvection (2 : Fin 3) 0 (-1)
  rw [SpecialLinearGroup.diag2n_coe]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, diagonal_apply_eq, diagonal_apply_ne,
      transvection, single, Matrix.mul_apply, Matrix.add_apply, of_apply, true_and, false_and,
      and_true, and_false, Fin.sum_univ_three, one_apply_eq, one_apply_ne, ↓reduceIte, add_zero,
      zero_add, one_mul, mul_one, zero_mul, mul_zero, neg_mul, mul_neg, nonzero, mul_inv_cancel₀,
      inv_mul_cancel₀, add_neg_cancel, neg_add_cancel, neg_zero, Finset.sum_neg_distrib,
      neg_add_rev, neg_neg]

/-- The case `first = 2`, `last = 1` of `ternary_diag2n_transvections`. -/
private theorem diag2n_transvections_21 {F : Type*} [Field F] (a : F) (nonzero : a ≠ 0) :
    SpecialLinearGroup.diag2n (show (2 : Fin 3) ≠ 1 by decide) a nonzero =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (-a⁻¹) *
          SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a *
            SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-1) *
              SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1 *
                SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-1) := by
  apply Subtype.ext
  change (SpecialLinearGroup.diag2n (show (2 : Fin 3) ≠ 1 by decide) a nonzero).val =
    Matrix.transvection (2 : Fin 3) 1 a * Matrix.transvection (1 : Fin 3) 2 (-a⁻¹) *
      Matrix.transvection (2 : Fin 3) 1 a * Matrix.transvection (2 : Fin 3) 1 (-1) *
        Matrix.transvection (1 : Fin 3) 2 1 * Matrix.transvection (2 : Fin 3) 1 (-1)
  rw [SpecialLinearGroup.diag2n_coe]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ne_eq,
      zero_ne_one, one_ne_zero, not_false_eq_true, diagonal_apply_eq, diagonal_apply_ne,
      transvection, single, Matrix.mul_apply, Matrix.add_apply, of_apply, true_and, false_and,
      and_true, and_false, Fin.sum_univ_three, one_apply_eq, one_apply_ne, ↓reduceIte, add_zero,
      zero_add, one_mul, mul_one, zero_mul, mul_zero, neg_mul, mul_neg, nonzero, mul_inv_cancel₀,
      inv_mul_cancel₀, add_neg_cancel, neg_add_cancel, neg_zero, Finset.sum_neg_distrib,
      neg_add_rev, neg_neg]

theorem ternary_diag2n_transvections {F : Type*} [Field F]
    {first last : Fin 3} (distinct : first ≠ last) (a : F) (nonzero : a ≠ 0) :
    SpecialLinearGroup.diag2n distinct a nonzero =
      SpecialLinearGroup.transvection distinct a * SpecialLinearGroup.transvection (Ne.symm distinct) (-a⁻¹) *
        SpecialLinearGroup.transvection distinct a * SpecialLinearGroup.transvection distinct (-1) *
          SpecialLinearGroup.transvection (Ne.symm distinct) 1 * SpecialLinearGroup.transvection distinct (-1) := by
  fin_cases first <;> fin_cases last <;> try contradiction
  · exact diag2n_transvections_01 a nonzero
  · exact diag2n_transvections_02 a nonzero
  · exact diag2n_transvections_10 a nonzero
  · exact diag2n_transvections_12 a nonzero
  · exact diag2n_transvections_20 a nonzero
  · exact diag2n_transvections_21 a nonzero

theorem ternary_commutative_character_trivial {C : Type*} [CommGroup C]
    (character : SpecialLinearGroup (Fin 3) ℝ →* C) (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    character matrix = 1 := by
  apply SpecialLinearGroup.diagonal_transvection_induction' (fun matrix => character matrix = 1) matrix
  · intro first last distinct a nonzero
    rw [ternary_diag2n_transvections distinct a nonzero]
    simp only [map_mul, ternary_character_transvection, one_mul]
  · intro first last distinct a
    exact ternary_character_transvection character distinct a
  · intro first second first_trivial second_trivial
    rw [map_mul, first_trivial, second_trivial, one_mul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
