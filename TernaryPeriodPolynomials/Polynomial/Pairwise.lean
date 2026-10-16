module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

open MvPolynomial

namespace TernaryPoly

/-- Every monomial with nonzero coefficient omits at least one variable. -/
def Pairwise (f : MvPolynomial (Fin 3) ℚ) : Prop :=
  ∀ d : Fin 3 →₀ ℕ, (∀ i, 0 < d i) → f.coeff d = 0

@[simp] theorem pairwise_zero : Pairwise 0 := by
  intro d hd
  exact rfl

theorem Pairwise.add {f g : MvPolynomial (Fin 3) ℚ}
    (hf : Pairwise f) (hg : Pairwise g) : Pairwise (f + g) := by
  intro d hd
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf d hd, hg d hd, add_zero]

theorem Pairwise.neg {f : MvPolynomial (Fin 3) ℚ}
    (hf : Pairwise f) : Pairwise (-f) := by
  intro d hd
  simp only [coeff_neg, hf d hd, neg_zero]

theorem Pairwise.smul {f : MvPolynomial (Fin 3) ℚ}
    (hf : Pairwise f) (a : ℚ) : Pairwise (a • f) := by
  intro d hd
  simp only [coeff_smul, hf d hd, smul_zero]

theorem pairwise_sum {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin 3) ℚ) (hf : ∀ i ∈ s, Pairwise (f i)) :
    Pairwise (∑ i ∈ s, f i) := by
  intro d hd
  simp only [coeff_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi d hd

private def HasPairwiseRepresentation (f : MvPolynomial (Fin 3) ℚ) : Prop :=
  ∃ p q r : MvPolynomial (Fin 2) ℚ,
    f = rename (![0, 1] : Fin 2 → Fin 3) p +
      rename (![1, 2] : Fin 2 → Fin 3) q +
      rename (![0, 2] : Fin 2 → Fin 3) r

private theorem representation_zero : HasPairwiseRepresentation 0 := by
  exact ⟨0, 0, 0, by simp⟩

private theorem representation_add {f g : MvPolynomial (Fin 3) ℚ}
    (hf : HasPairwiseRepresentation f) (hg : HasPairwiseRepresentation g) :
    HasPairwiseRepresentation (f + g) := by
  obtain ⟨p, q, r, rfl⟩ := hf
  obtain ⟨p', q', r', rfl⟩ := hg
  exact ⟨p + p', q + q', r + r', by simp only [map_add]; ac_rfl⟩

private theorem monomial_representation (d : Fin 3 →₀ ℕ) (a : ℚ)
    (hd : ∃ i, d i = 0) : HasPairwiseRepresentation (monomial d a) := by
  classical
  by_cases ha : a = 0
  · subst a
    simpa using representation_zero
  obtain ⟨i, hi⟩ := hd
  fin_cases i
  · obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range
      (monomial d a) (![1, 2] : Fin 2 → Fin 3) (by decide) (by
        rw [vars_monomial ha]
        intro j hj
        have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
        fin_cases j
        · exact (hj' hi).elim
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩)
    exact ⟨0, q, 0, by simpa using hq.symm⟩
  · obtain ⟨r, hr⟩ := exists_rename_eq_of_vars_subset_range
      (monomial d a) (![0, 2] : Fin 2 → Fin 3) (by decide) (by
        rw [vars_monomial ha]
        intro j hj
        have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
        fin_cases j
        · exact ⟨0, rfl⟩
        · exact (hj' hi).elim
        · exact ⟨1, rfl⟩)
    exact ⟨0, 0, r, by simpa using hr.symm⟩
  · obtain ⟨p, hp⟩ := exists_rename_eq_of_vars_subset_range
      (monomial d a) (![0, 1] : Fin 2 → Fin 3) (by decide) (by
        rw [vars_monomial ha]
        intro j hj
        have hj' : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
        fin_cases j
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact (hj' hi).elim)
    exact ⟨p, 0, 0, by simpa using hp.symm⟩

theorem Pairwise.exists_rename {f : MvPolynomial (Fin 3) ℚ} (hf : Pairwise f) :
    ∃ p q r : MvPolynomial (Fin 2) ℚ,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![0, 2] : Fin 2 → Fin 3) r := by
  classical
  change HasPairwiseRepresentation f
  rw [← support_sum_monomial_coeff f]
  apply Finset.sum_induction
  · intro p q hp hq
    exact representation_add hp hq
  · exact representation_zero
  · intro d hd
    apply monomial_representation
    by_contra h
    have hall : ∀ i, 0 < d i := by
      intro i
      exact Nat.pos_of_ne_zero fun hi => h ⟨i, hi⟩
    exact (mem_support_iff.mp hd) (hf d hall)

private theorem pairwise_rename_of_omits (ι : Fin 2 → Fin 3) (i : Fin 3)
    (hi : i ∉ Set.range ι) (p : MvPolynomial (Fin 2) ℚ) : Pairwise (rename ι p) := by
  intro d hd
  apply coeff_rename_eq_zero
  intro u hu
  have hz : d i = 0 := by
    rw [← hu]
    exact Finsupp.mapDomain_of_notMem_range u i hi
  exact (Nat.ne_of_gt (hd i) hz).elim

theorem pairwise_iff_exists_rename (f : MvPolynomial (Fin 3) ℚ) :
    Pairwise f ↔ ∃ p q r : MvPolynomial (Fin 2) ℚ,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![0, 2] : Fin 2 → Fin 3) r := by
  constructor
  · exact Pairwise.exists_rename
  · rintro ⟨p, q, r, rfl⟩
    exact ((pairwise_rename_of_omits _ 2 (by decide) p).add
      (pairwise_rename_of_omits _ 0 (by decide) q)).add
      (pairwise_rename_of_omits _ 1 (by decide) r)

end TernaryPoly
