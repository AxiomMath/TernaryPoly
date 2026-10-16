module

public import TernaryPeriodPolynomials.Polynomial.ClassificationEquivalence

@[expose] public section


/-! Main statements from Ilin–Ono, *From three variables to two: polynomials
and periods of cusp forms*.
-/

noncomputable section
namespace TernaryPeriodPolynomials
open MvPolynomial

/-- Pairwise decomposition over every characteristic-zero field, in the
paper's cyclic order of the last pair of coordinates. -/
theorem ternary_period_polynomial_pairwise_field {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 3) F)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) :
    ∃ p q r : MvPolynomial (Fin 2) F,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![2, 0] : Fin 2 → Fin 3) r :=
  TernaryPoly.Paper.ternary_period_polynomial_pairwise f hcyclic hnorm

/-- Every odd-degree homogeneous solution vanishes. -/
theorem odd_homogeneous_solution_eq_zero {F : Type*} [Field F] [CharZero F]
    {f : MvPolynomial (Fin 3) F} {n : ℕ} (hf : f.IsHomogeneous n)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) (hodd : Odd n) : f = 0 :=
  TernaryPoly.Paper.solution_odd_eq_zero hf ⟨hcyclic, hnorm⟩ hodd

/-- The complete statement of the paper's first theorem. -/
theorem main {F : Type*} [Field F] [CharZero F] (f : MvPolynomial (Fin 3) F)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) :
    (∃ p q r : MvPolynomial (Fin 2) F,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![2, 0] : Fin 2 → Fin 3) r) ∧
    pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 ∧
    (∀ n, f.IsHomogeneous n → Odd n → f = 0) := by
  exact ⟨ternary_period_polynomial_pairwise_field f hcyclic hnorm,
    TernaryPoly.Paper.solution_mixed_derivative_eq_zero f ⟨hcyclic, hnorm⟩,
    fun _ hf hodd => odd_homogeneous_solution_eq_zero hf hcyclic hnorm hodd⟩

/-- The paper's symmetric classification, with all binary conditions
written literally. The unique binary polynomial is the restriction at z = 0. -/
theorem symmetric_classification {F : Type*} [Field F] [CharZero F]
    {f : MvPolynomial (Fin 3) F} {n : ℕ}
    (hf : f.IsHomogeneous n) (hs : f.IsSymmetric) :
    (f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) ↔
    ∃! q : MvPolynomial (Fin 2) F, q.IsHomogeneous n ∧
      (bind₁ ![X 1, X 0] q = q ∧ bind₁ ![-X 0, X 1] q = -q ∧
        bind₁ ![X 0, -X 1] q = -q ∧
        q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0) ∧
      f = TernaryPoly.Paper.cyclicLift q :=
  TernaryPoly.Paper.symmetric_classification_literal hf hs

end TernaryPeriodPolynomials
