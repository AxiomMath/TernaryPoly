module

public import TernaryPeriodPolynomials.Polynomial.Pairwise
public import TernaryPeriodPolynomials.Polynomial.Operators
public import TernaryPeriodPolynomials.Polynomial.Homogeneous
public import TernaryPeriodPolynomials.Polynomial.Derivative
public import TernaryPeriodPolynomials.ArithmeticCohomology.Boundary

@[expose] public section


open MvPolynomial

namespace TernaryPoly

theorem pairwise_iff_homogeneousComponents (f : TernaryPolynomial) :
    Pairwise f ↔ ∀ n, Pairwise (homogeneousComponent n f) := by
  constructor
  · intro hf n d hd
    simp only [coeff_homogeneousComponent, hf d hd, ite_self]
  · intro hf d hd
    simpa [coeff_homogeneousComponent] using hf d.degree d hd

theorem PeriodRelations.homogeneousComponent {f : TernaryPolynomial}
    (hf : PeriodRelations f) (n : ℕ) : PeriodRelations (homogeneousComponent n f) := by
  exact homogeneousComponent_relations f hf.1 hf.2 n

theorem isHomogeneous_swap {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (S f).IsHomogeneous n := by
  apply isHomogeneous_bind₁_linear hf
  intro i
  fin_cases i <;> exact isHomogeneous_X ℚ _

theorem isHomogeneous_symmetricPart {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (symmetricPart f).IsHomogeneous n := by
  exact (homogeneousSubmodule (Fin 3) ℚ n).smul_mem _ (hf.add (isHomogeneous_swap hf))

theorem isHomogeneous_alternatingPart {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) : (alternatingPart f).IsHomogeneous n := by
  exact (homogeneousSubmodule (Fin 3) ℚ n).smul_mem _ (hf.sub (isHomogeneous_swap hf))

/-- It suffices to prove support separately in every homogeneous degree. -/
theorem pairwise_of_homogeneous_solutions
    (h : ∀ n (f : TernaryPolynomial), f.IsHomogeneous n → PeriodRelations f → Pairwise f)
    {f : TernaryPolynomial} (hf : PeriodRelations f) : Pairwise f := by
  apply (pairwise_iff_homogeneousComponents f).mpr
  intro n
  exact h n _ (homogeneousComponent_isHomogeneous n f) (hf.homogeneousComponent n)

/-- It suffices to prove support in the symmetric and alternating sectors. -/
theorem pairwise_of_homogeneous_sectors
    (hs : ∀ n (f : TernaryPolynomial), f.IsHomogeneous n →
      PeriodRelations f → S f = f → Pairwise f)
    (ha : ∀ n (f : TernaryPolynomial), f.IsHomogeneous n →
      PeriodRelations f → S f = -f → Pairwise f)
    {f : TernaryPolynomial} (hf : PeriodRelations f) : Pairwise f := by
  apply pairwise_of_homogeneous_solutions (f := f) _ hf
  intro n g hg hrel
  have hp := hs n _ (isHomogeneous_symmetricPart hg)
    (symmetricPart_relations hrel) (S_symmetricPart g)
  have hm := ha n _ (isHomogeneous_alternatingPart hg)
    (alternatingPart_relations hrel) (S_alternatingPart g)
  simpa only [symmetricPart_add_alternatingPart] using hp.add hm

/-- Follows from the four unbounded homogeneous sectors. -/
theorem benchmark_of_four_sectors
    (hse : ∀ n (f : TernaryPolynomial), Even n → f.IsHomogeneous n →
      PeriodRelations f → S f = f → Pairwise f)
    (hso : ∀ n (f : TernaryPolynomial), Odd n → f.IsHomogeneous n →
      PeriodRelations f → S f = f → Pairwise f)
    (hae : ∀ n (f : TernaryPolynomial), Even n → f.IsHomogeneous n →
      PeriodRelations f → S f = -f → Pairwise f)
    (hao : ∀ n (f : TernaryPolynomial), Odd n → f.IsHomogeneous n →
      PeriodRelations f → S f = -f → Pairwise f)
    (f : TernaryPolynomial)
    (hcyclic : bind₁ ![X 1, X 2, X 0] f = f)
    (hnorm : f + bind₁ ![-X 1, X 0 - X 1, X 2] f +
      bind₁ ![X 1 - X 0, -X 0, X 2] f = 0) :
    ∃ p q r : MvPolynomial (Fin 2) ℚ,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![0, 2] : Fin 2 → Fin 3) r := by
  apply Pairwise.exists_rename
  apply pairwise_of_homogeneous_sectors (f := f) _ _ ⟨hcyclic, hnorm⟩
  · intro n g hg hrel hs
    rcases Nat.even_or_odd n with he | ho
    · exact hse n g he hg hrel hs
    · exact hso n g ho hg hrel hs
  · intro n g hg hrel hs
    rcases Nat.even_or_odd n with he | ho
    · exact hae n g he hg hrel hs
    · exact hao n g ho hg hrel hs

/-- The coordinate-support and differential formulations have exactly the same witnesses. -/
theorem exists_rename_iff_mixed_derivative_eq_zero (f : TernaryPolynomial) :
    (∃ p q r : MvPolynomial (Fin 2) ℚ,
      f = rename (![0, 1] : Fin 2 → Fin 3) p +
        rename (![1, 2] : Fin 2 → Fin 3) q +
        rename (![0, 2] : Fin 2 → Fin 3) r) ↔
      pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 :=
  (pairwise_iff_exists_rename f).symm.trans (pairwise_iff_mixed_derivative_eq_zero f)

/-- Degree zero is already discharged by the norm relation. -/
theorem pairwise_of_positive_homogeneous_sectors
    (hs : ∀ n (f : TernaryPolynomial), 0 < n → f.IsHomogeneous n →
      PeriodRelations f → S f = f → Pairwise f)
    (ha : ∀ n (f : TernaryPolynomial), 0 < n → f.IsHomogeneous n →
      PeriodRelations f → S f = -f → Pairwise f)
    {f : TernaryPolynomial} (hf : PeriodRelations f) : Pairwise f := by
  apply pairwise_of_homogeneous_sectors (f := f) _ _ hf
  · intro n g hg hrel hsymm
    cases n with
    | zero => simpa only [hrel.eq_zero_of_isHomogeneous_zero hg] using pairwise_zero
    | succ n => exact hs _ _ (Nat.succ_pos n) hg hrel hsymm
  · intro n g hg hrel halt
    cases n with
    | zero => simpa only [hrel.eq_zero_of_isHomogeneous_zero hg] using pairwise_zero
    | succ n => exact ha _ _ (Nat.succ_pos n) hg hrel halt

end TernaryPoly
