module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GenAbsComponent

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (a b c Poly)

/-- Row 2 of the hand-derived `(row, slot, coefficient)` table: the `![4,6,7]`-
abstract coefficients of `genAbs 2 = d6 * standardMonomial 0 + d4 * standardMonomial 2 +
standardMonomial 14 + standardMonomial 15 + standardMonomial 16` (via `invariantEval_a/b/c`,
`d6 ↦ b`, `d4 ↦ a`), indexed by slot. -/
noncomputable def coeffAbs2 : Fin 28 → Poly :=
  fun j => if j = 0 then b else if j = 2 then a else if j = 14 then 1
    else if j = 15 then 1 else if j = 16 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs2 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs2 j) (genAbsDeg 2 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs2, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _
      | exact isWeightedHomogeneous_a_467
      | exact isWeightedHomogeneous_b_467

/-- Row 0: `genAbs 0 = standardMonomial 8 + standardMonomial 9`, both coefficients `1`. -/
noncomputable def coeffAbs0 : Fin 28 → Poly :=
  fun j => if j = 8 then 1 else if j = 9 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs0 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs0 j) (genAbsDeg 0 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs0, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _

/-- Row 1: `genAbs 1 = standardMonomial 12 + standardMonomial 13`, both coefficients `1`. -/
noncomputable def coeffAbs1 : Fin 28 → Poly :=
  fun j => if j = 12 then 1 else if j = 13 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs1 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs1 j) (genAbsDeg 1 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs1, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _

/-- Row 3: `genAbs 3 = d6 * standardMonomial 1 + d4 * standardMonomial 4 + standardMonomial 18`
(`d6 ↦ b`, `d4 ↦ a`). -/
noncomputable def coeffAbs3 : Fin 28 → Poly :=
  fun j => if j = 1 then b else if j = 4 then a else if j = 18 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs3 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs3 j) (genAbsDeg 3 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs3, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _
      | exact isWeightedHomogeneous_a_467
      | exact isWeightedHomogeneous_b_467

/-- Row 4: `genAbs 4 = d4 * standardMonomial 4 + d4 * standardMonomial 5 + standardMonomial 18 +
standardMonomial 20` (`d4 ↦ a`). -/
noncomputable def coeffAbs4 : Fin 28 → Poly :=
  fun j => if j = 4 then a else if j = 5 then a else if j = 18 then 1
    else if j = 20 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs4 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs4 j) (genAbsDeg 4 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs4, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _
      | exact isWeightedHomogeneous_a_467

/-- Row 5: `genAbs 5 = d7 * standardMonomial 1 + d6 * standardMonomial 3 + d4 * standardMonomial 8
+ standardMonomial 23` (`d7 ↦ c`, `d6 ↦ b`, `d4 ↦ a`). -/
noncomputable def coeffAbs5 : Fin 28 → Poly :=
  fun j => if j = 1 then c else if j = 3 then b else if j = 8 then a
    else if j = 23 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs5 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs5 j) (genAbsDeg 5 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs5, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _
      | exact isWeightedHomogeneous_a_467
      | exact isWeightedHomogeneous_b_467
      | exact isWeightedHomogeneous_c_467

/-- Row 6: `genAbs 6 = d6 * standardMonomial 4 + d6 * standardMonomial 5 + d6 * standardMonomial 6
+ d4 * standardMonomial 13 + standardMonomial 24` (`d6 ↦ b`, `d4 ↦ a`). -/
noncomputable def coeffAbs6 : Fin 28 → Poly :=
  fun j => if j = 4 then b else if j = 5 then b else if j = 6 then b
    else if j = 13 then a else if j = 24 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs6 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs6 j) (genAbsDeg 6 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs6, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _
      | exact isWeightedHomogeneous_a_467
      | exact isWeightedHomogeneous_b_467

/-- Row 7: `genAbs 7 = d4 * d6 * standardMonomial 0 + d4 * d4 * standardMonomial 2 +
d7 * standardMonomial 6 + d6 * standardMonomial 7 + d4 * standardMonomial 16 +
d4 * standardMonomial 17 + standardMonomial 26` (`d4 ↦ a`, `d6 ↦ b`, `d7 ↦ c`). -/
noncomputable def coeffAbs7 : Fin 28 → Poly :=
  fun j => if j = 0 then a * b else if j = 2 then a * a else if j = 6 then c
    else if j = 7 then b else if j = 16 then a else if j = 17 then a
    else if j = 26 then 1 else 0

theorem isWeightedHomogeneous_coeffAbs7 (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs7 j) (genAbsDeg 7 - stdDeg j) := by
  fin_cases j <;>
    simp [coeffAbs7, stdDeg, genAbsDeg] <;>
    first
      | exact isWeightedHomogeneous_zero _ _ _
      | exact isWeightedHomogeneous_one _ _
      | exact isWeightedHomogeneous_a_467
      | exact isWeightedHomogeneous_b_467
      | exact isWeightedHomogeneous_c_467
      | exact isWeightedHomogeneous_a_467.mul isWeightedHomogeneous_b_467
      | exact isWeightedHomogeneous_a_467.mul isWeightedHomogeneous_a_467

/-- The full `(row, slot) ↦ coefficient` table, `coeffAbs i j` giving the `![4,6,7]`-abstract
coefficient of `standardMonomial j` in `genAbs i`'s expansion. -/
noncomputable def coeffAbs : Fin 8 → Fin 28 → Poly :=
  ![coeffAbs0, coeffAbs1, coeffAbs2, coeffAbs3, coeffAbs4, coeffAbs5, coeffAbs6, coeffAbs7]

theorem isWeightedHomogeneous_coeffAbs (i : Fin 8) (j : Fin 28) :
    IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (coeffAbs i j) (genAbsDeg i - stdDeg j) := by
  fin_cases i
  · exact isWeightedHomogeneous_coeffAbs0 j
  · exact isWeightedHomogeneous_coeffAbs1 j
  · exact isWeightedHomogeneous_coeffAbs2 j
  · exact isWeightedHomogeneous_coeffAbs3 j
  · exact isWeightedHomogeneous_coeffAbs4 j
  · exact isWeightedHomogeneous_coeffAbs5 j
  · exact isWeightedHomogeneous_coeffAbs6 j
  · exact isWeightedHomogeneous_coeffAbs7 j

end TernaryPeriodPolynomials.Argument.CharTwoKernel
