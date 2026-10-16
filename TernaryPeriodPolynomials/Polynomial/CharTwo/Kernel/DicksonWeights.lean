module

public import TernaryPeriodPolynomials.Polynomial.DicksonQuotient
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Data.Fintype.Order
public import Mathlib.Lean.Meta.Tactic.Rewrite

@[expose] public section





namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (a b c d4 d6 d7)

/-- **STEP2b item (i).** The standard weight `(1,2,3)` on the three generators `a,b,c` of
`TernaryPoly.DicksonQuotient.Poly`, under which `d4,d6,d7` turn out to be homogeneous of degree
`4,6,7` respectively (matching their names). -/
def stdWeight : Fin 3 → ℕ := ![1, 2, 3]

theorem isWeightedHomogeneous_a : IsWeightedHomogeneous stdWeight a 1 := by
  simpa [stdWeight, a] using isWeightedHomogeneous_X (ZMod 2) stdWeight (0 : Fin 3)

theorem isWeightedHomogeneous_b : IsWeightedHomogeneous stdWeight b 2 := by
  simpa [stdWeight, b] using isWeightedHomogeneous_X (ZMod 2) stdWeight (1 : Fin 3)

theorem isWeightedHomogeneous_c : IsWeightedHomogeneous stdWeight c 3 := by
  simpa [stdWeight, c] using isWeightedHomogeneous_X (ZMod 2) stdWeight (2 : Fin 3)

/-- `d4 = a^4+b^2+a*c` is weighted-homogeneous of degree 4. -/
theorem isWeightedHomogeneous_d4 : IsWeightedHomogeneous stdWeight d4 4 := by
  unfold d4
  have h1 : IsWeightedHomogeneous stdWeight (a ^ 4) 4 := by
    simpa using isWeightedHomogeneous_a.pow 4
  have h2 : IsWeightedHomogeneous stdWeight (b ^ 2) 4 := by
    simpa using isWeightedHomogeneous_b.pow 2
  have h3 : IsWeightedHomogeneous stdWeight (a * c) 4 := by
    simpa using isWeightedHomogeneous_a.mul isWeightedHomogeneous_c
  exact (h1.add h2).add h3

/-- `d6 = a^2*b^2+a^3*c+a*b*c+c^2` is weighted-homogeneous of degree 6. -/
theorem isWeightedHomogeneous_d6 : IsWeightedHomogeneous stdWeight d6 6 := by
  unfold d6
  have h1 : IsWeightedHomogeneous stdWeight (a ^ 2 * b ^ 2) 6 := by
    simpa using (isWeightedHomogeneous_a.pow 2).mul (isWeightedHomogeneous_b.pow 2)
  have h2 : IsWeightedHomogeneous stdWeight (a ^ 3 * c) 6 := by
    simpa using (isWeightedHomogeneous_a.pow 3).mul isWeightedHomogeneous_c
  have h3 : IsWeightedHomogeneous stdWeight (a * b * c) 6 := by
    simpa using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_b).mul isWeightedHomogeneous_c
  have h4 : IsWeightedHomogeneous stdWeight (c ^ 2) 6 := by
    simpa using isWeightedHomogeneous_c.pow 2
  exact ((h1.add h2).add h3).add h4

/-- `d7 = a*c*(a*b+c)` is weighted-homogeneous of degree 7. -/
theorem isWeightedHomogeneous_d7 : IsWeightedHomogeneous stdWeight d7 7 := by
  unfold d7
  rw [mul_add]
  have h1 : IsWeightedHomogeneous stdWeight (a * c * (a * b)) 7 := by
    simpa using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_c).mul
      (isWeightedHomogeneous_a.mul isWeightedHomogeneous_b)
  have h2 : IsWeightedHomogeneous stdWeight (a * c * c) 7 := by
    simpa using (isWeightedHomogeneous_a.mul isWeightedHomogeneous_c).mul isWeightedHomogeneous_c
  exact h1.add h2

end TernaryPeriodPolynomials.Argument.CharTwoKernel
