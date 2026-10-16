module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section



/-! Additivity of `piOperator` and `expandOdd`, used in the proof of Theorem 5.2
(`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

private theorem sumMap_add {α M : Type*} [AddCommMonoid M] (l : List α) (f g : α → M) :
    (l.map fun t => f t + g t).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    abel

/-- `piOperator` is additive. -/
theorem piOperator_add (x y : Poly2) : piOperator (x + y) = piOperator x + piOperator y := by
  show (piSubstitutions.map fun t => bind₁ t (x + y)).sum
      = (piSubstitutions.map fun t => bind₁ t x).sum + (piSubstitutions.map fun t => bind₁ t y).sum
  have hpt : (fun t : Fin 3 → Poly2 => bind₁ t (x + y)) = (fun t => bind₁ t x + bind₁ t y) := by
    funext t; exact map_add (bind₁ t) x y
  rw [hpt, sumMap_add]

/-- `piOperator` vanishes at zero. -/
theorem piOperator_zero : piOperator (0 : Poly2) = 0 := by
  simp [piOperator]

/-- `expandOdd` is additive. -/
theorem expandOdd_add (r s : Fin 8 → Poly2) :
    expandOdd (r + s) = expandOdd r + expandOdd s := by
  show ∑ j, evalR0 ((r + s) j) * oddGenerator j
      = (∑ j, evalR0 (r j) * oddGenerator j) + ∑ j, evalR0 (s j) * oddGenerator j
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.add_apply, map_add, add_mul]

/-- `expandOdd` vanishes at the zero tuple. -/
theorem expandOdd_zero : expandOdd (0 : Fin 8 → Poly2) = 0 := by
  show ∑ j, evalR0 ((0 : Fin 8 → Poly2) j) * oddGenerator j = 0
  apply Finset.sum_eq_zero
  intro j _
  rw [Pi.zero_apply, map_zero, zero_mul]

end TernaryPeriodPolynomials.Argument
