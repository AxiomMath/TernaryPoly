module

public import TernaryPeriodPolynomials.Polynomial.Pairwise
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Fintype.Order
public import Mathlib.Lean.Meta.Tactic.Rewrite

@[expose] public section


open MvPolynomial

namespace TernaryPoly

/-- The mixed derivative reads precisely the coefficients involving all three variables. -/
theorem coeff_mixed_derivative (f : MvPolynomial (Fin 3) ℚ) (d : Fin 3 →₀ ℕ) :
    (pderiv 0 (pderiv 1 (pderiv 2 f))).coeff d =
      f.coeff (d + Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) *
        ((d 2 : ℚ) + 1) * ((d 1 : ℚ) + 1) * ((d 0 : ℚ) + 1) := by
  simp [coeff_pderiv]

/-- A ternary rational polynomial is pairwise supported exactly when its mixed derivative vanishes. -/
theorem pairwise_iff_mixed_derivative_eq_zero (f : MvPolynomial (Fin 3) ℚ) :
    Pairwise f ↔ pderiv 0 (pderiv 1 (pderiv 2 f)) = 0 := by
  constructor
  · intro hf
    ext d
    rw [coeff_mixed_derivative, hf]
    · simp
    · intro i
      fin_cases i <;> simp
  · intro hf d hd
    let m : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d i - 1)
    have hm : m + Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 = d := by
      ext i
      fin_cases i <;> simp [m, Nat.sub_add_cancel (hd _)]
    have hc := congrArg (·.coeff m) hf
    rw [coeff_mixed_derivative, hm, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    simpa only [mul_eq_zero, Nat.cast_add_one_ne_zero, or_false] using hc

end TernaryPoly
