module

public import TernaryPeriodPolynomials.Polynomial.Defs

@[expose] public section


/-! Odd-monomial property of the sharpness example for Theorem 5.2 (`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

private theorem sharp_isHomogeneous :
    ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ).IsHomogeneous 5 := by
  have h0 : (X 0 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 1 := isHomogeneous_X ℤ 0
  have h1 : (X 1 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 1 := isHomogeneous_X ℤ 1
  have h2 : (X 2 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 1 := isHomogeneous_X ℤ 2
  have hSum : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 1 := (h0.add h1).add h2
  have hSumSq : ((X 0 + X 1 + X 2) ^ 2 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 2 := hSum.pow 2
  have hd1 : (X 0 - X 1 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 1 := h0.sub h1
  have hd2 : (X 0 - X 2 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 1 := h0.sub h2
  have hd3 : (X 1 - X 2 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 1 := h1.sub h2
  have hV : ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2) : MvPolynomial (Fin 3) ℤ).IsHomogeneous 3 :=
    (hd1.mul hd2).mul hd3
  exact hSumSq.mul hV

/-- `f = (x+y+z)²(x-y)(x-z)(y-z)` has every monomial of odd total degree (degree `5`). -/
theorem sharp_oddMonomials :
    HasOddMonomials ((X 0 + X 1 + X 2) ^ 2 * ((X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)) :
      MvPolynomial (Fin 3) ℤ) := by
  intro d hd
  rw [mem_support_iff] at hd
  have hw := sharp_isHomogeneous hd
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hw
  rw [Finsupp.sum_fintype d _ (fun i => rfl), Fin.sum_univ_three] at hw
  rw [hw]
  decide

end TernaryPeriodPolynomials.Argument
