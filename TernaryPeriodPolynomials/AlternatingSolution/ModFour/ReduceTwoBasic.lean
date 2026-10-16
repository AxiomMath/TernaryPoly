module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section



/-! Basic transfer facts for reduction mod two, used in the proof of Theorem 5.2
(`mf:thm:main`). -/

open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- Characteristic two: every element of `Poly2` is its own negative. -/
theorem neg_eq_self_two (x : Poly2) : -x = x :=
  CharTwo.neg_eq x

/-- Reduction mod two can only shrink the monomial support, so it preserves having only
odd-degree monomials. -/
theorem reduceTwo_hasOddMonomials {f : MvPolynomial (Fin 3) ℤ} (hf : HasOddMonomials f) :
    HasOddMonomials (reduceTwo f) := by
  intro d hd
  rw [mem_support_iff] at hd
  apply hf
  rw [mem_support_iff]
  intro hc
  apply hd
  rw [MvPolynomial.coeff_map, hc, map_zero]

/-- Reduction mod two of `C 2 * g` is always zero. -/
theorem reduceTwo_two_mul (g : MvPolynomial (Fin 3) ℤ) : reduceTwo (C 2 * g) = 0 := by
  have h2 : (2 : Poly2) = 0 := by exact_mod_cast CharP.cast_eq_zero Poly2 2
  show MvPolynomial.map (Int.castRingHom (ZMod 2)) (C 2 * g) = 0
  simp [h2]

/-- An alternating integral polynomial reduces mod two to a symmetric polynomial. -/
theorem alternating_reduceTwo_symmetric {f : MvPolynomial (Fin 3) ℤ} (hf : IsAlternating f) :
    (reduceTwo f).IsSymmetric := by
  intro σ
  have hnat : (reduceTwo (rename σ f) : Poly2) = rename σ (reduceTwo f) := map_rename _ _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · have hr : rename σ f = f := by rw [hf, h]; simp
    rw [← hnat, hr]
  · have hr : rename σ f = -f := by rw [hf, h]; simp
    rw [← hnat, hr, map_neg, neg_eq_self_two]

end TernaryPeriodPolynomials.Argument
