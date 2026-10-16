module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.DicksonInvariance18

@[expose] public section



/-!
# Basic infrastructure for Lemma 5.5 (`mf:lem:well-defined`)

Division by two, additivity of `threeTermNorm`/`piOperator`, reduction of the integral
lifts `liftA, liftB, liftC, liftCplus, liftDelta, liftD4, liftD6, liftD7`, and the
symmetric/alternating cancellation facts needed to go from `C 2 * h` back to `h`.
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (d4 d6 d7 a b c cplus)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

private theorem my_ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly2) = ((n % 2 : ℕ) : Poly2) :=
  CharP.cast_eq_mod Poly2 2 n

/-- Division by two for an integral polynomial whose reduction mod two is zero. -/
theorem exists_half {f : MvPolynomial (Fin 3) ℤ} (hf : reduceTwo f = 0) :
    ∃ g : MvPolynomial (Fin 3) ℤ, f = C 2 * g := by
  have hc : ∀ d, (2 : ℤ) ∣ f.coeff d := by
    intro d
    have heq : (reduceTwo f).coeff d = (0 : Poly2).coeff d := by
      rw [hf]
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at heq
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff d) 2).mp (by exact_mod_cast heq)
  choose k hk using hc
  refine ⟨∑ d ∈ f.support, monomial d (k d), ?_⟩
  conv_lhs => rw [f.as_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by rw [hk d, C_mul_monomial]

/-- Reduction mod two of `C 2 * g` is always zero. -/
theorem reduceTwo_two_mul (g : MvPolynomial (Fin 3) ℤ) : reduceTwo (C 2 * g) = 0 := by
  have h2 : (2 : Poly2) = 0 := by exact_mod_cast CharP.cast_eq_zero Poly2 2
  show MvPolynomial.map (Int.castRingHom (ZMod 2)) (C 2 * g) = 0
  simp [h2]

theorem reduceTwo_liftA : reduceTwo liftA = a := by
  simp only [liftA, a, map_add, map_X]

theorem reduceTwo_liftB : reduceTwo liftB = b := by
  simp only [liftB, b, map_add, map_mul, map_X]

theorem reduceTwo_liftC : reduceTwo liftC = c := by
  simp only [liftC, c, map_mul, map_X]

theorem reduceTwo_liftCplus : reduceTwo liftCplus = cplus := by
  simp only [liftCplus, cplus, map_add, map_mul, reduceTwo_liftA, reduceTwo_liftB, reduceTwo_liftC]

theorem reduceTwo_liftD4 : reduceTwo liftD4 = d4 := by
  simp only [liftD4, d4, map_add, map_mul, map_pow, reduceTwo_liftA, reduceTwo_liftB,
    reduceTwo_liftC]

theorem reduceTwo_liftD6 : reduceTwo liftD6 = d6 := by
  simp only [liftD6, d6, map_add, map_mul, map_pow, reduceTwo_liftA, reduceTwo_liftB,
    reduceTwo_liftC]

theorem reduceTwo_liftD7 : reduceTwo liftD7 = d7 := by
  simp only [liftD7, d7, cplus, map_add, map_mul, reduceTwo_liftA, reduceTwo_liftB, reduceTwo_liftC]

theorem reduceTwo_liftDelta : reduceTwo liftDelta = cplus := by
  have hZ : liftDelta =
      liftA * liftB - liftC -
        2 * (X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 0 * X 1 * X 2) := by
    simp only [liftDelta, liftA, liftB, liftC]
    ring
  have h2 : (2 : Poly2) = 0 := by exact_mod_cast CharP.cast_eq_zero Poly2 2
  have hzero : reduceTwo
      ((2 : MvPolynomial (Fin 3) ℤ) *
        (X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 0 * X 1 * X 2)) = 0 := by
    show MvPolynomial.map (Int.castRingHom (ZMod 2))
      ((2 : MvPolynomial (Fin 3) ℤ) *
        (X 0 ^ 2 * X 2 + X 0 * X 1 ^ 2 + X 1 * X 2 ^ 2 + X 0 * X 1 * X 2)) = 0
    simp [h2]
  rw [hZ, map_sub, map_sub, map_mul, hzero, sub_zero, reduceTwo_liftA, reduceTwo_liftB,
    reduceTwo_liftC]
  simp only [cplus, sub_eq_add_neg, CharTwo.neg_eq]

end TernaryPeriodPolynomials.Argument.ModFourBeta
