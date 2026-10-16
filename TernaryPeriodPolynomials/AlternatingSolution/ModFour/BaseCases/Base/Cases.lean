module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.ExplicitLiftConstruction
public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.QuadrantDecomposition
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

@[expose] public section


/-! Base cases for the 32-case `W(j,m)` table (`modFour_beta_triangular`'s `uOperator`/`piOperator` route):
connects `baseSym j m` (the "pure quadrant" symmetric witnesses) all the way through
`threeTermNorm`, division by two, and `piOperator`, to the hand-derived table value for each
`(j,m)`. -/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 basis generator)

namespace TernaryPeriodPolynomials.Argument.ModFourBeta

/-- The four quadrant multipliers `1, D₆, D₄, D₄D₆` lifting `1, q, p, pq`. -/
noncomputable def mult : Fin 4 → MvPolynomial (Fin 3) ℤ := ![1, liftD6, liftD4, liftD4 * liftD6]

/-- The 32 "pure quadrant" symmetric base witnesses. -/
noncomputable def baseSym (j : Fin 8) (m : Fin 4) : MvPolynomial (Fin 3) ℤ :=
  mult m * oddGenLiftSym j

theorem half_4_0 :
    threeTermNorm (baseSym 4 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (-16 * X 0 ^ 7 + 56 * X 0 ^ 6 * X 1 + 83 * X 0 ^ 6 * X 2 - 72 * X 0 ^ 5 * X 1 ^ 2 -
        249 * X 0 ^ 5 * X 1 * X 2 - 138 * X 0 ^ 5 * X 2 ^ 2 + 40 * X 0 ^ 4 * X 1 ^ 3 +
        372 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 345 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 127 * X 0 ^ 4 * X 2 ^ 3 +
        40 * X 0 ^ 3 * X 1 ^ 4 - 329 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 138 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 -
        254 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 40 * X 0 ^ 3 * X 2 ^ 4 - 72 * X 0 ^ 2 * X 1 ^ 5 +
        372 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 138 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 +
        381 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 60 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 16 * X 0 ^ 2 * X 2 ^ 5 +
        56 * X 0 * X 1 ^ 6 - 249 * X 0 * X 1 ^ 5 * X 2 + 345 * X 0 * X 1 ^ 4 * X 2 ^ 2 -
        254 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 60 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 16 * X 0 * X 1 * X 2 ^ 5 -
        16 * X 1 ^ 7 + 83 * X 1 ^ 6 * X 2 - 138 * X 1 ^ 5 * X 2 ^ 2 + 127 * X 1 ^ 4 * X 2 ^ 3 -
        40 * X 1 ^ 3 * X 2 ^ 4 + 16 * X 1 ^ 2 * X 2 ^ 5)) := by
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus, liftC,
    liftB, liftA, threeTermNorm]
  ring

theorem ofNat_mod_poly2 (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly2) = ((n % 2 : ℕ) : Poly2) :=
  CharP.cast_eq_mod Poly2 2 n

theorem half_1_0 :
    threeTermNorm (baseSym 1 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (10 * X 1 ^ 2 * X 2 ^ 3 - 14 * X 1 ^ 3 * X 2 ^ 2 + 17 * X 1 ^ 4 * X 2 - 4 * X 1 ^ 5 -
        10 * X 0 * X 1 * X 2 ^ 3 + 21 * X 0 * X 1 ^ 2 * X 2 ^ 2 - 34 * X 0 * X 1 ^ 3 * X 2 +
        10 * X 0 * X 1 ^ 4 + 10 * X 0 ^ 2 * X 2 ^ 3 + 21 * X 0 ^ 2 * X 1 * X 2 ^ 2 +
        51 * X 0 ^ 2 * X 1 ^ 2 * X 2 - 4 * X 0 ^ 2 * X 1 ^ 3 - 14 * X 0 ^ 3 * X 2 ^ 2 -
        34 * X 0 ^ 3 * X 1 * X 2 - 4 * X 0 ^ 3 * X 1 ^ 2 + 17 * X 0 ^ 4 * X 2 +
        10 * X 0 ^ 4 * X 1 - 4 * X 0 ^ 5)) := by
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa, liftD7, liftCplus, liftC,
    liftB, liftA, threeTermNorm]
  ring

theorem reduceTwo_g40 :
    reduceTwo
      (poly_literal% (MvPolynomial (Fin 3) ℤ) (-16 * X 0 ^ 7 + 56 * X 0 ^ 6 * X 1 + 83 * X 0 ^ 6 * X 2 - 72 * X 0 ^ 5 * X 1 ^ 2 -
        249 * X 0 ^ 5 * X 1 * X 2 - 138 * X 0 ^ 5 * X 2 ^ 2 + 40 * X 0 ^ 4 * X 1 ^ 3 +
        372 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 345 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 127 * X 0 ^ 4 * X 2 ^ 3 +
        40 * X 0 ^ 3 * X 1 ^ 4 - 329 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 138 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 -
        254 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 40 * X 0 ^ 3 * X 2 ^ 4 - 72 * X 0 ^ 2 * X 1 ^ 5 +
        372 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 138 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 +
        381 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 60 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 16 * X 0 ^ 2 * X 2 ^ 5 +
        56 * X 0 * X 1 ^ 6 - 249 * X 0 * X 1 ^ 5 * X 2 + 345 * X 0 * X 1 ^ 4 * X 2 ^ 2 -
        254 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 60 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 16 * X 0 * X 1 * X 2 ^ 5 -
        16 * X 1 ^ 7 + 83 * X 1 ^ 6 * X 2 - 138 * X 1 ^ 5 * X 2 ^ 2 + 127 * X 1 ^ 4 * X 2 ^ 3 -
        40 * X 1 ^ 3 * X 2 ^ 4 + 16 * X 1 ^ 2 * X 2 ^ 5)) =
      ((poly_literal% Poly2 (X 0 ^ 6 * X 2 + X 0 ^ 5 * X 1 * X 2 + X 0 ^ 4 * X 1 * X 2 ^ 2 + X 0 ^ 4 * X 2 ^ 3 +
       X 0 ^ 3 * X 1 ^ 3 * X 2 + X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + X 0 * X 1 ^ 5 * X 2 +
       X 0 * X 1 ^ 4 * X 2 ^ 2 + X 1 ^ 6 * X 2 + X 1 ^ 4 * X 2 ^ 3)) : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp only [ofNat_mod_poly2]
  ring

theorem reduceTwo_g10 :
    reduceTwo
      (poly_literal% (MvPolynomial (Fin 3) ℤ) (10 * X 1 ^ 2 * X 2 ^ 3 - 14 * X 1 ^ 3 * X 2 ^ 2 + 17 * X 1 ^ 4 * X 2 - 4 * X 1 ^ 5 -
        10 * X 0 * X 1 * X 2 ^ 3 + 21 * X 0 * X 1 ^ 2 * X 2 ^ 2 - 34 * X 0 * X 1 ^ 3 * X 2 +
        10 * X 0 * X 1 ^ 4 + 10 * X 0 ^ 2 * X 2 ^ 3 + 21 * X 0 ^ 2 * X 1 * X 2 ^ 2 +
        51 * X 0 ^ 2 * X 1 ^ 2 * X 2 - 4 * X 0 ^ 2 * X 1 ^ 3 - 14 * X 0 ^ 3 * X 2 ^ 2 -
        34 * X 0 ^ 3 * X 1 * X 2 - 4 * X 0 ^ 3 * X 1 ^ 2 + 17 * X 0 ^ 4 * X 2 +
        10 * X 0 ^ 4 * X 1 - 4 * X 0 ^ 5)) =
      ((poly_literal% Poly2 (X 1 ^ 4 * X 2 + X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 1 * X 2 ^ 2 +
       X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 4 * X 2)) : Poly2) := by
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp only [ofNat_mod_poly2]
  ring

theorem pi_1_0 :
    piOperator
      ((poly_literal% Poly2 (X 1 ^ 4 * X 2 + X 0 * X 1 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 1 * X 2 ^ 2 +
       X 0 ^ 2 * X 1 ^ 2 * X 2 + X 0 ^ 4 * X 2)) : Poly2) = 0 := by
  simp [piOperator, piSubstitutions]
  ring_nf
  simp [ofNat_mod_poly2]

/-- **Case (1,0), fully closed.** -/
theorem case_1_0 :
    threeTermNorm (baseSym 1 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (10 * X 1 ^ 2 * X 2 ^ 3 - 14 * X 1 ^ 3 * X 2 ^ 2 + 17 * X 1 ^ 4 * X 2 - 4 * X 1 ^ 5 -
        10 * X 0 * X 1 * X 2 ^ 3 + 21 * X 0 * X 1 ^ 2 * X 2 ^ 2 - 34 * X 0 * X 1 ^ 3 * X 2 +
        10 * X 0 * X 1 ^ 4 + 10 * X 0 ^ 2 * X 2 ^ 3 + 21 * X 0 ^ 2 * X 1 * X 2 ^ 2 +
        51 * X 0 ^ 2 * X 1 ^ 2 * X 2 - 4 * X 0 ^ 2 * X 1 ^ 3 - 14 * X 0 ^ 3 * X 2 ^ 2 -
        34 * X 0 ^ 3 * X 1 * X 2 - 4 * X 0 ^ 3 * X 1 ^ 2 + 17 * X 0 ^ 4 * X 2 +
        10 * X 0 ^ 4 * X 1 - 4 * X 0 ^ 5)) ∧
    piOperator
      (reduceTwo
        (poly_literal% (MvPolynomial (Fin 3) ℤ) (10 * X 1 ^ 2 * X 2 ^ 3 - 14 * X 1 ^ 3 * X 2 ^ 2 + 17 * X 1 ^ 4 * X 2 - 4 * X 1 ^ 5 -
          10 * X 0 * X 1 * X 2 ^ 3 + 21 * X 0 * X 1 ^ 2 * X 2 ^ 2 - 34 * X 0 * X 1 ^ 3 * X 2 +
          10 * X 0 * X 1 ^ 4 + 10 * X 0 ^ 2 * X 2 ^ 3 + 21 * X 0 ^ 2 * X 1 * X 2 ^ 2 +
          51 * X 0 ^ 2 * X 1 ^ 2 * X 2 - 4 * X 0 ^ 2 * X 1 ^ 3 - 14 * X 0 ^ 3 * X 2 ^ 2 -
          34 * X 0 ^ 3 * X 1 * X 2 - 4 * X 0 ^ 3 * X 1 ^ 2 + 17 * X 0 ^ 4 * X 2 +
          10 * X 0 ^ 4 * X 1 - 4 * X 0 ^ 5))) = 0 :=
  ⟨half_1_0, by rw [reduceTwo_g10]; exact pi_1_0⟩

theorem pi_4_0 :
    piOperator
      ((poly_literal% Poly2 (X 0 ^ 6 * X 2 + X 0 ^ 5 * X 1 * X 2 + X 0 ^ 4 * X 1 * X 2 ^ 2 + X 0 ^ 4 * X 2 ^ 3 +
       X 0 ^ 3 * X 1 ^ 3 * X 2 + X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + X 0 * X 1 ^ 5 * X 2 +
       X 0 * X 1 ^ 4 * X 2 ^ 2 + X 1 ^ 6 * X 2 + X 1 ^ 4 * X 2 ^ 3)) : Poly2) = oddGenerator 3 := by
  simp [piOperator, piSubstitutions, oddGenerator, kappa, generator, basis, a, b, c, cplus]
  ring_nf
  simp [ofNat_mod_poly2]

/-- **Case (4,0), fully closed.** -/
theorem case_4_0 :
    threeTermNorm (baseSym 4 0) = C 2 *
      (poly_literal% (@MvPolynomial (Fin 3) ℤ CommRing.toCommSemiring) (-16 * X 0 ^ 7 + 56 * X 0 ^ 6 * X 1 + 83 * X 0 ^ 6 * X 2 - 72 * X 0 ^ 5 * X 1 ^ 2 -
        249 * X 0 ^ 5 * X 1 * X 2 - 138 * X 0 ^ 5 * X 2 ^ 2 + 40 * X 0 ^ 4 * X 1 ^ 3 +
        372 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 345 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 127 * X 0 ^ 4 * X 2 ^ 3 +
        40 * X 0 ^ 3 * X 1 ^ 4 - 329 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 138 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 -
        254 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 40 * X 0 ^ 3 * X 2 ^ 4 - 72 * X 0 ^ 2 * X 1 ^ 5 +
        372 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 138 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 +
        381 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 60 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 16 * X 0 ^ 2 * X 2 ^ 5 +
        56 * X 0 * X 1 ^ 6 - 249 * X 0 * X 1 ^ 5 * X 2 + 345 * X 0 * X 1 ^ 4 * X 2 ^ 2 -
        254 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 60 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 16 * X 0 * X 1 * X 2 ^ 5 -
        16 * X 1 ^ 7 + 83 * X 1 ^ 6 * X 2 - 138 * X 1 ^ 5 * X 2 ^ 2 + 127 * X 1 ^ 4 * X 2 ^ 3 -
        40 * X 1 ^ 3 * X 2 ^ 4 + 16 * X 1 ^ 2 * X 2 ^ 5)) ∧
    piOperator
      (reduceTwo
        (poly_literal% (MvPolynomial (Fin 3) ℤ) (-16 * X 0 ^ 7 + 56 * X 0 ^ 6 * X 1 + 83 * X 0 ^ 6 * X 2 - 72 * X 0 ^ 5 * X 1 ^ 2 -
          249 * X 0 ^ 5 * X 1 * X 2 - 138 * X 0 ^ 5 * X 2 ^ 2 + 40 * X 0 ^ 4 * X 1 ^ 3 +
          372 * X 0 ^ 4 * X 1 ^ 2 * X 2 + 345 * X 0 ^ 4 * X 1 * X 2 ^ 2 + 127 * X 0 ^ 4 * X 2 ^ 3 +
          40 * X 0 ^ 3 * X 1 ^ 4 - 329 * X 0 ^ 3 * X 1 ^ 3 * X 2 - 138 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 2 -
          254 * X 0 ^ 3 * X 1 * X 2 ^ 3 - 40 * X 0 ^ 3 * X 2 ^ 4 - 72 * X 0 ^ 2 * X 1 ^ 5 +
          372 * X 0 ^ 2 * X 1 ^ 4 * X 2 - 138 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 2 +
          381 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 + 60 * X 0 ^ 2 * X 1 * X 2 ^ 4 + 16 * X 0 ^ 2 * X 2 ^ 5 +
          56 * X 0 * X 1 ^ 6 - 249 * X 0 * X 1 ^ 5 * X 2 + 345 * X 0 * X 1 ^ 4 * X 2 ^ 2 -
          254 * X 0 * X 1 ^ 3 * X 2 ^ 3 + 60 * X 0 * X 1 ^ 2 * X 2 ^ 4 - 16 * X 0 * X 1 * X 2 ^ 5 -
          16 * X 1 ^ 7 + 83 * X 1 ^ 6 * X 2 - 138 * X 1 ^ 5 * X 2 ^ 2 + 127 * X 1 ^ 4 * X 2 ^ 3 -
          40 * X 1 ^ 3 * X 2 ^ 4 + 16 * X 1 ^ 2 * X 2 ^ 5))) = oddGenerator 3 :=
  ⟨half_4_0, by rw [reduceTwo_g40]; exact pi_4_0⟩

end TernaryPeriodPolynomials.Argument.ModFourBeta
