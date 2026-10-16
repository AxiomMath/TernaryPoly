module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Reflection

@[expose] public section


/-!
Lemma 5.6 table (`mf:eq:table`, the paper) — one column per file. Column `nu`
is `beta_+(V_nu)`, where `V_{4j+m} = mult_m * L_j`, `mult = (1, d6, d4, d4 d6)`, and the
half-norm `g` satisfies `threeTermNorm (baseSym j m) = C 2 * g` (symmetric lift).
Each column has: a literal integral half-norm `lit*G`, its reduction `lit*P` mod two, and
`piOperator lit*P = value` (the printed table entry, with `rho = d7^2` where printed).
-/

open MvPolynomial
open TernaryPoly.CharTwoNorm (a b c cplus d7 d4 d6 basis generator)
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.ModFourBeta

namespace TernaryPeriodPolynomials.Argument.Identities.Lemma56Table

noncomputable section

set_option maxRecDepth 20000
-- Half-norm of the symmetric lift of V_7 (column 7), in 6 chunks.
def lit7G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-272 * X 0 ^ 15+ 2040 * X 0 ^ 14 * X 1+ 3736 * X 0 ^ 14 * X 2- 6928 * X 0 ^ 13 * X 1 ^ 2- 26152 * X 0 ^ 13 * X 1 * X 2- 20240 * X 0 ^ 13 * X 2 ^ 2
    + 14092 * X 0 ^ 12 * X 1 ^ 3+ 82624 * X 0 ^ 12 * X 1 ^ 2 * X 2+ 131560 * X 0 ^ 12 * X 1 * X 2 ^ 2+ 58963 * X 0 ^ 12 * X 2 ^ 3- 19114 * X 0 ^ 11 * X 1 ^ 4
    - 155768 * X 0 ^ 11 * X 1 ^ 3 * X 2- 383894 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 2- 353778 * X 0 ^ 11 * X 1 * X 2 ^ 3- 105328 * X 0 ^ 11 * X 2 ^ 4+ 18183 * X 0 ^ 10 * X 1 ^ 5
    + 195761 * X 0 ^ 10 * X 1 ^ 4 * X 2+ 664257 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 2+ 947671 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 3+ 579304 * X 0 ^ 10 * X 1 * X 2 ^ 4
    + 123644 * X 0 ^ 10 * X 2 ^ 5- 11957 * X 0 ^ 9 * X 1 ^ 6- 174221 * X 0 ^ 9 * X 1 ^ 5 * X 2- 750675 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 2)

def lit7G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-1495390 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 3- 1404482 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 4- 618220 * X 0 ^ 9 * X 1 * X 2 ^ 5- 98790 * X 0 ^ 9 * X 2 ^ 6+ 4092 * X 0 ^ 8 * X 1 ^ 7
    + 124299 * X 0 ^ 8 * X 1 ^ 6 * X 2+ 566850 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 2+ 1583449 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3+ 1975389 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 4
    + 1362673 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 5+ 444555 * X 0 ^ 8 * X 1 * X 2 ^ 6+ 55028 * X 0 ^ 8 * X 2 ^ 7+ 4092 * X 0 ^ 7 * X 1 ^ 8- 96822 * X 0 ^ 7 * X 1 ^ 7 * X 2
    - 197738 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 2- 1253014 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 3- 1668454 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 4- 1741372 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 5
    - 845698 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 6- 220112 * X 0 ^ 7 * X 1 * X 2 ^ 7- 21064 * X 0 ^ 7 * X 2 ^ 8- 11957 * X 0 ^ 6 * X 1 ^ 9+ 124299 * X 0 ^ 6 * X 1 ^ 8 * X 2
    - 197738 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 2)

def lit7G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (1083161 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 3+ 676235 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 4+ 1628084 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 5+ 885353 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 6
    + 391261 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 7+ 73724 * X 0 ^ 6 * X 1 * X 2 ^ 8+ 5705 * X 0 ^ 6 * X 2 ^ 9+ 18183 * X 0 ^ 5 * X 1 ^ 10- 174221 * X 0 ^ 5 * X 1 ^ 9 * X 2
    + 566850 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 2- 1253014 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 3+ 676235 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 4- 1385974 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 5
    - 336025 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 6- 403391 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 7- 94788 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 8- 17115 * X 0 ^ 5 * X 1 * X 2 ^ 9
    - 944 * X 0 ^ 5 * X 2 ^ 10- 19114 * X 0 ^ 4 * X 1 ^ 11+ 195761 * X 0 ^ 4 * X 1 ^ 10 * X 2- 750675 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 2+ 1583449 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3
    - 1668454 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 4+ 1628084 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 5)

def lit7G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-336025 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 6+ 409456 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 7+ 52660 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 8+ 25758 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 9
    + 2360 * X 0 ^ 4 * X 1 * X 2 ^ 10+ 112 * X 0 ^ 4 * X 2 ^ 11+ 14092 * X 0 ^ 3 * X 1 ^ 12- 155768 * X 0 ^ 3 * X 1 ^ 11 * X 2+ 664257 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 2
    - 1495390 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 3+ 1975389 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 4- 1741372 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 5+ 885353 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 6
    - 403391 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 7+ 52660 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 8- 22991 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 9- 944 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 10
    - 224 * X 0 ^ 3 * X 1 * X 2 ^ 11- 4 * X 0 ^ 3 * X 2 ^ 12- 6928 * X 0 ^ 2 * X 1 ^ 13+ 82624 * X 0 ^ 2 * X 1 ^ 12 * X 2- 383894 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 2
    + 947671 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 3- 1404482 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 4)

def lit7G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (1362673 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 5- 845698 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 6+ 391261 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 7- 94788 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 8
    + 25758 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 9- 944 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 10+ 336 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 11+ 6 * X 0 ^ 2 * X 1 * X 2 ^ 12+ 2040 * X 0 * X 1 ^ 14
    - 26152 * X 0 * X 1 ^ 13 * X 2+ 131560 * X 0 * X 1 ^ 12 * X 2 ^ 2- 353778 * X 0 * X 1 ^ 11 * X 2 ^ 3+ 579304 * X 0 * X 1 ^ 10 * X 2 ^ 4- 618220 * X 0 * X 1 ^ 9 * X 2 ^ 5
    + 444555 * X 0 * X 1 ^ 8 * X 2 ^ 6- 220112 * X 0 * X 1 ^ 7 * X 2 ^ 7+ 73724 * X 0 * X 1 ^ 6 * X 2 ^ 8- 17115 * X 0 * X 1 ^ 5 * X 2 ^ 9+ 2360 * X 0 * X 1 ^ 4 * X 2 ^ 10
    - 224 * X 0 * X 1 ^ 3 * X 2 ^ 11+ 6 * X 0 * X 1 ^ 2 * X 2 ^ 12- 272 * X 1 ^ 15+ 3736 * X 1 ^ 14 * X 2- 20240 * X 1 ^ 13 * X 2 ^ 2)

def lit7G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (58963 * X 1 ^ 12 * X 2 ^ 3- 105328 * X 1 ^ 11 * X 2 ^ 4+ 123644 * X 1 ^ 10 * X 2 ^ 5- 98790 * X 1 ^ 9 * X 2 ^ 6+ 55028 * X 1 ^ 8 * X 2 ^ 7- 21064 * X 1 ^ 7 * X 2 ^ 8
    + 5705 * X 1 ^ 6 * X 2 ^ 9- 944 * X 1 ^ 5 * X 2 ^ 10+ 112 * X 1 ^ 4 * X 2 ^ 11- 4 * X 1 ^ 3 * X 2 ^ 12)

-- The integral half-norm lit7G, the sum of its chunks.
def lit7G : MvPolynomial (Fin 3) ℤ :=
    lit7G_0 + lit7G_1 + lit7G_2 + lit7G_3 + lit7G_4 + lit7G_5

def lit7P_0 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 12 * X 2 ^ 3+ X 0 ^ 10 * X 1 ^ 5+ X 0 ^ 10 * X 1 ^ 4 * X 2+ X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 2+ X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 3+ X 0 ^ 9 * X 1 ^ 6+ X 0 ^ 9 * X 1 ^ 5 * X 2
    + X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 2)

def lit7P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 8 * X 1 ^ 6 * X 2+ X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3+ X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 4+ X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 5+ X 0 ^ 8 * X 1 * X 2 ^ 6+ X 0 ^ 6 * X 1 ^ 9
    + X 0 ^ 6 * X 1 ^ 8 * X 2)

def lit7P_2 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 4+ X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 6+ X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 7+ X 0 ^ 6 * X 2 ^ 9+ X 0 ^ 5 * X 1 ^ 10
    + X 0 ^ 5 * X 1 ^ 9 * X 2+ X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 4+ X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 6+ X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 7+ X 0 ^ 5 * X 1 * X 2 ^ 9+ X 0 ^ 4 * X 1 ^ 10 * X 2
    + X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 2+ X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3)

def lit7P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 6+ X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 2+ X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 4+ X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 6+ X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 7
    + X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 9+ X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 3)

def lit7P_4 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 5+ X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 7+ X 0 * X 1 ^ 8 * X 2 ^ 6+ X 0 * X 1 ^ 5 * X 2 ^ 9)

def lit7P_5 : Poly2 :=
    X 1 ^ 12 * X 2 ^ 3+ X 1 ^ 6 * X 2 ^ 9

-- The reduction of lit7G modulo two, the sum of its chunks.
def lit7P : Poly2 :=
    lit7P_0 + lit7P_1 + lit7P_2 + lit7P_3 + lit7P_4 + lit7P_5

theorem lemma56_nu7_half :
    threeTermNorm (baseSym 1 3) = C 2 * lit7G := by
  unfold lit7G lit7G_0 lit7G_1 lit7G_2 lit7G_3 lit7G_4 lit7G_5
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

theorem lemma56_nu7_reduce_0 : reduceTwo lit7G_0 = lit7P_0 := by
  unfold lit7G_0 lit7P_0
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu7_reduce_1 : reduceTwo lit7G_1 = lit7P_1 := by
  unfold lit7G_1 lit7P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu7_reduce_2 : reduceTwo lit7G_2 = lit7P_2 := by
  unfold lit7G_2 lit7P_2
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu7_reduce_3 : reduceTwo lit7G_3 = lit7P_3 := by
  unfold lit7G_3 lit7P_3
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu7_reduce_4 : reduceTwo lit7G_4 = lit7P_4 := by
  unfold lit7G_4 lit7P_4
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu7_reduce_5 : reduceTwo lit7G_5 = lit7P_5 := by
  unfold lit7G_5 lit7P_5
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu7_reduce : reduceTwo lit7G = lit7P := by
  unfold lit7G lit7P
  simp only [map_add]
  rw [lemma56_nu7_reduce_0, lemma56_nu7_reduce_1, lemma56_nu7_reduce_2, lemma56_nu7_reduce_3, lemma56_nu7_reduce_4, lemma56_nu7_reduce_5]

open PolynomialReflection in
theorem lemma56_nu7_pi : piOperator lit7P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(0, 6, 9), (0, 12, 3), (1, 5, 9), (1, 8, 6), (2, 6, 7), (2, 8, 5), (2, 10, 3), (3, 3, 9),
       (3, 5, 7), (3, 6, 6), (3, 8, 4), (3, 10, 2), (4, 5, 6), (4, 8, 3), (4, 9, 2), (4, 10, 1),
       (5, 1, 9), (5, 3, 7), (5, 4, 6), (5, 6, 4), (5, 9, 1), (5, 10, 0), (6, 0, 9), (6, 2, 7),
       (6, 3, 6), (6, 5, 4), (6, 6, 3), (6, 8, 1), (6, 9, 0), (8, 1, 6), (8, 2, 5), (8, 3, 4),
       (8, 4, 3), (8, 6, 1), (9, 4, 2), (9, 5, 1), (9, 6, 0), (10, 2, 3), (10, 3, 2), (10, 4, 1),
       (10, 5, 0), (12, 0, 3)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit7P lit7P_0 lit7P_1 lit7P_2 lit7P_3 lit7P_4 lit7P_5
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
