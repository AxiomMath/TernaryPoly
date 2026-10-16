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
-- Half-norm of the symmetric lift of V_11 (column 11), in 11 chunks.
def lit11G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2720 * X 0 ^ 22 * X 2- 29920 * X 0 ^ 21 * X 1 * X 2- 48784 * X 0 ^ 21 * X 2 ^ 2+ 153464 * X 0 ^ 20 * X 1 ^ 2 * X 2+ 512232 * X 0 ^ 20 * X 1 * X 2 ^ 2
    + 372368 * X 0 ^ 20 * X 2 ^ 3- 487440 * X 0 ^ 19 * X 1 ^ 3 * X 2- 2503208 * X 0 ^ 19 * X 1 ^ 2 * X 2 ^ 2- 3723680 * X 0 ^ 19 * X 1 * X 2 ^ 3- 1623924 * X 0 ^ 19 * X 2 ^ 4
    + 1073774 * X 0 ^ 18 * X 1 ^ 4 * X 2+ 7559796 * X 0 ^ 18 * X 1 ^ 3 * X 2 ^ 2+ 17289784 * X 0 ^ 18 * X 1 ^ 2 * X 2 ^ 3+ 15427278 * X 0 ^ 18 * X 1 * X 2 ^ 4
    + 4569086 * X 0 ^ 18 * X 2 ^ 5- 1740966 * X 0 ^ 17 * X 1 ^ 5 * X 2- 15798904 * X 0 ^ 17 * X 1 ^ 4 * X 2 ^ 2- 49483176 * X 0 ^ 17 * X 1 ^ 3 * X 2 ^ 3
    - 67855114 * X 0 ^ 17 * X 1 ^ 2 * X 2 ^ 4- 41121774 * X 0 ^ 17 * X 1 * X 2 ^ 5- 8862192 * X 0 ^ 17 * X 2 ^ 6+ 2151414 * X 0 ^ 16 * X 1 ^ 6 * X 2
    + 24241354 * X 0 ^ 16 * X 1 ^ 5 * X 2 ^ 2+ 97717586 * X 0 ^ 16 * X 1 ^ 4 * X 2 ^ 3)

def lit11G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (183372880 * X 0 ^ 16 * X 1 ^ 3 * X 2 ^ 4+ 170762814 * X 0 ^ 16 * X 1 ^ 2 * X 2 ^ 5+ 75328632 * X 0 ^ 16 * X 1 * X 2 ^ 6+ 12338256 * X 0 ^ 16 * X 2 ^ 7
    - 2070024 * X 0 ^ 15 * X 1 ^ 7 * X 2- 28270174 * X 0 ^ 15 * X 1 ^ 6 * X 2 ^ 2- 141221488 * X 0 ^ 15 * X 1 ^ 5 * X 2 ^ 3- 340695860 * X 0 ^ 15 * X 1 ^ 4 * X 2 ^ 4
    - 434008968 * X 0 ^ 15 * X 1 ^ 3 * X 2 ^ 5- 294237662 * X 0 ^ 15 * X 1 ^ 2 * X 2 ^ 6- 98706048 * X 0 ^ 15 * X 1 * X 2 ^ 7- 12648964 * X 0 ^ 15 * X 2 ^ 8
    + 1571784 * X 0 ^ 14 * X 1 ^ 8 * X 2+ 25581457 * X 0 ^ 14 * X 1 ^ 7 * X 2 ^ 2+ 154602779 * X 0 ^ 14 * X 1 ^ 6 * X 2 ^ 3+ 461343706 * X 0 ^ 14 * X 1 ^ 5 * X 2 ^ 4
    + 755117857 * X 0 ^ 14 * X 1 ^ 4 * X 2 ^ 5+ 700209825 * X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 6+ 361158854 * X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 7+ 94867230 * X 0 ^ 14 * X 1 * X 2 ^ 8
    + 9699256 * X 0 ^ 14 * X 2 ^ 9- 954824 * X 0 ^ 13 * X 1 ^ 9 * X 2- 18110431 * X 0 ^ 13 * X 1 ^ 8 * X 2 ^ 2- 131011429 * X 0 ^ 13 * X 1 ^ 7 * X 2 ^ 3)

def lit11G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-470566502 * X 0 ^ 13 * X 1 ^ 6 * X 2 ^ 4- 952995463 * X 0 ^ 13 * X 1 ^ 5 * X 2 ^ 5- 1134494571 * X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 6- 800756138 * X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 7
    - 323602906 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 8- 67894792 * X 0 ^ 13 * X 1 * X 2 ^ 9- 5608412 * X 0 ^ 13 * X 2 ^ 10+ 500444 * X 0 ^ 12 * X 1 ^ 10 * X 2
    + 9806849 * X 0 ^ 12 * X 1 ^ 9 * X 2 ^ 2+ 87983778 * X 0 ^ 12 * X 1 ^ 8 * X 2 ^ 3+ 367400566 * X 0 ^ 12 * X 1 ^ 7 * X 2 ^ 4+ 903681135 * X 0 ^ 12 * X 1 ^ 6 * X 2 ^ 5
    + 1324302707 * X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 6+ 1202048066 * X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 7+ 664599234 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 8+ 214775113 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 9
    + 36454678 * X 0 ^ 12 * X 1 * X 2 ^ 10+ 2449096 * X 0 ^ 12 * X 2 ^ 11- 338132 * X 0 ^ 11 * X 1 ^ 11 * X 2- 2945795 * X 0 ^ 11 * X 1 ^ 10 * X 2 ^ 2
    - 50728659 * X 0 ^ 11 * X 1 ^ 9 * X 2 ^ 3- 213951466 * X 0 ^ 11 * X 1 ^ 8 * X 2 ^ 4- 663337763 * X 0 ^ 11 * X 1 ^ 7 * X 2 ^ 5- 1142582035 * X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 6)

def lit11G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-1293583786 * X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 7- 915548452 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 8- 406018382 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 9- 106215970 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 10
    - 14694576 * X 0 ^ 11 * X 1 * X 2 ^ 11- 803184 * X 0 ^ 11 * X 2 ^ 12+ 500444 * X 0 ^ 10 * X 1 ^ 12 * X 2- 2945795 * X 0 ^ 10 * X 1 ^ 11 * X 2 ^ 2
    + 36776642 * X 0 ^ 10 * X 1 ^ 10 * X 2 ^ 3+ 67960398 * X 0 ^ 10 * X 1 ^ 9 * X 2 ^ 4+ 415120070 * X 0 ^ 10 * X 1 ^ 8 * X 2 ^ 5+ 717880075 * X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 6
    + 1046328758 * X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 7+ 890328153 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 8+ 512854957 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 9+ 183186377 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 10
    + 39193167 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 11+ 4417512 * X 0 ^ 10 * X 1 * X 2 ^ 12+ 194952 * X 0 ^ 10 * X 2 ^ 13- 954824 * X 0 ^ 9 * X 1 ^ 13 * X 2
    + 9806849 * X 0 ^ 9 * X 1 ^ 12 * X 2 ^ 2- 50728659 * X 0 ^ 9 * X 1 ^ 11 * X 2 ^ 3+ 67960398 * X 0 ^ 9 * X 1 ^ 10 * X 2 ^ 4- 311004902 * X 0 ^ 9 * X 1 ^ 9 * X 2 ^ 5)

def lit11G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-233113683 * X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 6- 696009654 * X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 7- 600831691 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 8- 460598826 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 9
    - 206017225 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 10- 61265555 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 11- 10649176 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 12- 974760 * X 0 ^ 9 * X 1 * X 2 ^ 13
    - 34044 * X 0 ^ 9 * X 2 ^ 14+ 1571784 * X 0 ^ 8 * X 1 ^ 14 * X 2- 18110431 * X 0 ^ 8 * X 1 ^ 13 * X 2 ^ 2+ 87983778 * X 0 ^ 8 * X 1 ^ 12 * X 2 ^ 3
    - 213951466 * X 0 ^ 8 * X 1 ^ 11 * X 2 ^ 4+ 415120070 * X 0 ^ 8 * X 1 ^ 10 * X 2 ^ 5- 233113683 * X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 6+ 546701640 * X 0 ^ 8 * X 1 ^ 8 * X 2 ^ 7
    + 209161878 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 8+ 333656683 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 9+ 154681872 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 10+ 63739308 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 11
    + 14789952 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 12+ 2121057 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 13+ 153198 * X 0 ^ 8 * X 1 * X 2 ^ 14+ 4056 * X 0 ^ 8 * X 2 ^ 15)

def lit11G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-2070024 * X 0 ^ 7 * X 1 ^ 15 * X 2+ 25581457 * X 0 ^ 7 * X 1 ^ 14 * X 2 ^ 2- 131011429 * X 0 ^ 7 * X 1 ^ 13 * X 2 ^ 3+ 367400566 * X 0 ^ 7 * X 1 ^ 12 * X 2 ^ 4
    - 663337763 * X 0 ^ 7 * X 1 ^ 11 * X 2 ^ 5+ 717880075 * X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 6- 696009654 * X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 7+ 209161878 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 8
    - 263248762 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 9- 53677114 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 10- 49004238 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 11- 12297472 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 12
    - 2635668 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 13- 289224 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 14- 16224 * X 0 ^ 7 * X 1 * X 2 ^ 15- 296 * X 0 ^ 7 * X 2 ^ 16
    + 2151414 * X 0 ^ 6 * X 1 ^ 16 * X 2- 28270174 * X 0 ^ 6 * X 1 ^ 15 * X 2 ^ 2+ 154602779 * X 0 ^ 6 * X 1 ^ 14 * X 2 ^ 3- 470566502 * X 0 ^ 6 * X 1 ^ 13 * X 2 ^ 4
    + 903681135 * X 0 ^ 6 * X 1 ^ 12 * X 2 ^ 5- 1142582035 * X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 6+ 1046328758 * X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 7- 600831691 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 8)

def lit11G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (333656683 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 9- 53677114 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 10+ 41614692 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 11+ 4943960 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 12
    + 2347056 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 13+ 297360 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 14+ 27853 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 15+ 1036 * X 0 ^ 6 * X 1 * X 2 ^ 16
    + 10 * X 0 ^ 6 * X 2 ^ 17- 1740966 * X 0 ^ 5 * X 1 ^ 17 * X 2+ 24241354 * X 0 ^ 5 * X 1 ^ 16 * X 2 ^ 2- 141221488 * X 0 ^ 5 * X 1 ^ 15 * X 2 ^ 3
    + 461343706 * X 0 ^ 5 * X 1 ^ 14 * X 2 ^ 4- 952995463 * X 0 ^ 5 * X 1 ^ 13 * X 2 ^ 5+ 1324302707 * X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 6- 1293583786 * X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 7
    + 890328153 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 8- 460598826 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 9+ 154681872 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 10- 49004238 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 11
    + 4943960 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 12- 1910322 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 13- 110268 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 14- 26775 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 15)

def lit11G_7 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-1332 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 16- 30 * X 0 ^ 5 * X 1 * X 2 ^ 17+ 1073774 * X 0 ^ 4 * X 1 ^ 18 * X 2- 15798904 * X 0 ^ 4 * X 1 ^ 17 * X 2 ^ 2
    + 97717586 * X 0 ^ 4 * X 1 ^ 16 * X 2 ^ 3- 340695860 * X 0 ^ 4 * X 1 ^ 15 * X 2 ^ 4+ 755117857 * X 0 ^ 4 * X 1 ^ 14 * X 2 ^ 5- 1134494571 * X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 6
    + 1202048066 * X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 7- 915548452 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 8+ 512854957 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 9- 206017225 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 10
    + 63739308 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 11- 12297472 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 12+ 2347056 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 13- 110268 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 14
    + 26236 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 15+ 740 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 16+ 42 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 17- 487440 * X 0 ^ 3 * X 1 ^ 19 * X 2
    + 7559796 * X 0 ^ 3 * X 1 ^ 18 * X 2 ^ 2- 49483176 * X 0 ^ 3 * X 1 ^ 17 * X 2 ^ 3+ 183372880 * X 0 ^ 3 * X 1 ^ 16 * X 2 ^ 4- 434008968 * X 0 ^ 3 * X 1 ^ 15 * X 2 ^ 5)

def lit11G_8 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (700209825 * X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 6- 800756138 * X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 7+ 664599234 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 8- 406018382 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 9
    + 183186377 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 10- 61265555 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 11+ 14789952 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 12- 2635668 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 13
    + 297360 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 14- 26775 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 15+ 740 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 16- 34 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 17
    + 153464 * X 0 ^ 2 * X 1 ^ 20 * X 2- 2503208 * X 0 ^ 2 * X 1 ^ 19 * X 2 ^ 2+ 17289784 * X 0 ^ 2 * X 1 ^ 18 * X 2 ^ 3- 67855114 * X 0 ^ 2 * X 1 ^ 17 * X 2 ^ 4
    + 170762814 * X 0 ^ 2 * X 1 ^ 16 * X 2 ^ 5- 294237662 * X 0 ^ 2 * X 1 ^ 15 * X 2 ^ 6+ 361158854 * X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 7- 323602906 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 8
    + 214775113 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 9- 106215970 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 10+ 39193167 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 11- 10649176 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 12)

def lit11G_9 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2121057 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 13- 289224 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 14+ 27853 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 15- 1332 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 16
    + 42 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 17- 29920 * X 0 * X 1 ^ 21 * X 2+ 512232 * X 0 * X 1 ^ 20 * X 2 ^ 2- 3723680 * X 0 * X 1 ^ 19 * X 2 ^ 3
    + 15427278 * X 0 * X 1 ^ 18 * X 2 ^ 4- 41121774 * X 0 * X 1 ^ 17 * X 2 ^ 5+ 75328632 * X 0 * X 1 ^ 16 * X 2 ^ 6- 98706048 * X 0 * X 1 ^ 15 * X 2 ^ 7
    + 94867230 * X 0 * X 1 ^ 14 * X 2 ^ 8- 67894792 * X 0 * X 1 ^ 13 * X 2 ^ 9+ 36454678 * X 0 * X 1 ^ 12 * X 2 ^ 10- 14694576 * X 0 * X 1 ^ 11 * X 2 ^ 11
    + 4417512 * X 0 * X 1 ^ 10 * X 2 ^ 12- 974760 * X 0 * X 1 ^ 9 * X 2 ^ 13+ 153198 * X 0 * X 1 ^ 8 * X 2 ^ 14- 16224 * X 0 * X 1 ^ 7 * X 2 ^ 15
    + 1036 * X 0 * X 1 ^ 6 * X 2 ^ 16- 30 * X 0 * X 1 ^ 5 * X 2 ^ 17+ 2720 * X 1 ^ 22 * X 2- 48784 * X 1 ^ 21 * X 2 ^ 2)

def lit11G_10 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (372368 * X 1 ^ 20 * X 2 ^ 3- 1623924 * X 1 ^ 19 * X 2 ^ 4+ 4569086 * X 1 ^ 18 * X 2 ^ 5- 8862192 * X 1 ^ 17 * X 2 ^ 6+ 12338256 * X 1 ^ 16 * X 2 ^ 7
    - 12648964 * X 1 ^ 15 * X 2 ^ 8+ 9699256 * X 1 ^ 14 * X 2 ^ 9- 5608412 * X 1 ^ 13 * X 2 ^ 10+ 2449096 * X 1 ^ 12 * X 2 ^ 11- 803184 * X 1 ^ 11 * X 2 ^ 12
    + 194952 * X 1 ^ 10 * X 2 ^ 13- 34044 * X 1 ^ 9 * X 2 ^ 14+ 4056 * X 1 ^ 8 * X 2 ^ 15- 296 * X 1 ^ 7 * X 2 ^ 16+ 10 * X 1 ^ 6 * X 2 ^ 17)

-- The integral half-norm lit11G, the sum of its chunks.
def lit11G : MvPolynomial (Fin 3) ℤ :=
    lit11G_0 + lit11G_1 + lit11G_2 + lit11G_3 + lit11G_4 + lit11G_5 + lit11G_6 + lit11G_7 + lit11G_8 + lit11G_9 + lit11G_10

def lit11P_0 : Poly2 :=
    0

def lit11P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 14 * X 1 ^ 7 * X 2 ^ 2+ X 0 ^ 14 * X 1 ^ 6 * X 2 ^ 3+ X 0 ^ 14 * X 1 ^ 4 * X 2 ^ 5+ X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 6+ X 0 ^ 13 * X 1 ^ 8 * X 2 ^ 2
    + X 0 ^ 13 * X 1 ^ 7 * X 2 ^ 3)

def lit11P_2 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 13 * X 1 ^ 5 * X 2 ^ 5+ X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 6+ X 0 ^ 12 * X 1 ^ 9 * X 2 ^ 2+ X 0 ^ 12 * X 1 ^ 6 * X 2 ^ 5+ X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 6
    + X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 9+ X 0 ^ 11 * X 1 ^ 10 * X 2 ^ 2+ X 0 ^ 11 * X 1 ^ 9 * X 2 ^ 3+ X 0 ^ 11 * X 1 ^ 7 * X 2 ^ 5+ X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 6)

def lit11P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 10 * X 1 ^ 11 * X 2 ^ 2+ X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 6+ X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 8+ X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 9+ X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 10
    + X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 11+ X 0 ^ 9 * X 1 ^ 12 * X 2 ^ 2+ X 0 ^ 9 * X 1 ^ 11 * X 2 ^ 3)

def lit11P_4 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 6+ X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 8+ X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 10+ X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 11+ X 0 ^ 8 * X 1 ^ 13 * X 2 ^ 2
    + X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 6+ X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 9+ X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 13)

def lit11P_5 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 7 * X 1 ^ 14 * X 2 ^ 2+ X 0 ^ 7 * X 1 ^ 13 * X 2 ^ 3+ X 0 ^ 7 * X 1 ^ 11 * X 2 ^ 5+ X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 6+ X 0 ^ 6 * X 1 ^ 14 * X 2 ^ 3
    + X 0 ^ 6 * X 1 ^ 12 * X 2 ^ 5+ X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 6+ X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 8)

def lit11P_6 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 9+ X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 15+ X 0 ^ 5 * X 1 ^ 13 * X 2 ^ 5+ X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 6+ X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 8
    + X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 15)

def lit11P_7 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 4 * X 1 ^ 14 * X 2 ^ 5+ X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 6+ X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 9+ X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 10)

def lit11P_8 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 6+ X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 10+ X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 11+ X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 15+ X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 9
    + X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 11)

def lit11P_9 : Poly2 :=
    X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 13+ X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 15

def lit11P_10 : Poly2 :=
    0

-- The reduction of lit11G modulo two, the sum of its chunks.
def lit11P : Poly2 :=
    lit11P_0 + lit11P_1 + lit11P_2 + lit11P_3 + lit11P_4 + lit11P_5 + lit11P_6 + lit11P_7 + lit11P_8 + lit11P_9 + lit11P_10

theorem lemma56_nu11_half :
    threeTermNorm (baseSym 2 3) = C 2 * lit11G := by
  unfold lit11G lit11G_0 lit11G_1 lit11G_2 lit11G_3 lit11G_4 lit11G_5 lit11G_6 lit11G_7 lit11G_8 lit11G_9 lit11G_10
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

theorem lemma56_nu11_reduce_0 : reduceTwo lit11G_0 = lit11P_0 := by
  unfold lit11G_0 lit11P_0
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_1 : reduceTwo lit11G_1 = lit11P_1 := by
  unfold lit11G_1 lit11P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_2 : reduceTwo lit11G_2 = lit11P_2 := by
  unfold lit11G_2 lit11P_2
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_3 : reduceTwo lit11G_3 = lit11P_3 := by
  unfold lit11G_3 lit11P_3
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_4 : reduceTwo lit11G_4 = lit11P_4 := by
  unfold lit11G_4 lit11P_4
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_5 : reduceTwo lit11G_5 = lit11P_5 := by
  unfold lit11G_5 lit11P_5
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_6 : reduceTwo lit11G_6 = lit11P_6 := by
  unfold lit11G_6 lit11P_6
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_7 : reduceTwo lit11G_7 = lit11P_7 := by
  unfold lit11G_7 lit11P_7
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_8 : reduceTwo lit11G_8 = lit11P_8 := by
  unfold lit11G_8 lit11P_8
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_9 : reduceTwo lit11G_9 = lit11P_9 := by
  unfold lit11G_9 lit11P_9
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce_10 : reduceTwo lit11G_10 = lit11P_10 := by
  unfold lit11G_10 lit11P_10
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu11_reduce : reduceTwo lit11G = lit11P := by
  unfold lit11G lit11P
  simp only [map_add]
  rw [lemma56_nu11_reduce_0, lemma56_nu11_reduce_1, lemma56_nu11_reduce_2, lemma56_nu11_reduce_3, lemma56_nu11_reduce_4, lemma56_nu11_reduce_5, lemma56_nu11_reduce_6, lemma56_nu11_reduce_7, lemma56_nu11_reduce_8, lemma56_nu11_reduce_9, lemma56_nu11_reduce_10]

open PolynomialReflection in
theorem lemma56_nu11_pi : piOperator lit11P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(2, 6, 15), (2, 8, 13), (2, 10, 11), (2, 12, 9), (3, 5, 15), (3, 9, 11), (3, 10, 10),
       (3, 14, 6), (4, 9, 10), (4, 10, 9), (4, 13, 6), (4, 14, 5), (5, 3, 15), (5, 10, 8),
       (5, 12, 6), (5, 13, 5), (6, 2, 15), (6, 8, 9), (6, 9, 8), (6, 11, 6), (6, 12, 5),
       (6, 14, 3), (7, 10, 6), (7, 11, 5), (7, 13, 3), (7, 14, 2), (8, 2, 13), (8, 6, 9),
       (8, 9, 6), (8, 13, 2), (9, 3, 11), (9, 4, 10), (9, 6, 8), (9, 8, 6), (9, 11, 3), (9, 12, 2),
       (10, 2, 11), (10, 3, 10), (10, 4, 9), (10, 5, 8), (10, 7, 6), (10, 11, 2), (11, 6, 6),
       (11, 7, 5), (11, 9, 3), (11, 10, 2), (12, 2, 9), (12, 5, 6), (12, 6, 5), (12, 9, 2),
       (13, 4, 6), (13, 5, 5), (13, 7, 3), (13, 8, 2), (14, 3, 6), (14, 4, 5), (14, 6, 3),
       (14, 7, 2)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit11P lit11P_0 lit11P_1 lit11P_2 lit11P_3 lit11P_4 lit11P_5 lit11P_6 lit11P_7 lit11P_8 lit11P_9 lit11P_10
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
