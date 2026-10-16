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

def lit21G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (128 * X 0 ^ 20 * X 2- 1280 * X 0 ^ 19 * X 1 * X 2- 2304 * X 0 ^ 19 * X 2 ^ 2+ 5888 * X 0 ^ 18 * X 1 ^ 2 * X 2+ 21888 * X 0 ^ 18 * X 1 * X 2 ^ 2
    + 17376 * X 0 ^ 18 * X 2 ^ 3- 16512 * X 0 ^ 17 * X 1 ^ 3 * X 2- 95424 * X 0 ^ 17 * X 1 ^ 2 * X 2 ^ 2- 156384 * X 0 ^ 17 * X 1 * X 2 ^ 3- 72912 * X 0 ^ 17 * X 2 ^ 4
    + 31536 * X 0 ^ 16 * X 1 ^ 4 * X 2+ 252960 * X 0 ^ 16 * X 1 ^ 3 * X 2 ^ 2+ 644072 * X 0 ^ 16 * X 1 ^ 2 * X 2 ^ 3+ 619752 * X 0 ^ 16 * X 1 * X 2 ^ 4
    + 190288 * X 0 ^ 16 * X 2 ^ 5- 43392 * X 0 ^ 15 * X 1 ^ 5 * X 2- 455376 * X 0 ^ 15 * X 1 ^ 4 * X 2 ^ 2- 1607872 * X 0 ^ 15 * X 1 ^ 3 * X 2 ^ 3
    - 2402536 * X 0 ^ 15 * X 1 ^ 2 * X 2 ^ 4- 1522304 * X 0 ^ 15 * X 1 * X 2 ^ 5- 327420 * X 0 ^ 15 * X 2 ^ 6+ 44361 * X 0 ^ 14 * X 1 ^ 6 * X 2
    + 588696 * X 0 ^ 14 * X 1 ^ 5 * X 2 ^ 2+ 2716199 * X 0 ^ 14 * X 1 ^ 4 * X 2 ^ 3)

def lit21G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (5623980 * X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 4+ 5531646 * X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 5+ 2455650 * X 0 ^ 14 * X 1 * X 2 ^ 6+ 384852 * X 0 ^ 14 * X 2 ^ 7
    - 34239 * X 0 ^ 13 * X 1 ^ 7 * X 2- 563304 * X 0 ^ 13 * X 1 ^ 6 * X 2 ^ 2- 3282097 * X 0 ^ 13 * X 1 ^ 5 * X 2 ^ 3- 8869822 * X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 4
    - 12081202 * X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 5- 8323980 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 6- 2693964 * X 0 ^ 13 * X 1 * X 2 ^ 7- 315812 * X 0 ^ 13 * X 2 ^ 8
    + 20166 * X 0 ^ 12 * X 1 ^ 8 * X 2+ 404664 * X 0 ^ 12 * X 1 ^ 7 * X 2 ^ 2+ 2925632 * X 0 ^ 12 * X 1 ^ 6 * X 2 ^ 3+ 9955101 * X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 4
    + 17686937 * X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 5+ 16861845 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 6+ 8472105 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 7+ 2052778 * X 0 ^ 12 * X 1 * X 2 ^ 8
    + 182688 * X 0 ^ 12 * X 2 ^ 9- 9521 * X 0 ^ 11 * X 1 ^ 9 * X 2- 214008 * X 0 ^ 11 * X 1 ^ 8 * X 2 ^ 2- 1963555 * X 0 ^ 11 * X 1 ^ 7 * X 2 ^ 3)

def lit21G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-8154526 * X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 4- 18330828 * X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 5- 22720812 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 6- 15811098 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 7
    - 5949624 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 8- 1096128 * X 0 ^ 11 * X 1 * X 2 ^ 9- 74232 * X 0 ^ 11 * X 2 ^ 10+ 5858 * X 0 ^ 10 * X 1 ^ 10 * X 2
    + 63360 * X 0 ^ 10 * X 1 ^ 9 * X 2 ^ 2+ 1075629 * X 0 ^ 10 * X 1 ^ 8 * X 2 ^ 3+ 4831200 * X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 4+ 14009869 * X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 5
    + 21421026 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 6+ 19532439 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 7+ 10142374 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 8+ 2908573 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 9
    + 408276 * X 0 ^ 10 * X 1 * X 2 ^ 10+ 20752 * X 0 ^ 10 * X 2 ^ 11- 9521 * X 0 ^ 9 * X 1 ^ 11 * X 2+ 63360 * X 0 ^ 9 * X 1 ^ 10 * X 2 ^ 2
    - 720624 * X 0 ^ 9 * X 1 ^ 9 * X 2 ^ 3- 1493781 * X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 4- 8544176 * X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 5- 13946751 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 6)

def lit21G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-16933272 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 7- 11207900 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 8- 4495025 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 9- 980378 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 10
    - 103760 * X 0 ^ 9 * X 1 * X 2 ^ 11- 3804 * X 0 ^ 9 * X 2 ^ 12+ 20166 * X 0 ^ 8 * X 1 ^ 12 * X 2- 214008 * X 0 ^ 8 * X 1 ^ 11 * X 2 ^ 2
    + 1075629 * X 0 ^ 8 * X 1 ^ 10 * X 2 ^ 3- 1493781 * X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 4+ 6309828 * X 0 ^ 8 * X 1 ^ 8 * X 2 ^ 5+ 4744152 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 6
    + 11631249 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 7+ 8238582 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 8+ 4577347 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 9+ 1349631 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 10
    + 224871 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 11+ 17118 * X 0 ^ 8 * X 1 * X 2 ^ 12+ 412 * X 0 ^ 8 * X 2 ^ 13- 34239 * X 0 ^ 7 * X 1 ^ 13 * X 2
    + 404664 * X 0 ^ 7 * X 1 ^ 12 * X 2 ^ 2- 1963555 * X 0 ^ 7 * X 1 ^ 11 * X 2 ^ 3+ 4831200 * X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 4- 8544176 * X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 5)

def lit21G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (4744152 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 6- 8779770 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 7- 2802492 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 8- 3396646 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 9
    - 1109666 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 10- 276924 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 11- 32280 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 12- 1648 * X 0 ^ 7 * X 1 * X 2 ^ 13
    - 20 * X 0 ^ 7 * X 2 ^ 14+ 44361 * X 0 ^ 6 * X 1 ^ 14 * X 2- 563304 * X 0 ^ 6 * X 1 ^ 13 * X 2 ^ 2+ 2925632 * X 0 ^ 6 * X 1 ^ 12 * X 2 ^ 3
    - 8154526 * X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 4+ 14009869 * X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 5- 13946751 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 6+ 11631249 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 7
    - 2802492 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 8+ 2821070 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 9+ 443485 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 10+ 242568 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 11
    + 33096 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 12+ 2833 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 13+ 70 * X 0 ^ 6 * X 1 * X 2 ^ 14- 43392 * X 0 ^ 5 * X 1 ^ 15 * X 2)

def lit21G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (588696 * X 0 ^ 5 * X 1 ^ 14 * X 2 ^ 2- 3282097 * X 0 ^ 5 * X 1 ^ 13 * X 2 ^ 3+ 9955101 * X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 4- 18330828 * X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 5
    + 21421026 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 6- 16933272 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 7+ 8238582 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 8- 3396646 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 9
    + 443485 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 10- 194262 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 11- 12228 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 12- 2731 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 13
    - 90 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 14+ 31536 * X 0 ^ 4 * X 1 ^ 16 * X 2- 455376 * X 0 ^ 4 * X 1 ^ 15 * X 2 ^ 2+ 2716199 * X 0 ^ 4 * X 1 ^ 14 * X 2 ^ 3
    - 8869822 * X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 4+ 17686937 * X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 5- 22720812 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 6+ 19532439 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 7
    - 11207900 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 8+ 4577347 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 9- 1109666 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 10+ 242568 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 11)

def lit21G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-12228 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 12+ 2680 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 13+ 50 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 14- 16512 * X 0 ^ 3 * X 1 ^ 17 * X 2
    + 252960 * X 0 ^ 3 * X 1 ^ 16 * X 2 ^ 2- 1607872 * X 0 ^ 3 * X 1 ^ 15 * X 2 ^ 3+ 5623980 * X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 4- 12081202 * X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 5
    + 16861845 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 6- 15811098 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 7+ 10142374 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 8- 4495025 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 9
    + 1349631 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 10- 276924 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 11+ 33096 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 12- 2731 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 13
    + 50 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 14+ 5888 * X 0 ^ 2 * X 1 ^ 18 * X 2- 95424 * X 0 ^ 2 * X 1 ^ 17 * X 2 ^ 2+ 644072 * X 0 ^ 2 * X 1 ^ 16 * X 2 ^ 3
    - 2402536 * X 0 ^ 2 * X 1 ^ 15 * X 2 ^ 4+ 5531646 * X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 5- 8323980 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 6+ 8472105 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 7)

def lit21G_7 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-5949624 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 8+ 2908573 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 9- 980378 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 10+ 224871 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 11
    - 32280 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 12+ 2833 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 13- 90 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 14- 1280 * X 0 * X 1 ^ 19 * X 2
    + 21888 * X 0 * X 1 ^ 18 * X 2 ^ 2- 156384 * X 0 * X 1 ^ 17 * X 2 ^ 3+ 619752 * X 0 * X 1 ^ 16 * X 2 ^ 4- 1522304 * X 0 * X 1 ^ 15 * X 2 ^ 5
    + 2455650 * X 0 * X 1 ^ 14 * X 2 ^ 6- 2693964 * X 0 * X 1 ^ 13 * X 2 ^ 7+ 2052778 * X 0 * X 1 ^ 12 * X 2 ^ 8- 1096128 * X 0 * X 1 ^ 11 * X 2 ^ 9
    + 408276 * X 0 * X 1 ^ 10 * X 2 ^ 10- 103760 * X 0 * X 1 ^ 9 * X 2 ^ 11+ 17118 * X 0 * X 1 ^ 8 * X 2 ^ 12- 1648 * X 0 * X 1 ^ 7 * X 2 ^ 13+ 70 * X 0 * X 1 ^ 6 * X 2 ^ 14
    + 128 * X 1 ^ 20 * X 2- 2304 * X 1 ^ 19 * X 2 ^ 2+ 17376 * X 1 ^ 18 * X 2 ^ 3)

def lit21G_8 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-72912 * X 1 ^ 17 * X 2 ^ 4+ 190288 * X 1 ^ 16 * X 2 ^ 5- 327420 * X 1 ^ 15 * X 2 ^ 6+ 384852 * X 1 ^ 14 * X 2 ^ 7- 315812 * X 1 ^ 13 * X 2 ^ 8
    + 182688 * X 1 ^ 12 * X 2 ^ 9- 74232 * X 1 ^ 11 * X 2 ^ 10+ 20752 * X 1 ^ 10 * X 2 ^ 11- 3804 * X 1 ^ 9 * X 2 ^ 12+ 412 * X 1 ^ 8 * X 2 ^ 13- 20 * X 1 ^ 7 * X 2 ^ 14)

/-- The full lit21G, a sum of 9 chunks. -/
def lit21G : MvPolynomial (Fin 3) ℤ :=
    lit21G_0 + lit21G_1 + lit21G_2 + lit21G_3 + lit21G_4 + lit21G_5 + lit21G_6 + lit21G_7 + lit21G_8

def lit21P_0 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 14 * X 1 ^ 6 * X 2+ X 0 ^ 14 * X 1 ^ 4 * X 2 ^ 3+ X 0 ^ 13 * X 1 ^ 7 * X 2+ X 0 ^ 13 * X 1 ^ 5 * X 2 ^ 3+ X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 4+ X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 5
    + X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 6+ X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 7+ X 0 ^ 11 * X 1 ^ 9 * X 2+ X 0 ^ 11 * X 1 ^ 7 * X 2 ^ 3+ X 0 ^ 10 * X 1 ^ 8 * X 2 ^ 3
    + X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 5+ X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 7+ X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 9+ X 0 ^ 9 * X 1 ^ 11 * X 2+ X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 4
    + X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 6+ X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 9+ X 0 ^ 8 * X 1 ^ 10 * X 2 ^ 3+ X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 4+ X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 7
    + X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 9+ X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 10+ X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 11)

def lit21P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 7 * X 1 ^ 13 * X 2+ X 0 ^ 7 * X 1 ^ 11 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 14 * X 2+ X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 5+ X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 6+ X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 7
    + X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 10+ X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 13+ X 0 ^ 5 * X 1 ^ 13 * X 2 ^ 3+ X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 4+ X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 10
    + X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 13+ X 0 ^ 4 * X 1 ^ 14 * X 2 ^ 3+ X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 5+ X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 7+ X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 9
    + X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 6+ X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 9+ X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 10+ X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 13+ X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 7
    + X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 9+ X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 11+ X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 13)

/-- The full lit21P, a sum of 2 chunks. -/
def lit21P : Poly2 :=
    lit21P_0 + lit21P_1

set_option maxRecDepth 20000 in
theorem lemma56_nu21_half :
    threeTermNorm (baseSym 5 1) = C 2 * lit21G := by
  unfold lit21G lit21G_0 lit21G_1 lit21G_2 lit21G_3 lit21G_4 lit21G_5 lit21G_6 lit21G_7 lit21G_8
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD6, threeTermNorm]
  ring

set_option maxRecDepth 20000 in
theorem lemma56_nu21_reduce : reduceTwo lit21G = lit21P := by
  unfold lit21G lit21G_0 lit21G_1 lit21G_2 lit21G_3 lit21G_4 lit21G_5 lit21G_6 lit21G_7 lit21G_8 lit21P lit21P_0 lit21P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp only [ofNat_mod_poly2]
  ring

open PolynomialReflection in
theorem lemma56_nu21_pi : piOperator lit21P = d7 ^ 2 * (oddGenerator 3 + oddGenerator 4) := by
  refine piOperator_eq_of_reflect (lP :=
      [(2, 6, 13), (2, 8, 11), (2, 10, 9), (2, 12, 7), (3, 5, 13), (3, 8, 10), (3, 9, 9),
       (3, 12, 6), (4, 8, 9), (4, 10, 7), (4, 12, 5), (4, 14, 3), (5, 3, 13), (5, 6, 10),
       (5, 12, 4), (5, 13, 3), (6, 2, 13), (6, 5, 10), (6, 8, 7), (6, 9, 6), (6, 10, 5),
       (6, 14, 1), (7, 11, 3), (7, 13, 1), (8, 2, 11), (8, 3, 10), (8, 4, 9), (8, 6, 7), (8, 9, 4),
       (8, 10, 3), (9, 3, 9), (9, 6, 6), (9, 8, 4), (9, 11, 1), (10, 2, 9), (10, 4, 7), (10, 6, 5),
       (10, 8, 3), (11, 7, 3), (11, 9, 1), (12, 2, 7), (12, 3, 6), (12, 4, 5), (12, 5, 4),
       (13, 5, 3), (13, 7, 1), (14, 4, 3), (14, 6, 1)])
    (lQ := mulL (powL d7L 2) (addL (oddGeneratorL 3) (oddGeneratorL 4))) ?_ ?_ ?_
  · unfold lit21P lit21P_0 lit21P_1
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_mulL, ev_powL, ev_addL, ev_d7, ev_oddGenerator]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
