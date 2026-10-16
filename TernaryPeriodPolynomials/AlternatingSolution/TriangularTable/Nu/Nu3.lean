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
-- Half-norm of the symmetric lift of V_3 (column 3), in 9 chunks.
def lit3G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (544 * X 0 ^ 20 * X 2- 5440 * X 0 ^ 19 * X 1 * X 2- 9104 * X 0 ^ 19 * X 2 ^ 2+ 25144 * X 0 ^ 18 * X 1 ^ 2 * X 2+ 86488 * X 0 ^ 18 * X 1 * X 2 ^ 2
    + 63440 * X 0 ^ 18 * X 2 ^ 3- 71256 * X 0 ^ 17 * X 1 ^ 3 * X 2- 378896 * X 0 ^ 17 * X 1 ^ 2 * X 2 ^ 2- 570960 * X 0 ^ 17 * X 1 * X 2 ^ 3- 246836 * X 0 ^ 17 * X 2 ^ 4
    + 138470 * X 0 ^ 16 * X 1 ^ 4 * X 2+ 1015172 * X 0 ^ 16 * X 1 ^ 3 * X 2 ^ 2+ 2362712 * X 0 ^ 16 * X 1 ^ 2 * X 2 ^ 3+ 2098106 * X 0 ^ 16 * X 1 * X 2 ^ 4
    + 604926 * X 0 ^ 16 * X 2 ^ 5- 195472 * X 0 ^ 15 * X 1 ^ 5 * X 2- 1859908 * X 0 ^ 15 * X 1 ^ 4 * X 2 ^ 2- 5959936 * X 0 ^ 15 * X 1 ^ 3 * X 2 ^ 3
    - 8169936 * X 0 ^ 15 * X 1 ^ 2 * X 2 ^ 4- 4839408 * X 0 ^ 15 * X 1 * X 2 ^ 5- 997160 * X 0 ^ 15 * X 2 ^ 6+ 207130 * X 0 ^ 14 * X 1 ^ 6 * X 2
    + 2467646 * X 0 ^ 14 * X 1 ^ 5 * X 2 ^ 2+ 10242511 * X 0 ^ 14 * X 1 ^ 4 * X 2 ^ 3)

def lit3G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (19312400 * X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 4+ 17656891 * X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 5+ 7478700 * X 0 ^ 14 * X 1 * X 2 ^ 6+ 1150074 * X 0 ^ 14 * X 2 ^ 7
    - 167886 * X 0 ^ 13 * X 1 ^ 7 * X 2- 2447746 * X 0 ^ 13 * X 1 ^ 6 * X 2 ^ 2- 12694857 * X 0 ^ 13 * X 1 ^ 5 * X 2 ^ 3- 30951828 * X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 4
    - 38908597 * X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 5- 25443268 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 6- 8050518 * X 0 ^ 13 * X 1 * X 2 ^ 7- 950272 * X 0 ^ 13 * X 2 ^ 8
    + 105884 * X 0 ^ 12 * X 1 ^ 8 * X 2+ 1843790 * X 0 ^ 12 * X 1 ^ 7 * X 2 ^ 2+ 11732633 * X 0 ^ 12 * X 1 ^ 6 * X 2 ^ 3+ 35567246 * X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 4
    + 57816013 * X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 5+ 51954292 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 6+ 25401152 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 7+ 6176768 * X 0 ^ 12 * X 1 * X 2 ^ 8
    + 569510 * X 0 ^ 12 * X 2 ^ 9- 55530 * X 0 ^ 11 * X 1 ^ 9 * X 2- 1031054 * X 0 ^ 11 * X 1 ^ 8 * X 2 ^ 2- 8296865 * X 0 ^ 11 * X 1 ^ 7 * X 2 ^ 3)

def lit3G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-30064140 * X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 4- 61277381 * X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 5- 70918384 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 6- 47750178 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 7
    - 17953568 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 8- 3417060 * X 0 ^ 11 * X 1 * X 2 ^ 9- 248216 * X 0 ^ 11 * X 2 ^ 10+ 37368 * X 0 ^ 10 * X 1 ^ 10 * X 2
    + 318164 * X 0 ^ 10 * X 1 ^ 9 * X 2 ^ 2+ 4915180 * X 0 ^ 10 * X 1 ^ 8 * X 2 ^ 3+ 18464600 * X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 4+ 48442123 * X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 5
    + 68093190 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 6+ 59733308 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 7+ 30800176 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 8+ 9090959 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 9
    + 1365188 * X 0 ^ 10 * X 1 * X 2 ^ 10+ 78058 * X 0 ^ 10 * X 2 ^ 11- 55530 * X 0 ^ 9 * X 1 ^ 11 * X 2+ 318164 * X 0 ^ 9 * X 1 ^ 10 * X 2 ^ 2
    - 3524276 * X 0 ^ 9 * X 1 ^ 9 * X 2 ^ 3- 5886194 * X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 4- 31126731 * X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 5- 45288962 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 6)

def lit3G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-52827254 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 7- 34365200 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 8- 14131745 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 9- 3284140 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 10
    - 390290 * X 0 ^ 9 * X 1 * X 2 ^ 11- 17324 * X 0 ^ 9 * X 2 ^ 12+ 105884 * X 0 ^ 8 * X 1 ^ 12 * X 2- 1031054 * X 0 ^ 8 * X 1 ^ 11 * X 2 ^ 2
    + 4915180 * X 0 ^ 8 * X 1 ^ 10 * X 2 ^ 3- 5886194 * X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 4+ 23869254 * X 0 ^ 8 * X 1 ^ 8 * X 2 ^ 5+ 15620172 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 6
    + 37397912 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 7+ 25558752 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 8+ 14549348 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 9+ 4539720 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 10
    + 846988 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 11+ 77958 * X 0 ^ 8 * X 1 * X 2 ^ 12+ 2590 * X 0 ^ 8 * X 2 ^ 13- 167886 * X 0 ^ 7 * X 1 ^ 13 * X 2
    + 1843790 * X 0 ^ 7 * X 1 ^ 12 * X 2 ^ 2- 8296865 * X 0 ^ 7 * X 1 ^ 11 * X 2 ^ 3+ 18464600 * X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 4- 31126731 * X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 5)

def lit3G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (15620172 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 6- 28958918 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 7- 8791520 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 8- 10994582 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 9
    - 3752240 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 10- 1046212 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 11- 146980 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 12- 10360 * X 0 ^ 7 * X 1 * X 2 ^ 13
    - 236 * X 0 ^ 7 * X 2 ^ 14+ 207130 * X 0 ^ 6 * X 1 ^ 14 * X 2- 2447746 * X 0 ^ 6 * X 1 ^ 13 * X 2 ^ 2+ 11732633 * X 0 ^ 6 * X 1 ^ 12 * X 2 ^ 3
    - 30064140 * X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 4+ 48442123 * X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 5- 45288962 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 6+ 37397912 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 7
    - 8791520 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 8+ 9236650 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 9+ 1503796 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 10+ 921554 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 11
    + 150626 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 12+ 17732 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 13+ 826 * X 0 ^ 6 * X 1 * X 2 ^ 14+ 10 * X 0 ^ 6 * X 2 ^ 15)

def lit3G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-195472 * X 0 ^ 5 * X 1 ^ 15 * X 2+ 2467646 * X 0 ^ 5 * X 1 ^ 14 * X 2 ^ 2- 12694857 * X 0 ^ 5 * X 1 ^ 13 * X 2 ^ 3+ 35567246 * X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 4
    - 61277381 * X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 5+ 68093190 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 6- 52827254 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 7+ 25558752 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 8
    - 10994582 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 9+ 1503796 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 10- 742138 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 11- 55618 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 12
    - 16936 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 13- 1062 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 14- 30 * X 0 ^ 5 * X 1 * X 2 ^ 15+ 138470 * X 0 ^ 4 * X 1 ^ 16 * X 2
    - 1859908 * X 0 ^ 4 * X 1 ^ 15 * X 2 ^ 2+ 10242511 * X 0 ^ 4 * X 1 ^ 14 * X 2 ^ 3- 30951828 * X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 4+ 57816013 * X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 5
    - 70918384 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 6+ 59733308 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 7- 34365200 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 8+ 14549348 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 9)

def lit3G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-3752240 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 10+ 921554 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 11- 55618 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 12+ 16538 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 13
    + 590 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 14+ 42 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 15- 71256 * X 0 ^ 3 * X 1 ^ 17 * X 2+ 1015172 * X 0 ^ 3 * X 1 ^ 16 * X 2 ^ 2
    - 5959936 * X 0 ^ 3 * X 1 ^ 15 * X 2 ^ 3+ 19312400 * X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 4- 38908597 * X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 5+ 51954292 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 6
    - 47750178 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 7+ 30800176 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 8- 14131745 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 9+ 4539720 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 10
    - 1046212 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 11+ 150626 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 12- 16936 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 13+ 590 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 14
    - 34 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 15+ 25144 * X 0 ^ 2 * X 1 ^ 18 * X 2- 378896 * X 0 ^ 2 * X 1 ^ 17 * X 2 ^ 2+ 2362712 * X 0 ^ 2 * X 1 ^ 16 * X 2 ^ 3)

def lit3G_7 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-8169936 * X 0 ^ 2 * X 1 ^ 15 * X 2 ^ 4+ 17656891 * X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 5- 25443268 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 6+ 25401152 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 7
    - 17953568 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 8+ 9090959 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 9- 3284140 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 10+ 846988 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 11
    - 146980 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 12+ 17732 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 13- 1062 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 14+ 42 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 15
    - 5440 * X 0 * X 1 ^ 19 * X 2+ 86488 * X 0 * X 1 ^ 18 * X 2 ^ 2- 570960 * X 0 * X 1 ^ 17 * X 2 ^ 3+ 2098106 * X 0 * X 1 ^ 16 * X 2 ^ 4- 4839408 * X 0 * X 1 ^ 15 * X 2 ^ 5
    + 7478700 * X 0 * X 1 ^ 14 * X 2 ^ 6- 8050518 * X 0 * X 1 ^ 13 * X 2 ^ 7+ 6176768 * X 0 * X 1 ^ 12 * X 2 ^ 8- 3417060 * X 0 * X 1 ^ 11 * X 2 ^ 9
    + 1365188 * X 0 * X 1 ^ 10 * X 2 ^ 10- 390290 * X 0 * X 1 ^ 9 * X 2 ^ 11+ 77958 * X 0 * X 1 ^ 8 * X 2 ^ 12)

def lit3G_8 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-10360 * X 0 * X 1 ^ 7 * X 2 ^ 13+ 826 * X 0 * X 1 ^ 6 * X 2 ^ 14- 30 * X 0 * X 1 ^ 5 * X 2 ^ 15+ 544 * X 1 ^ 20 * X 2- 9104 * X 1 ^ 19 * X 2 ^ 2
    + 63440 * X 1 ^ 18 * X 2 ^ 3- 246836 * X 1 ^ 17 * X 2 ^ 4+ 604926 * X 1 ^ 16 * X 2 ^ 5- 997160 * X 1 ^ 15 * X 2 ^ 6+ 1150074 * X 1 ^ 14 * X 2 ^ 7
    - 950272 * X 1 ^ 13 * X 2 ^ 8+ 569510 * X 1 ^ 12 * X 2 ^ 9- 248216 * X 1 ^ 11 * X 2 ^ 10+ 78058 * X 1 ^ 10 * X 2 ^ 11- 17324 * X 1 ^ 9 * X 2 ^ 12
    + 2590 * X 1 ^ 8 * X 2 ^ 13- 236 * X 1 ^ 7 * X 2 ^ 14+ 10 * X 1 ^ 6 * X 2 ^ 15)

-- The integral half-norm lit3G, the sum of its chunks.
def lit3G : MvPolynomial (Fin 3) ℤ :=
    lit3G_0 + lit3G_1 + lit3G_2 + lit3G_3 + lit3G_4 + lit3G_5 + lit3G_6 + lit3G_7 + lit3G_8

def lit3P_0 : Poly2 :=
    X 0 ^ 14 * X 1 ^ 4 * X 2 ^ 3

def lit3P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 5+ X 0 ^ 13 * X 1 ^ 5 * X 2 ^ 3+ X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 5+ X 0 ^ 12 * X 1 ^ 6 * X 2 ^ 3+ X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 5
    + X 0 ^ 11 * X 1 ^ 7 * X 2 ^ 3)

def lit3P_2 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 5+ X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 5+ X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 9+ X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 5)

def lit3P_3 : Poly2 :=
    X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 9+ X 0 ^ 7 * X 1 ^ 11 * X 2 ^ 3+ X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 5

def lit3P_4 : Poly2 :=
    X 0 ^ 6 * X 1 ^ 12 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 5

def lit3P_5 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 5 * X 1 ^ 13 * X 2 ^ 3+ X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 5+ X 0 ^ 4 * X 1 ^ 14 * X 2 ^ 3+ X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 5)

def lit3P_6 : Poly2 :=
    X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 5+ X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 9

def lit3P_7 : Poly2 :=
    X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 5+ X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 9

def lit3P_8 : Poly2 :=
    0

-- The reduction of lit3G modulo two, the sum of its chunks.
def lit3P : Poly2 :=
    lit3P_0 + lit3P_1 + lit3P_2 + lit3P_3 + lit3P_4 + lit3P_5 + lit3P_6 + lit3P_7 + lit3P_8

theorem lemma56_nu3_half :
    threeTermNorm (baseSym 0 3) = C 2 * lit3G := by
  unfold lit3G lit3G_0 lit3G_1 lit3G_2 lit3G_3 lit3G_4 lit3G_5 lit3G_6 lit3G_7 lit3G_8
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

theorem lemma56_nu3_reduce_0 : reduceTwo lit3G_0 = lit3P_0 := by
  unfold lit3G_0 lit3P_0
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_1 : reduceTwo lit3G_1 = lit3P_1 := by
  unfold lit3G_1 lit3P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_2 : reduceTwo lit3G_2 = lit3P_2 := by
  unfold lit3G_2 lit3P_2
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_3 : reduceTwo lit3G_3 = lit3P_3 := by
  unfold lit3G_3 lit3P_3
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_4 : reduceTwo lit3G_4 = lit3P_4 := by
  unfold lit3G_4 lit3P_4
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_5 : reduceTwo lit3G_5 = lit3P_5 := by
  unfold lit3G_5 lit3P_5
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_6 : reduceTwo lit3G_6 = lit3P_6 := by
  unfold lit3G_6 lit3P_6
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_7 : reduceTwo lit3G_7 = lit3P_7 := by
  unfold lit3G_7 lit3P_7
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce_8 : reduceTwo lit3G_8 = lit3P_8 := by
  unfold lit3G_8 lit3P_8
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu3_reduce : reduceTwo lit3G = lit3P := by
  unfold lit3G lit3P
  simp only [map_add]
  rw [lemma56_nu3_reduce_0, lemma56_nu3_reduce_1, lemma56_nu3_reduce_2, lemma56_nu3_reduce_3, lemma56_nu3_reduce_4, lemma56_nu3_reduce_5, lemma56_nu3_reduce_6, lemma56_nu3_reduce_7, lemma56_nu3_reduce_8]

open PolynomialReflection in
theorem lemma56_nu3_pi : piOperator lit3P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(2, 10, 9), (2, 14, 5), (3, 9, 9), (3, 13, 5), (4, 12, 5), (4, 14, 3), (5, 11, 5),
       (5, 13, 3), (6, 10, 5), (6, 12, 3), (7, 9, 5), (7, 11, 3), (9, 3, 9), (9, 7, 5), (10, 2, 9),
       (10, 6, 5), (11, 5, 5), (11, 7, 3), (12, 4, 5), (12, 6, 3), (13, 3, 5), (13, 5, 3),
       (14, 2, 5), (14, 4, 3)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit3P lit3P_0 lit3P_1 lit3P_2 lit3P_3 lit3P_4 lit3P_5 lit3P_6 lit3P_7 lit3P_8
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
