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
-- Half-norm of the symmetric lift of V_27 (column 27), in 9 chunks.
def lit27G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-5440 * X 0 ^ 19+ 51680 * X 0 ^ 18 * X 1+ 86688 * X 0 ^ 18 * X 2- 228048 * X 0 ^ 17 * X 1 ^ 2- 780192 * X 0 ^ 17 * X 1 * X 2- 578160 * X 0 ^ 17 * X 2 ^ 2
    + 620568 * X 0 ^ 16 * X 1 ^ 3+ 3255004 * X 0 ^ 16 * X 1 ^ 2 * X 2+ 4914360 * X 0 ^ 16 * X 1 * X 2 ^ 2+ 2195809 * X 0 ^ 16 * X 2 ^ 3- 1165782 * X 0 ^ 15 * X 1 ^ 4
    - 8355680 * X 0 ^ 15 * X 1 ^ 3 * X 2- 19308266 * X 0 ^ 15 * X 1 ^ 2 * X 2 ^ 2- 17566472 * X 0 ^ 15 * X 1 * X 2 ^ 3- 5406606 * X 0 ^ 15 * X 2 ^ 4
    + 1603365 * X 0 ^ 14 * X 1 ^ 5+ 14771392 * X 0 ^ 14 * X 1 ^ 4 * X 2+ 46524795 * X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 2+ 64722300 * X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 3
    + 40549545 * X 0 ^ 14 * X 1 * X 2 ^ 4+ 9258940 * X 0 ^ 14 * X 2 ^ 5- 1668891 * X 0 ^ 13 * X 1 ^ 6- 19070576 * X 0 ^ 13 * X 1 ^ 5 * X 2
    - 76887233 * X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 2)

def lit27G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-145642840 * X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 3- 139420521 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 4- 64812580 * X 0 ^ 13 * X 1 * X 2 ^ 5- 11501918 * X 0 ^ 13 * X 2 ^ 6
    + 1335321 * X 0 ^ 12 * X 1 ^ 7+ 18653017 * X 0 ^ 12 * X 1 ^ 6 * X 2+ 92278797 * X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 2+ 223968116 * X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 3
    + 291231954 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 4+ 206958853 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 5+ 74762467 * X 0 ^ 12 * X 1 * X 2 ^ 6+ 10640802 * X 0 ^ 12 * X 2 ^ 7
    - 797937 * X 0 ^ 11 * X 1 ^ 8- 14287478 * X 0 ^ 11 * X 1 ^ 7 * X 2- 82444217 * X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 2- 249726252 * X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 3
    - 411921729 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 4- 399189578 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 5- 220057662 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 6- 63844812 * X 0 ^ 11 * X 1 * X 2 ^ 7
    - 7441940 * X 0 ^ 11 * X 2 ^ 8+ 257884 * X 0 ^ 10 * X 1 ^ 9+ 9471255 * X 0 ^ 10 * X 1 ^ 8 * X 2+ 53749113 * X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 2)

def lit27G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (212761258 * X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 3+ 415021167 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 4+ 521846969 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 5+ 387930004 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 6
    + 172603626 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 7+ 40930670 * X 0 ^ 10 * X 1 * X 2 ^ 8+ 3971292 * X 0 ^ 10 * X 2 ^ 9+ 257884 * X 0 ^ 9 * X 1 ^ 10
    - 7400172 * X 0 ^ 9 * X 1 ^ 9 * X 2- 17960109 * X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 2- 152465420 * X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 3- 291220992 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 4
    - 494696870 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 5- 450337175 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 6- 277774020 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 7- 99894842 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 8
    - 19856460 * X 0 ^ 9 * X 1 * X 2 ^ 9- 1611784 * X 0 ^ 9 * X 2 ^ 10- 797937 * X 0 ^ 8 * X 1 ^ 11+ 9471255 * X 0 ^ 8 * X 1 ^ 10 * X 2
    - 17960109 * X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 2+ 125702811 * X 0 ^ 8 * X 1 ^ 8 * X 2 ^ 3+ 103870485 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 4+ 387312615 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 5)

def lit27G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (350622963 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 6+ 304915416 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 7+ 142546764 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 8+ 44215980 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 9
    + 7253028 * X 0 ^ 8 * X 1 * X 2 ^ 10+ 499166 * X 0 ^ 8 * X 2 ^ 11+ 1335321 * X 0 ^ 7 * X 1 ^ 12- 14287478 * X 0 ^ 7 * X 1 ^ 11 * X 2
    + 53749113 * X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 2- 152465420 * X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 3+ 103870485 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 4- 324097758 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 5
    - 125667720 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 6- 255310476 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 7- 122513544 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 8- 57725160 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 9
    - 13852484 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 10- 1996664 * X 0 ^ 7 * X 1 * X 2 ^ 11- 113442 * X 0 ^ 7 * X 2 ^ 12- 1668891 * X 0 ^ 6 * X 1 ^ 13
    + 18653017 * X 0 ^ 6 * X 1 ^ 12 * X 2- 82444217 * X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 2+ 212761258 * X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 3- 291220992 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 4)

def lit27G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (387312615 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 5- 125667720 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 6+ 228179730 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 7+ 50093862 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 8
    + 55880940 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 9+ 14636230 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 10+ 3594144 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 11+ 397047 * X 0 ^ 6 * X 1 * X 2 ^ 12
    + 19396 * X 0 ^ 6 * X 2 ^ 13+ 1603365 * X 0 ^ 5 * X 1 ^ 14- 19070576 * X 0 ^ 5 * X 1 ^ 13 * X 2+ 92278797 * X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 2
    - 249726252 * X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 3+ 415021167 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 4- 494696870 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 5+ 350622963 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 6
    - 255310476 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 7+ 50093862 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 8- 49001892 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 9- 5619098 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 10
    - 3794108 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 11- 510489 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 12- 58188 * X 0 ^ 5 * X 1 * X 2 ^ 13- 2086 * X 0 ^ 5 * X 2 ^ 14)

def lit27G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-1165782 * X 0 ^ 4 * X 1 ^ 15+ 14771392 * X 0 ^ 4 * X 1 ^ 14 * X 2- 76887233 * X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 2+ 223968116 * X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 3
    - 411921729 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 4+ 521846969 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 5- 450337175 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 6+ 304915416 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 7
    - 122513544 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 8+ 55880940 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 9- 5619098 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 10+ 3894090 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 11
    + 283605 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 12+ 88578 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 13+ 5215 * X 0 ^ 4 * X 1 * X 2 ^ 14+ 167 * X 0 ^ 4 * X 2 ^ 15+ 620568 * X 0 ^ 3 * X 1 ^ 16
    - 8355680 * X 0 ^ 3 * X 1 ^ 15 * X 2+ 46524795 * X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 2- 145642840 * X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 3+ 291231954 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 4
    - 399189578 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 5+ 387930004 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 6- 277774020 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 7)

def lit27G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (142546764 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 8- 57725160 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 9+ 14636230 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 10- 3794108 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 11
    + 283605 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 12- 80176 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 13- 2086 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 14- 334 * X 0 ^ 3 * X 1 * X 2 ^ 15- 4 * X 0 ^ 3 * X 2 ^ 16
    - 228048 * X 0 ^ 2 * X 1 ^ 17+ 3255004 * X 0 ^ 2 * X 1 ^ 16 * X 2- 19308266 * X 0 ^ 2 * X 1 ^ 15 * X 2 ^ 2+ 64722300 * X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 3
    - 139420521 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 4+ 206958853 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 5- 220057662 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 6+ 172603626 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 7
    - 99894842 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 8+ 44215980 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 9- 13852484 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 10+ 3594144 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 11
    - 510489 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 12+ 88578 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 13- 2086 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 14)

def lit27G_7 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (501 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 15+ 6 * X 0 ^ 2 * X 1 * X 2 ^ 16+ 51680 * X 0 * X 1 ^ 18- 780192 * X 0 * X 1 ^ 17 * X 2+ 4914360 * X 0 * X 1 ^ 16 * X 2 ^ 2
    - 17566472 * X 0 * X 1 ^ 15 * X 2 ^ 3+ 40549545 * X 0 * X 1 ^ 14 * X 2 ^ 4- 64812580 * X 0 * X 1 ^ 13 * X 2 ^ 5+ 74762467 * X 0 * X 1 ^ 12 * X 2 ^ 6
    - 63844812 * X 0 * X 1 ^ 11 * X 2 ^ 7+ 40930670 * X 0 * X 1 ^ 10 * X 2 ^ 8- 19856460 * X 0 * X 1 ^ 9 * X 2 ^ 9+ 7253028 * X 0 * X 1 ^ 8 * X 2 ^ 10
    - 1996664 * X 0 * X 1 ^ 7 * X 2 ^ 11+ 397047 * X 0 * X 1 ^ 6 * X 2 ^ 12- 58188 * X 0 * X 1 ^ 5 * X 2 ^ 13+ 5215 * X 0 * X 1 ^ 4 * X 2 ^ 14- 334 * X 0 * X 1 ^ 3 * X 2 ^ 15
    + 6 * X 0 * X 1 ^ 2 * X 2 ^ 16- 5440 * X 1 ^ 19+ 86688 * X 1 ^ 18 * X 2- 578160 * X 1 ^ 17 * X 2 ^ 2+ 2195809 * X 1 ^ 16 * X 2 ^ 3- 5406606 * X 1 ^ 15 * X 2 ^ 4)

def lit27G_8 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (9258940 * X 1 ^ 14 * X 2 ^ 5- 11501918 * X 1 ^ 13 * X 2 ^ 6+ 10640802 * X 1 ^ 12 * X 2 ^ 7- 7441940 * X 1 ^ 11 * X 2 ^ 8+ 3971292 * X 1 ^ 10 * X 2 ^ 9
    - 1611784 * X 1 ^ 9 * X 2 ^ 10+ 499166 * X 1 ^ 8 * X 2 ^ 11- 113442 * X 1 ^ 7 * X 2 ^ 12+ 19396 * X 1 ^ 6 * X 2 ^ 13- 2086 * X 1 ^ 5 * X 2 ^ 14+ 167 * X 1 ^ 4 * X 2 ^ 15
    - 4 * X 1 ^ 3 * X 2 ^ 16)

-- The integral half-norm lit27G, the sum of its chunks.
def lit27G : MvPolynomial (Fin 3) ℤ :=
    lit27G_0 + lit27G_1 + lit27G_2 + lit27G_3 + lit27G_4 + lit27G_5 + lit27G_6 + lit27G_7 + lit27G_8

def lit27P_0 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 16 * X 2 ^ 3+ X 0 ^ 14 * X 1 ^ 5+ X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 2+ X 0 ^ 14 * X 1 * X 2 ^ 4+ X 0 ^ 13 * X 1 ^ 6+ X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 2)

def lit27P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 4+ X 0 ^ 12 * X 1 ^ 7+ X 0 ^ 12 * X 1 ^ 6 * X 2+ X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 2+ X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 5+ X 0 ^ 12 * X 1 * X 2 ^ 6
    + X 0 ^ 11 * X 1 ^ 8+ X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 2+ X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 4+ X 0 ^ 10 * X 1 ^ 8 * X 2+ X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 2)

def lit27P_2 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 4+ X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 5+ X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 2+ X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 6+ X 0 ^ 8 * X 1 ^ 11+ X 0 ^ 8 * X 1 ^ 10 * X 2
    + X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 2+ X 0 ^ 8 * X 1 ^ 8 * X 2 ^ 3+ X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 4+ X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 5)

def lit27P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 6+ X 0 ^ 7 * X 1 ^ 12+ X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 2+ X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 4+ X 0 ^ 6 * X 1 ^ 13+ X 0 ^ 6 * X 1 ^ 12 * X 2
    + X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 2)

def lit27P_4 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 5+ X 0 ^ 6 * X 1 * X 2 ^ 12+ X 0 ^ 5 * X 1 ^ 14+ X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 2+ X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 4+ X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 6
    + X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 12)

def lit27P_5 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 2+ X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 4+ X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 5+ X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 6+ X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 12
    + X 0 ^ 4 * X 1 * X 2 ^ 14+ X 0 ^ 4 * X 2 ^ 15+ X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 2)

def lit27P_6 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 12+ X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 4+ X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 5+ X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 12)

def lit27P_7 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 15+ X 0 * X 1 ^ 14 * X 2 ^ 4+ X 0 * X 1 ^ 12 * X 2 ^ 6+ X 0 * X 1 ^ 6 * X 2 ^ 12+ X 0 * X 1 ^ 4 * X 2 ^ 14+ X 1 ^ 16 * X 2 ^ 3)

def lit27P_8 : Poly2 :=
    X 1 ^ 4 * X 2 ^ 15

-- The reduction of lit27G modulo two, the sum of its chunks.
def lit27P : Poly2 :=
    lit27P_0 + lit27P_1 + lit27P_2 + lit27P_3 + lit27P_4 + lit27P_5 + lit27P_6 + lit27P_7 + lit27P_8

theorem lemma56_nu27_half :
    threeTermNorm (baseSym 6 3) = C 2 * lit27G := by
  unfold lit27G lit27G_0 lit27G_1 lit27G_2 lit27G_3 lit27G_4 lit27G_5 lit27G_6 lit27G_7 lit27G_8
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

theorem lemma56_nu27_reduce_0 : reduceTwo lit27G_0 = lit27P_0 := by
  unfold lit27G_0 lit27P_0
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_1 : reduceTwo lit27G_1 = lit27P_1 := by
  unfold lit27G_1 lit27P_1
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_2 : reduceTwo lit27G_2 = lit27P_2 := by
  unfold lit27G_2 lit27P_2
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_3 : reduceTwo lit27G_3 = lit27P_3 := by
  unfold lit27G_3 lit27P_3
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_4 : reduceTwo lit27G_4 = lit27P_4 := by
  unfold lit27G_4 lit27P_4
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_5 : reduceTwo lit27G_5 = lit27P_5 := by
  unfold lit27G_5 lit27P_5
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_6 : reduceTwo lit27G_6 = lit27P_6 := by
  unfold lit27G_6 lit27P_6
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_7 : reduceTwo lit27G_7 = lit27P_7 := by
  unfold lit27G_7 lit27P_7
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce_8 : reduceTwo lit27G_8 = lit27P_8 := by
  unfold lit27G_8 lit27P_8
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu27_reduce : reduceTwo lit27G = lit27P := by
  unfold lit27G lit27P
  simp only [map_add]
  rw [lemma56_nu27_reduce_0, lemma56_nu27_reduce_1, lemma56_nu27_reduce_2, lemma56_nu27_reduce_3, lemma56_nu27_reduce_4, lemma56_nu27_reduce_5, lemma56_nu27_reduce_6, lemma56_nu27_reduce_7, lemma56_nu27_reduce_8]

open PolynomialReflection in
theorem lemma56_nu27_pi : piOperator lit27P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(0, 4, 15), (0, 16, 3), (1, 4, 14), (1, 6, 12), (1, 12, 6), (1, 14, 4), (2, 2, 15),
       (2, 5, 12), (2, 12, 5), (2, 13, 4), (3, 4, 12), (3, 14, 2), (4, 0, 15), (4, 1, 14),
       (4, 3, 12), (4, 9, 6), (4, 10, 5), (4, 11, 4), (4, 13, 2), (5, 2, 12), (5, 8, 6),
       (5, 10, 4), (5, 12, 2), (5, 14, 0), (6, 1, 12), (6, 8, 5), (6, 11, 2), (6, 12, 1),
       (6, 13, 0), (7, 8, 4), (7, 10, 2), (7, 12, 0), (8, 5, 6), (8, 6, 5), (8, 7, 4), (8, 8, 3),
       (8, 9, 2), (8, 10, 1), (8, 11, 0), (9, 4, 6), (9, 8, 2), (10, 4, 5), (10, 5, 4), (10, 7, 2),
       (10, 8, 1), (11, 4, 4), (11, 6, 2), (11, 8, 0), (12, 1, 6), (12, 2, 5), (12, 5, 2),
       (12, 6, 1), (12, 7, 0), (13, 2, 4), (13, 4, 2), (13, 6, 0), (14, 1, 4), (14, 3, 2),
       (14, 5, 0), (16, 0, 3)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit27P lit27P_0 lit27P_1 lit27P_2 lit27P_3 lit27P_4 lit27P_5 lit27P_6 lit27P_7 lit27P_8
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
