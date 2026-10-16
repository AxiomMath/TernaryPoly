module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.BaseCases.Base.Cases
public import TernaryPeriodPolynomials.Tactic.PolynomialLiteral

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
-- Half-norm of the symmetric lift of V_2 (column 2), in 5 chunks.
def lit2G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (136 * X 0 ^ 14 * X 2- 952 * X 0 ^ 13 * X 1 * X 2- 1256 * X 0 ^ 13 * X 2 ^ 2+ 2988 * X 0 ^ 12 * X 1 ^ 2 * X 2+ 8164 * X 0 ^ 12 * X 1 * X 2 ^ 2+ 4706 * X 0 ^ 12 * X 2 ^ 3
    - 5552 * X 0 ^ 11 * X 1 ^ 3 * X 2- 23644 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 2- 28236 * X 0 ^ 11 * X 1 * X 2 ^ 3- 9448 * X 0 ^ 11 * X 2 ^ 4+ 6802 * X 0 ^ 10 * X 1 ^ 4 * X 2
    + 40238 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 2+ 74914 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 3+ 51964 * X 0 ^ 10 * X 1 * X 2 ^ 4+ 11408 * X 0 ^ 10 * X 2 ^ 5- 5806 * X 0 ^ 9 * X 1 ^ 5 * X 2
    - 44350 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 2- 115740 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 3- 124792 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 4- 57040 * X 0 ^ 9 * X 1 * X 2 ^ 5
    - 8756 * X 0 ^ 9 * X 2 ^ 6+ 3878 * X 0 ^ 8 * X 1 ^ 6 * X 2+ 32496 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 2+ 117751 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3)

def lit2G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (171834 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 4+ 123563 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 5+ 39402 * X 0 ^ 8 * X 1 * X 2 ^ 6+ 4378 * X 0 ^ 8 * X 2 ^ 7- 2852 * X 0 ^ 7 * X 1 ^ 7 * X 2
    - 11020 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 2- 87160 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 3- 141324 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 4- 152012 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 5
    - 74240 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 6- 17512 * X 0 ^ 7 * X 1 * X 2 ^ 7- 1428 * X 0 ^ 7 * X 2 ^ 8+ 3878 * X 0 ^ 6 * X 1 ^ 8 * X 2- 11020 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 2
    + 72236 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 3+ 56490 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 4+ 132904 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 5+ 75964 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 6
    + 29942 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 7+ 4998 * X 0 ^ 6 * X 1 * X 2 ^ 8+ 296 * X 0 ^ 6 * X 2 ^ 9- 5806 * X 0 ^ 5 * X 1 ^ 9 * X 2+ 32496 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 2
    - 87160 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 3)

def lit2G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (56490 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 4- 106238 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 5- 27992 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 6- 28534 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 7
    - 6426 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 8- 888 * X 0 ^ 5 * X 1 * X 2 ^ 9- 36 * X 0 ^ 5 * X 2 ^ 10+ 6802 * X 0 ^ 4 * X 1 ^ 10 * X 2- 44350 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 2
    + 117751 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3- 141324 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 4+ 132904 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 5- 27992 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 6
    + 27830 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 7+ 3570 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 8+ 1239 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 9+ 90 * X 0 ^ 4 * X 1 * X 2 ^ 10+ 2 * X 0 ^ 4 * X 2 ^ 11
    - 5552 * X 0 ^ 3 * X 1 ^ 11 * X 2+ 40238 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 2- 115740 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 3+ 171834 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 4
    - 152012 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 5+ 75964 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 6)

def lit2G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-28534 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 7+ 3570 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 8- 998 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 9- 36 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 10
    - 4 * X 0 ^ 3 * X 1 * X 2 ^ 11+ 2988 * X 0 ^ 2 * X 1 ^ 12 * X 2- 23644 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 2+ 74914 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 3
    - 124792 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 4+ 123563 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 5- 74240 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 6+ 29942 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 7
    - 6426 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 8+ 1239 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 9- 36 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 10+ 6 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 11- 952 * X 0 * X 1 ^ 13 * X 2
    + 8164 * X 0 * X 1 ^ 12 * X 2 ^ 2- 28236 * X 0 * X 1 ^ 11 * X 2 ^ 3+ 51964 * X 0 * X 1 ^ 10 * X 2 ^ 4- 57040 * X 0 * X 1 ^ 9 * X 2 ^ 5+ 39402 * X 0 * X 1 ^ 8 * X 2 ^ 6
    - 17512 * X 0 * X 1 ^ 7 * X 2 ^ 7+ 4998 * X 0 * X 1 ^ 6 * X 2 ^ 8)

def lit2G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-888 * X 0 * X 1 ^ 5 * X 2 ^ 9+ 90 * X 0 * X 1 ^ 4 * X 2 ^ 10- 4 * X 0 * X 1 ^ 3 * X 2 ^ 11+ 136 * X 1 ^ 14 * X 2- 1256 * X 1 ^ 13 * X 2 ^ 2+ 4706 * X 1 ^ 12 * X 2 ^ 3
    - 9448 * X 1 ^ 11 * X 2 ^ 4+ 11408 * X 1 ^ 10 * X 2 ^ 5- 8756 * X 1 ^ 9 * X 2 ^ 6+ 4378 * X 1 ^ 8 * X 2 ^ 7- 1428 * X 1 ^ 7 * X 2 ^ 8+ 296 * X 1 ^ 6 * X 2 ^ 9
    - 36 * X 1 ^ 5 * X 2 ^ 10+ 2 * X 1 ^ 4 * X 2 ^ 11)

-- The integral half-norm lit2G, the sum of its chunks.
def lit2G : MvPolynomial (Fin 3) ℤ :=
    lit2G_0 + lit2G_1 + lit2G_2 + lit2G_3 + lit2G_4

def lit2P_0 : Poly2 :=
    X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3

def lit2P_1 : Poly2 :=
    X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 5

def lit2P_2 : Poly2 :=
    X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3+ X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 9

def lit2P_3 : Poly2 :=
    X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 5+ X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 9

def lit2P_4 : Poly2 :=
    0

-- The reduction of lit2G modulo two, the sum of its chunks.
def lit2P : Poly2 :=
    lit2P_0 + lit2P_1 + lit2P_2 + lit2P_3 + lit2P_4

theorem lemma56_nu2_half :
    threeTermNorm (baseSym 0 2) = C 2 * lit2G := by
  unfold lit2G lit2G_0 lit2G_1 lit2G_2 lit2G_3 lit2G_4
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, threeTermNorm]
  ring

theorem lemma56_nu2_reduce_0 : reduceTwo lit2G_0 = lit2P_0 := by
  unfold lit2G_0 lit2P_0
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu2_reduce_1 : reduceTwo lit2G_1 = lit2P_1 := by
  unfold lit2G_1 lit2P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu2_reduce_2 : reduceTwo lit2G_2 = lit2P_2 := by
  unfold lit2G_2 lit2P_2
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu2_reduce_3 : reduceTwo lit2G_3 = lit2P_3 := by
  unfold lit2G_3 lit2P_3
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu2_reduce_4 : reduceTwo lit2G_4 = lit2P_4 := by
  unfold lit2G_4 lit2P_4
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu2_reduce : reduceTwo lit2G = lit2P := by
  unfold lit2G lit2P
  simp only [map_add]
  rw [lemma56_nu2_reduce_0, lemma56_nu2_reduce_1, lemma56_nu2_reduce_2, lemma56_nu2_reduce_3, lemma56_nu2_reduce_4]

theorem lemma56_nu2_pi : piOperator lit2P = 0 := by
  unfold lit2P lit2P_0 lit2P_1 lit2P_2 lit2P_3 lit2P_4
  simp [piOperator, piSubstitutions]
  ring_nf
  simp [ofNat_mod_poly2]

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
