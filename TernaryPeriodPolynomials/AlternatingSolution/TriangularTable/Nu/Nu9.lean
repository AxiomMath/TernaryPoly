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
-- Half-norm of the symmetric lift of V_9 (column 9), in 8 chunks.
def lit9G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (160 * X 0 ^ 18 * X 2- 1440 * X 0 ^ 17 * X 1 * X 2- 2512 * X 0 ^ 17 * X 2 ^ 2+ 5912 * X 0 ^ 16 * X 1 ^ 2 * X 2+ 21352 * X 0 ^ 16 * X 1 * X 2 ^ 2
    + 16016 * X 0 ^ 16 * X 2 ^ 3- 14656 * X 0 ^ 15 * X 1 ^ 3 * X 2- 82552 * X 0 ^ 15 * X 1 ^ 2 * X 2 ^ 2- 128128 * X 0 ^ 15 * X 1 * X 2 ^ 3- 55364 * X 0 ^ 15 * X 2 ^ 4
    + 24470 * X 0 ^ 14 * X 1 ^ 4 * X 2+ 192100 * X 0 ^ 14 * X 1 ^ 3 * X 2 ^ 2+ 464520 * X 0 ^ 14 * X 1 ^ 2 * X 2 ^ 3+ 415230 * X 0 ^ 14 * X 1 * X 2 ^ 4
    + 116502 * X 0 ^ 14 * X 2 ^ 5- 29050 * X 0 ^ 13 * X 1 ^ 5 * X 2- 299980 * X 0 ^ 13 * X 1 ^ 4 * X 2 ^ 2- 1009400 * X 0 ^ 13 * X 1 ^ 3 * X 2 ^ 3
    - 1404810 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 4- 815514 * X 0 ^ 13 * X 1 * X 2 ^ 5- 158760 * X 0 ^ 13 * X 2 ^ 6+ 25238 * X 0 ^ 12 * X 1 ^ 6 * X 2
    + 331708 * X 0 ^ 12 * X 1 ^ 5 * X 2 ^ 2+ 1465150 * X 0 ^ 12 * X 1 ^ 4 * X 2 ^ 3)

def lit9G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2833610 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 4+ 2560430 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 5+ 1031940 * X 0 ^ 12 * X 1 * X 2 ^ 6+ 145170 * X 0 ^ 12 * X 2 ^ 7
    - 16306 * X 0 ^ 11 * X 1 ^ 7 * X 2- 266188 * X 0 ^ 11 * X 1 ^ 6 * X 2 ^ 2- 1498524 * X 0 ^ 11 * X 1 ^ 5 * X 2 ^ 3- 3791502 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 4
    - 4760898 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 5- 2986684 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 6- 871020 * X 0 ^ 11 * X 1 * X 2 ^ 7- 90652 * X 0 ^ 11 * X 2 ^ 8
    + 8412 * X 0 ^ 10 * X 1 ^ 8 * X 2+ 153868 * X 0 ^ 10 * X 1 ^ 7 * X 2 ^ 2+ 1121774 * X 0 ^ 10 * X 1 ^ 6 * X 2 ^ 3+ 3538392 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 4
    + 5843216 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 5+ 5075422 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 6+ 2307882 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 7+ 498586 * X 0 ^ 10 * X 1 * X 2 ^ 8
    + 38704 * X 0 ^ 10 * X 2 ^ 9- 5320 * X 0 ^ 9 * X 1 ^ 9 * X 2- 46540 * X 0 ^ 9 * X 1 ^ 8 * X 2 ^ 2- 661180 * X 0 ^ 9 * X 1 ^ 7 * X 2 ^ 3)

def lit9G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-2275556 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 4- 5010932 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 5- 5581550 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 6- 3555060 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 7
    - 1195622 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 8- 193520 * X 0 ^ 9 * X 1 * X 2 ^ 9- 11096 * X 0 ^ 9 * X 2 ^ 10+ 8412 * X 0 ^ 8 * X 1 ^ 10 * X 2
    - 46540 * X 0 ^ 8 * X 1 ^ 9 * X 2 ^ 2+ 475560 * X 0 ^ 8 * X 1 ^ 8 * X 2 ^ 3+ 767682 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 4+ 3382196 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 5
    + 4078320 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 6+ 3597258 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 7+ 1640904 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 8+ 418446 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 9
    + 49932 * X 0 ^ 8 * X 1 * X 2 ^ 10+ 2038 * X 0 ^ 8 * X 2 ^ 11- 16306 * X 0 ^ 7 * X 1 ^ 11 * X 2+ 153868 * X 0 ^ 7 * X 1 ^ 10 * X 2 ^ 2
    - 661180 * X 0 ^ 7 * X 1 ^ 9 * X 2 ^ 3+ 767682 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 4- 2513498 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 5- 1379308 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 6)

def lit9G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-2639892 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 7- 1343824 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 8- 512664 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 9- 93992 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 10
    - 8152 * X 0 ^ 7 * X 1 * X 2 ^ 11- 216 * X 0 ^ 7 * X 2 ^ 12+ 25238 * X 0 ^ 6 * X 1 ^ 12 * X 2- 266188 * X 0 ^ 6 * X 1 ^ 11 * X 2 ^ 2
    + 1121774 * X 0 ^ 6 * X 1 ^ 10 * X 2 ^ 3- 2275556 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 4+ 3382196 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 5- 1379308 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 6
    + 2176494 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 7+ 535934 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 8+ 444768 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 9+ 95956 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 10
    + 13916 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 11+ 756 * X 0 ^ 6 * X 1 * X 2 ^ 12+ 10 * X 0 ^ 6 * X 2 ^ 13- 29050 * X 0 ^ 5 * X 1 ^ 13 * X 2+ 331708 * X 0 ^ 5 * X 1 ^ 12 * X 2 ^ 2
    - 1498524 * X 0 ^ 5 * X 1 ^ 11 * X 2 ^ 3+ 3538392 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 4- 5010932 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 5)

def lit9G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (4078320 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 6- 2639892 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 7+ 535934 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 8- 352764 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 9
    - 35252 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 10- 13216 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 11- 972 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 12- 30 * X 0 ^ 5 * X 1 * X 2 ^ 13
    + 24470 * X 0 ^ 4 * X 1 ^ 14 * X 2- 299980 * X 0 ^ 4 * X 1 ^ 13 * X 2 ^ 2+ 1465150 * X 0 ^ 4 * X 1 ^ 12 * X 2 ^ 3- 3791502 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 4
    + 5843216 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 5- 5581550 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 6+ 3597258 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 7- 1343824 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 8
    + 444768 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 9- 35252 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 10+ 12866 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 11+ 540 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 12
    + 42 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 13- 14656 * X 0 ^ 3 * X 1 ^ 15 * X 2+ 192100 * X 0 ^ 3 * X 1 ^ 14 * X 2 ^ 2- 1009400 * X 0 ^ 3 * X 1 ^ 13 * X 2 ^ 3)

def lit9G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2833610 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 4- 4760898 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 5+ 5075422 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 6- 3555060 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 7
    + 1640904 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 8- 512664 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 9+ 95956 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 10- 13216 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 11
    + 540 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 12- 34 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 13+ 5912 * X 0 ^ 2 * X 1 ^ 16 * X 2- 82552 * X 0 ^ 2 * X 1 ^ 15 * X 2 ^ 2
    + 464520 * X 0 ^ 2 * X 1 ^ 14 * X 2 ^ 3- 1404810 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 4+ 2560430 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 5- 2986684 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 6
    + 2307882 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 7- 1195622 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 8+ 418446 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 9- 93992 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 10
    + 13916 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 11- 972 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 12+ 42 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 13- 1440 * X 0 * X 1 ^ 17 * X 2)

def lit9G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (21352 * X 0 * X 1 ^ 16 * X 2 ^ 2- 128128 * X 0 * X 1 ^ 15 * X 2 ^ 3+ 415230 * X 0 * X 1 ^ 14 * X 2 ^ 4- 815514 * X 0 * X 1 ^ 13 * X 2 ^ 5
    + 1031940 * X 0 * X 1 ^ 12 * X 2 ^ 6- 871020 * X 0 * X 1 ^ 11 * X 2 ^ 7+ 498586 * X 0 * X 1 ^ 10 * X 2 ^ 8- 193520 * X 0 * X 1 ^ 9 * X 2 ^ 9
    + 49932 * X 0 * X 1 ^ 8 * X 2 ^ 10- 8152 * X 0 * X 1 ^ 7 * X 2 ^ 11+ 756 * X 0 * X 1 ^ 6 * X 2 ^ 12- 30 * X 0 * X 1 ^ 5 * X 2 ^ 13+ 160 * X 1 ^ 18 * X 2
    - 2512 * X 1 ^ 17 * X 2 ^ 2+ 16016 * X 1 ^ 16 * X 2 ^ 3- 55364 * X 1 ^ 15 * X 2 ^ 4+ 116502 * X 1 ^ 14 * X 2 ^ 5- 158760 * X 1 ^ 13 * X 2 ^ 6+ 145170 * X 1 ^ 12 * X 2 ^ 7
    - 90652 * X 1 ^ 11 * X 2 ^ 8+ 38704 * X 1 ^ 10 * X 2 ^ 9- 11096 * X 1 ^ 9 * X 2 ^ 10+ 2038 * X 1 ^ 8 * X 2 ^ 11- 216 * X 1 ^ 7 * X 2 ^ 12)

def lit9G_7 : MvPolynomial (Fin 3) ℤ :=
    10 * X 1 ^ 6 * X 2 ^ 13

-- The integral half-norm lit9G, the sum of its chunks.
def lit9G : MvPolynomial (Fin 3) ℤ :=
    lit9G_0 + lit9G_1 + lit9G_2 + lit9G_3 + lit9G_4 + lit9G_5 + lit9G_6 + lit9G_7

def lit9P_0 : Poly2 :=
    0

def lit9P_1 : Poly2 :=
    0

def lit9P_2 : Poly2 :=
    0

def lit9P_3 : Poly2 :=
    0

def lit9P_4 : Poly2 :=
    0

def lit9P_5 : Poly2 :=
    0

def lit9P_6 : Poly2 :=
    0

def lit9P_7 : Poly2 :=
    0

-- The reduction of lit9G modulo two, the sum of its chunks.
def lit9P : Poly2 :=
    lit9P_0 + lit9P_1 + lit9P_2 + lit9P_3 + lit9P_4 + lit9P_5 + lit9P_6 + lit9P_7

theorem lemma56_nu9_half :
    threeTermNorm (baseSym 2 1) = C 2 * lit9G := by
  unfold lit9G lit9G_0 lit9G_1 lit9G_2 lit9G_3 lit9G_4 lit9G_5 lit9G_6 lit9G_7
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD6, threeTermNorm]
  ring

theorem lemma56_nu9_reduce_0 : reduceTwo lit9G_0 = lit9P_0 := by
  unfold lit9G_0 lit9P_0
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce_1 : reduceTwo lit9G_1 = lit9P_1 := by
  unfold lit9G_1 lit9P_1
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce_2 : reduceTwo lit9G_2 = lit9P_2 := by
  unfold lit9G_2 lit9P_2
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce_3 : reduceTwo lit9G_3 = lit9P_3 := by
  unfold lit9G_3 lit9P_3
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce_4 : reduceTwo lit9G_4 = lit9P_4 := by
  unfold lit9G_4 lit9P_4
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce_5 : reduceTwo lit9G_5 = lit9P_5 := by
  unfold lit9G_5 lit9P_5
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce_6 : reduceTwo lit9G_6 = lit9P_6 := by
  unfold lit9G_6 lit9P_6
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce_7 : reduceTwo lit9G_7 = lit9P_7 := by
  unfold lit9G_7 lit9P_7
  simp [reduceTwo]
  try ring_nf
  try simp [ofNat_mod_poly2]

theorem lemma56_nu9_reduce : reduceTwo lit9G = lit9P := by
  unfold lit9G lit9P
  simp only [map_add]
  rw [lemma56_nu9_reduce_0, lemma56_nu9_reduce_1, lemma56_nu9_reduce_2, lemma56_nu9_reduce_3, lemma56_nu9_reduce_4, lemma56_nu9_reduce_5, lemma56_nu9_reduce_6, lemma56_nu9_reduce_7]

theorem lemma56_nu9_pi : piOperator lit9P = 0 := by
  unfold lit9P lit9P_0 lit9P_1 lit9P_2 lit9P_3 lit9P_4 lit9P_5 lit9P_6 lit9P_7
  simp [piOperator, piSubstitutions]

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
