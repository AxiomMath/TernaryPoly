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
-- Half-norm of the symmetric lift of V_19 (column 19), in 7 chunks.
def lit19G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-1088 * X 0 ^ 17+ 9248 * X 0 ^ 16 * X 1+ 16168 * X 0 ^ 16 * X 2- 36144 * X 0 ^ 15 * X 1 ^ 2- 129344 * X 0 ^ 15 * X 1 * X 2- 97976 * X 0 ^ 15 * X 2 ^ 2
    + 86120 * X 0 ^ 14 * X 1 ^ 3+ 474560 * X 0 ^ 14 * X 1 ^ 2 * X 2+ 734820 * X 0 ^ 14 * X 1 * X 2 ^ 2+ 329765 * X 0 ^ 14 * X 2 ^ 3- 139794 * X 0 ^ 13 * X 1 ^ 4
    - 1058400 * X 0 ^ 13 * X 1 ^ 3 * X 2- 2517744 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 2- 2308355 * X 0 ^ 13 * X 1 * X 2 ^ 3- 702296 * X 0 ^ 13 * X 2 ^ 4+ 163553 * X 0 ^ 12 * X 1 ^ 5
    + 1603911 * X 0 ^ 12 * X 1 ^ 4 * X 2+ 5220566 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 2+ 7346641 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 3+ 4564924 * X 0 ^ 12 * X 1 * X 2 ^ 4
    + 1015027 * X 0 ^ 12 * X 2 ^ 5- 141426 * X 0 ^ 11 * X 1 ^ 6- 1749418 * X 0 ^ 11 * X 1 ^ 5 * X 2- 7300416 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 2)

def lit19G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-14071231 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 3- 13396710 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 4- 6090162 * X 0 ^ 11 * X 1 * X 2 ^ 5- 1036796 * X 0 ^ 11 * X 2 ^ 6
    + 89012 * X 0 ^ 10 * X 1 ^ 7+ 1441639 * X 0 ^ 10 * X 1 ^ 6 * X 2+ 7244556 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 2+ 18175383 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3
    + 23467741 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 4+ 16407178 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 5+ 5702378 * X 0 ^ 10 * X 1 * X 2 ^ 6+ 767638 * X 0 ^ 10 * X 2 ^ 7
    - 28937 * X 0 ^ 9 * X 1 ^ 8- 983570 * X 0 ^ 9 * X 1 ^ 7 * X 2- 4999898 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 2- 16906425 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3
    - 26999675 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 4- 26209405 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5- 13879780 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 6- 3838190 * X 0 ^ 9 * X 1 * X 2 ^ 7
    - 415898 * X 0 ^ 9 * X 2 ^ 8- 28937 * X 0 ^ 8 * X 1 ^ 9+ 785076 * X 0 ^ 8 * X 1 ^ 8 * X 2+ 1765080 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 2)

def lit19G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (12884795 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3+ 20811726 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 4+ 28387942 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5+ 19691175 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 6
    + 8509192 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 7+ 1871541 * X 0 ^ 8 * X 1 * X 2 ^ 8+ 166679 * X 0 ^ 8 * X 2 ^ 9+ 89012 * X 0 ^ 7 * X 1 ^ 10- 983570 * X 0 ^ 7 * X 1 ^ 9 * X 2
    + 1765080 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 2- 10571381 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 3- 7394562 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 4- 23287120 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 5
    - 16806770 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 6- 11007628 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 7- 3568052 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 8- 666716 * X 0 ^ 7 * X 1 * X 2 ^ 9
    - 48032 * X 0 ^ 7 * X 2 ^ 10- 141426 * X 0 ^ 6 * X 1 ^ 11+ 1441639 * X 0 ^ 6 * X 1 ^ 10 * X 2- 4999898 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 2
    + 12884795 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3- 7394562 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 4+ 20568107 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 5)

def lit19G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (6848191 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 6+ 10500686 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 7+ 3754324 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 8+ 1193031 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9
    + 168112 * X 0 ^ 6 * X 1 * X 2 ^ 10+ 10217 * X 0 ^ 6 * X 2 ^ 11+ 163553 * X 0 ^ 5 * X 1 ^ 12- 1749418 * X 0 ^ 5 * X 1 ^ 11 * X 2+ 7244556 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 2
    - 16906425 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3+ 20811726 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 4- 23287120 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 5+ 6848191 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 6
    - 9095758 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 7- 1433966 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 8- 1245587 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9- 216144 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 10
    - 30651 * X 0 ^ 5 * X 1 * X 2 ^ 11- 1362 * X 0 ^ 5 * X 2 ^ 12- 139794 * X 0 ^ 4 * X 1 ^ 13+ 1603911 * X 0 ^ 4 * X 1 ^ 12 * X 2- 7300416 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 2
    + 18175383 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3- 26999675 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 4)

def lit19G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (28387942 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5- 16806770 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 6+ 10500686 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 7- 1433966 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 8
    + 1271865 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 9+ 120080 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 10+ 46392 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 11+ 3405 * X 0 ^ 4 * X 1 * X 2 ^ 12
    + 134 * X 0 ^ 4 * X 2 ^ 13+ 86120 * X 0 ^ 3 * X 1 ^ 14- 1058400 * X 0 ^ 3 * X 1 ^ 13 * X 2+ 5220566 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 2
    - 14071231 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 3+ 23467741 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 4- 26209405 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5+ 19691175 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 6
    - 11007628 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 7+ 3754324 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 8- 1245587 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9+ 120080 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 10
    - 41699 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 11- 1362 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 12- 268 * X 0 ^ 3 * X 1 * X 2 ^ 13- 4 * X 0 ^ 3 * X 2 ^ 14)

def lit19G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-36144 * X 0 ^ 2 * X 1 ^ 15+ 474560 * X 0 ^ 2 * X 1 ^ 14 * X 2- 2517744 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 2+ 7346641 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 3
    - 13396710 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 4+ 16407178 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 5- 13879780 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 6+ 8509192 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 7
    - 3568052 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 8+ 1193031 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9- 216144 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 10+ 46392 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 11
    - 1362 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 12+ 402 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 13+ 6 * X 0 ^ 2 * X 1 * X 2 ^ 14+ 9248 * X 0 * X 1 ^ 16- 129344 * X 0 * X 1 ^ 15 * X 2
    + 734820 * X 0 * X 1 ^ 14 * X 2 ^ 2- 2308355 * X 0 * X 1 ^ 13 * X 2 ^ 3+ 4564924 * X 0 * X 1 ^ 12 * X 2 ^ 4- 6090162 * X 0 * X 1 ^ 11 * X 2 ^ 5
    + 5702378 * X 0 * X 1 ^ 10 * X 2 ^ 6- 3838190 * X 0 * X 1 ^ 9 * X 2 ^ 7+ 1871541 * X 0 * X 1 ^ 8 * X 2 ^ 8)

def lit19G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-666716 * X 0 * X 1 ^ 7 * X 2 ^ 9+ 168112 * X 0 * X 1 ^ 6 * X 2 ^ 10- 30651 * X 0 * X 1 ^ 5 * X 2 ^ 11+ 3405 * X 0 * X 1 ^ 4 * X 2 ^ 12- 268 * X 0 * X 1 ^ 3 * X 2 ^ 13
    + 6 * X 0 * X 1 ^ 2 * X 2 ^ 14- 1088 * X 1 ^ 17+ 16168 * X 1 ^ 16 * X 2- 97976 * X 1 ^ 15 * X 2 ^ 2+ 329765 * X 1 ^ 14 * X 2 ^ 3- 702296 * X 1 ^ 13 * X 2 ^ 4
    + 1015027 * X 1 ^ 12 * X 2 ^ 5- 1036796 * X 1 ^ 11 * X 2 ^ 6+ 767638 * X 1 ^ 10 * X 2 ^ 7- 415898 * X 1 ^ 9 * X 2 ^ 8+ 166679 * X 1 ^ 8 * X 2 ^ 9
    - 48032 * X 1 ^ 7 * X 2 ^ 10+ 10217 * X 1 ^ 6 * X 2 ^ 11- 1362 * X 1 ^ 5 * X 2 ^ 12+ 134 * X 1 ^ 4 * X 2 ^ 13- 4 * X 1 ^ 3 * X 2 ^ 14)

-- The integral half-norm lit19G, the sum of its chunks.
def lit19G : MvPolynomial (Fin 3) ℤ :=
    lit19G_0 + lit19G_1 + lit19G_2 + lit19G_3 + lit19G_4 + lit19G_5 + lit19G_6

def lit19P_0 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 14 * X 2 ^ 3+ X 0 ^ 13 * X 1 * X 2 ^ 3+ X 0 ^ 12 * X 1 ^ 5+ X 0 ^ 12 * X 1 ^ 4 * X 2+ X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 3+ X 0 ^ 12 * X 2 ^ 5)

def lit19P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 3+ X 0 ^ 10 * X 1 ^ 6 * X 2+ X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3+ X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 4+ X 0 ^ 9 * X 1 ^ 8+ X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3
    + X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 4+ X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5+ X 0 ^ 8 * X 1 ^ 9)

def lit19P_2 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3+ X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 6+ X 0 ^ 8 * X 1 * X 2 ^ 8+ X 0 ^ 8 * X 2 ^ 9+ X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 10 * X 2
    + X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 5)

def lit19P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 6+ X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9+ X 0 ^ 6 * X 2 ^ 11+ X 0 ^ 5 * X 1 ^ 12+ X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3+ X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 6
    + X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9+ X 0 ^ 5 * X 1 * X 2 ^ 11+ X 0 ^ 4 * X 1 ^ 12 * X 2+ X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3+ X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 4)

def lit19P_4 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 9+ X 0 ^ 4 * X 1 * X 2 ^ 12+ X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 3+ X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 4+ X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5
    + X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 6+ X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9+ X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 11)

def lit19P_5 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 3+ X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9+ X 0 * X 1 ^ 13 * X 2 ^ 3+ X 0 * X 1 ^ 8 * X 2 ^ 8)

def lit19P_6 : Poly2 :=
  poly_literal% Poly2
    (X 0 * X 1 ^ 5 * X 2 ^ 11+ X 0 * X 1 ^ 4 * X 2 ^ 12+ X 1 ^ 14 * X 2 ^ 3+ X 1 ^ 12 * X 2 ^ 5+ X 1 ^ 8 * X 2 ^ 9+ X 1 ^ 6 * X 2 ^ 11)

-- The reduction of lit19G modulo two, the sum of its chunks.
def lit19P : Poly2 :=
    lit19P_0 + lit19P_1 + lit19P_2 + lit19P_3 + lit19P_4 + lit19P_5 + lit19P_6

theorem lemma56_nu19_half :
    threeTermNorm (baseSym 4 3) = C 2 * lit19G := by
  unfold lit19G lit19G_0 lit19G_1 lit19G_2 lit19G_3 lit19G_4 lit19G_5 lit19G_6
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

theorem lemma56_nu19_reduce_0 : reduceTwo lit19G_0 = lit19P_0 := by
  unfold lit19G_0 lit19P_0
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu19_reduce_1 : reduceTwo lit19G_1 = lit19P_1 := by
  unfold lit19G_1 lit19P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu19_reduce_2 : reduceTwo lit19G_2 = lit19P_2 := by
  unfold lit19G_2 lit19P_2
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu19_reduce_3 : reduceTwo lit19G_3 = lit19P_3 := by
  unfold lit19G_3 lit19P_3
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu19_reduce_4 : reduceTwo lit19G_4 = lit19P_4 := by
  unfold lit19G_4 lit19P_4
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu19_reduce_5 : reduceTwo lit19G_5 = lit19P_5 := by
  unfold lit19G_5 lit19P_5
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu19_reduce_6 : reduceTwo lit19G_6 = lit19P_6 := by
  unfold lit19G_6 lit19P_6
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu19_reduce : reduceTwo lit19G = lit19P := by
  unfold lit19G lit19P
  simp only [map_add]
  rw [lemma56_nu19_reduce_0, lemma56_nu19_reduce_1, lemma56_nu19_reduce_2, lemma56_nu19_reduce_3, lemma56_nu19_reduce_4, lemma56_nu19_reduce_5, lemma56_nu19_reduce_6]

open PolynomialReflection in
theorem lemma56_nu19_pi : piOperator lit19P = d6 * oddGenerator 0 + d4 * oddGenerator 2 + d4 * d6 * oddGenerator 3 := by
  refine piOperator_eq_of_reflect (lP :=
      [(0, 6, 11), (0, 8, 9), (0, 12, 5), (0, 14, 3), (1, 4, 12), (1, 5, 11), (1, 8, 8),
       (1, 13, 3), (2, 6, 9), (2, 12, 3), (3, 3, 11), (3, 5, 9), (3, 8, 6), (3, 9, 5), (3, 10, 4),
       (3, 11, 3), (4, 1, 12), (4, 4, 9), (4, 9, 4), (4, 10, 3), (4, 12, 1), (5, 1, 11), (5, 3, 9),
       (5, 6, 6), (5, 9, 3), (5, 12, 0), (6, 0, 11), (6, 2, 9), (6, 5, 6), (6, 6, 5), (6, 8, 3),
       (6, 10, 1), (7, 7, 3), (8, 0, 9), (8, 1, 8), (8, 3, 6), (8, 6, 3), (8, 9, 0), (9, 3, 5),
       (9, 4, 4), (9, 5, 3), (9, 8, 0), (10, 3, 4), (10, 4, 3), (10, 6, 1), (11, 3, 3), (12, 0, 5),
       (12, 2, 3), (12, 4, 1), (12, 5, 0), (13, 1, 3), (14, 0, 3)])
    (lQ := addL (addL (mulL d6L (oddGeneratorL 0)) (mulL d4L (oddGeneratorL 2))) (mulL (mulL d4L d6L) (oddGeneratorL 3))) ?_ ?_ ?_
  · unfold lit19P lit19P_0 lit19P_1 lit19P_2 lit19P_3 lit19P_4 lit19P_5 lit19P_6
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_addL, ev_mulL, ev_d4, ev_d6, ev_oddGenerator]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
