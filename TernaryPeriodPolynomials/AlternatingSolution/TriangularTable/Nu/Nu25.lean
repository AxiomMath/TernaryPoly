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
-- Half-norm of the symmetric lift of V_25 (column 25), in 6 chunks.
def lit25G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-320 * X 0 ^ 15+ 2400 * X 0 ^ 14 * X 1+ 4384 * X 0 ^ 14 * X 2- 8144 * X 0 ^ 13 * X 1 ^ 2- 30688 * X 0 ^ 13 * X 1 * X 2- 23664 * X 0 ^ 13 * X 2 ^ 2
    + 16536 * X 0 ^ 12 * X 1 ^ 3+ 96892 * X 0 ^ 12 * X 1 ^ 2 * X 2+ 153816 * X 0 ^ 12 * X 1 * X 2 ^ 2+ 68641 * X 0 ^ 12 * X 2 ^ 3- 22364 * X 0 ^ 11 * X 1 ^ 4
    - 182408 * X 0 ^ 11 * X 1 ^ 3 * X 2- 448690 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 2- 411846 * X 0 ^ 11 * X 1 * X 2 ^ 3- 122146 * X 0 ^ 11 * X 2 ^ 4+ 21186 * X 0 ^ 10 * X 1 ^ 5
    + 228659 * X 0 ^ 10 * X 1 ^ 4 * X 2+ 775819 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 2+ 1103188 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 3+ 671803 * X 0 ^ 10 * X 1 * X 2 ^ 4
    + 143141 * X 0 ^ 10 * X 2 ^ 5- 13862 * X 0 ^ 9 * X 1 ^ 6- 202619 * X 0 ^ 9 * X 1 ^ 5 * X 2- 875825 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 2)

def lit25G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-1740685 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 3- 1629247 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 4- 715705 * X 0 ^ 9 * X 1 * X 2 ^ 5- 114556 * X 0 ^ 9 * X 2 ^ 6+ 4728 * X 0 ^ 8 * X 1 ^ 7
    + 143553 * X 0 ^ 8 * X 1 ^ 6 * X 2+ 660534 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 2+ 1842727 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3+ 2293089 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 4
    + 1578497 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 5+ 515502 * X 0 ^ 8 * X 1 * X 2 ^ 6+ 64104 * X 0 ^ 8 * X 2 ^ 7+ 4728 * X 0 ^ 7 * X 1 ^ 8- 111162 * X 0 ^ 7 * X 1 ^ 7 * X 2
    - 230158 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 2- 1457104 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 3- 1938414 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 4- 2019758 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 5
    - 980994 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 6- 256416 * X 0 ^ 7 * X 1 * X 2 ^ 7- 24646 * X 0 ^ 7 * X 2 ^ 8- 13862 * X 0 ^ 6 * X 1 ^ 9+ 143553 * X 0 ^ 6 * X 1 ^ 8 * X 2
    - 230158 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 2)

def lit25G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (1258799 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 3+ 785988 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 4+ 1892401 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 5+ 1027803 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 6
    + 456174 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 7+ 86261 * X 0 ^ 6 * X 1 * X 2 ^ 8+ 6667 * X 0 ^ 6 * X 2 ^ 9+ 21186 * X 0 ^ 5 * X 1 ^ 10- 202619 * X 0 ^ 5 * X 1 ^ 9 * X 2
    + 660534 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 2- 1457104 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 3+ 785988 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 4- 1614011 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 5
    - 390477 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 6- 471066 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 7- 110907 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 8- 20001 * X 0 ^ 5 * X 1 * X 2 ^ 9
    - 1084 * X 0 ^ 5 * X 2 ^ 10- 22364 * X 0 ^ 4 * X 1 ^ 11+ 228659 * X 0 ^ 4 * X 1 ^ 10 * X 2- 875825 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 2+ 1842727 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3
    - 1938414 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 4+ 1892401 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 5)

def lit25G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-390477 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 6+ 478512 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 7+ 61615 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 8+ 30126 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 9
    + 2710 * X 0 ^ 4 * X 1 * X 2 ^ 10+ 123 * X 0 ^ 4 * X 2 ^ 11+ 16536 * X 0 ^ 3 * X 1 ^ 12- 182408 * X 0 ^ 3 * X 1 ^ 11 * X 2+ 775819 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 2
    - 1740685 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 3+ 2293089 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 4- 2019758 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 5+ 1027803 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 6
    - 471066 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 7+ 61615 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 8- 26917 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 9- 1084 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 10
    - 246 * X 0 ^ 3 * X 1 * X 2 ^ 11- 4 * X 0 ^ 3 * X 2 ^ 12- 8144 * X 0 ^ 2 * X 1 ^ 13+ 96892 * X 0 ^ 2 * X 1 ^ 12 * X 2- 448690 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 2
    + 1103188 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 3- 1629247 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 4)

def lit25G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (1578497 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 5- 980994 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 6+ 456174 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 7- 110907 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 8
    + 30126 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 9- 1084 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 10+ 369 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 11+ 6 * X 0 ^ 2 * X 1 * X 2 ^ 12+ 2400 * X 0 * X 1 ^ 14
    - 30688 * X 0 * X 1 ^ 13 * X 2+ 153816 * X 0 * X 1 ^ 12 * X 2 ^ 2- 411846 * X 0 * X 1 ^ 11 * X 2 ^ 3+ 671803 * X 0 * X 1 ^ 10 * X 2 ^ 4- 715705 * X 0 * X 1 ^ 9 * X 2 ^ 5
    + 515502 * X 0 * X 1 ^ 8 * X 2 ^ 6- 256416 * X 0 * X 1 ^ 7 * X 2 ^ 7+ 86261 * X 0 * X 1 ^ 6 * X 2 ^ 8- 20001 * X 0 * X 1 ^ 5 * X 2 ^ 9+ 2710 * X 0 * X 1 ^ 4 * X 2 ^ 10
    - 246 * X 0 * X 1 ^ 3 * X 2 ^ 11+ 6 * X 0 * X 1 ^ 2 * X 2 ^ 12- 320 * X 1 ^ 15+ 4384 * X 1 ^ 14 * X 2- 23664 * X 1 ^ 13 * X 2 ^ 2)

def lit25G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (68641 * X 1 ^ 12 * X 2 ^ 3- 122146 * X 1 ^ 11 * X 2 ^ 4+ 143141 * X 1 ^ 10 * X 2 ^ 5- 114556 * X 1 ^ 9 * X 2 ^ 6+ 64104 * X 1 ^ 8 * X 2 ^ 7- 24646 * X 1 ^ 7 * X 2 ^ 8
    + 6667 * X 1 ^ 6 * X 2 ^ 9- 1084 * X 1 ^ 5 * X 2 ^ 10+ 123 * X 1 ^ 4 * X 2 ^ 11- 4 * X 1 ^ 3 * X 2 ^ 12)

-- The integral half-norm lit25G, the sum of its chunks.
def lit25G : MvPolynomial (Fin 3) ℤ :=
    lit25G_0 + lit25G_1 + lit25G_2 + lit25G_3 + lit25G_4 + lit25G_5

def lit25P_0 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 12 * X 2 ^ 3+ X 0 ^ 10 * X 1 ^ 4 * X 2+ X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 2+ X 0 ^ 10 * X 1 * X 2 ^ 4+ X 0 ^ 10 * X 2 ^ 5+ X 0 ^ 9 * X 1 ^ 5 * X 2
    + X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 2)

def lit25P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 3+ X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 4+ X 0 ^ 9 * X 1 * X 2 ^ 5+ X 0 ^ 8 * X 1 ^ 6 * X 2+ X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 3+ X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 4
    + X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 5+ X 0 ^ 6 * X 1 ^ 8 * X 2)

def lit25P_2 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 5+ X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 6+ X 0 ^ 6 * X 1 * X 2 ^ 8+ X 0 ^ 6 * X 2 ^ 9+ X 0 ^ 5 * X 1 ^ 9 * X 2
    + X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 5+ X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 6+ X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 8+ X 0 ^ 5 * X 1 * X 2 ^ 9+ X 0 ^ 4 * X 1 ^ 10 * X 2+ X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 2
    + X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 3+ X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 5)

def lit25P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 6+ X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 8+ X 0 ^ 4 * X 2 ^ 11+ X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 2+ X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 3+ X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 4
    + X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 6+ X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 8+ X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 9+ X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 4)

def lit25P_4 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 5+ X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 8+ X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 11+ X 0 * X 1 ^ 10 * X 2 ^ 4+ X 0 * X 1 ^ 9 * X 2 ^ 5+ X 0 * X 1 ^ 6 * X 2 ^ 8
    + X 0 * X 1 ^ 5 * X 2 ^ 9)

def lit25P_5 : Poly2 :=
    X 1 ^ 12 * X 2 ^ 3+ X 1 ^ 10 * X 2 ^ 5+ X 1 ^ 6 * X 2 ^ 9+ X 1 ^ 4 * X 2 ^ 11

-- The reduction of lit25G modulo two, the sum of its chunks.
def lit25P : Poly2 :=
    lit25P_0 + lit25P_1 + lit25P_2 + lit25P_3 + lit25P_4 + lit25P_5

theorem lemma56_nu25_half :
    threeTermNorm (baseSym 6 1) = C 2 * lit25G := by
  unfold lit25G lit25G_0 lit25G_1 lit25G_2 lit25G_3 lit25G_4 lit25G_5
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD6, threeTermNorm]
  ring

theorem lemma56_nu25_reduce_0 : reduceTwo lit25G_0 = lit25P_0 := by
  unfold lit25G_0 lit25P_0
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu25_reduce_1 : reduceTwo lit25G_1 = lit25P_1 := by
  unfold lit25G_1 lit25P_1
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu25_reduce_2 : reduceTwo lit25G_2 = lit25P_2 := by
  unfold lit25G_2 lit25P_2
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu25_reduce_3 : reduceTwo lit25G_3 = lit25P_3 := by
  unfold lit25G_3 lit25P_3
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu25_reduce_4 : reduceTwo lit25G_4 = lit25P_4 := by
  unfold lit25G_4 lit25P_4
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu25_reduce_5 : reduceTwo lit25G_5 = lit25P_5 := by
  unfold lit25G_5 lit25P_5
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu25_reduce : reduceTwo lit25G = lit25P := by
  unfold lit25G lit25P
  simp only [map_add]
  rw [lemma56_nu25_reduce_0, lemma56_nu25_reduce_1, lemma56_nu25_reduce_2, lemma56_nu25_reduce_3, lemma56_nu25_reduce_4, lemma56_nu25_reduce_5]

open PolynomialReflection in
theorem lemma56_nu25_pi : piOperator lit25P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(0, 4, 11), (0, 6, 9), (0, 10, 5), (0, 12, 3), (1, 5, 9), (1, 6, 8), (1, 9, 5), (1, 10, 4),
       (2, 2, 11), (2, 5, 8), (2, 8, 5), (2, 9, 4), (3, 3, 9), (3, 4, 8), (3, 6, 6), (3, 8, 4),
       (3, 9, 3), (3, 10, 2), (4, 0, 11), (4, 3, 8), (4, 5, 6), (4, 6, 5), (4, 8, 3), (4, 9, 2),
       (4, 10, 1), (5, 1, 9), (5, 2, 8), (5, 4, 6), (5, 5, 5), (5, 9, 1), (6, 0, 9), (6, 1, 8),
       (6, 3, 6), (6, 4, 5), (6, 6, 3), (6, 8, 1), (8, 2, 5), (8, 3, 4), (8, 4, 3), (8, 6, 1),
       (9, 1, 5), (9, 2, 4), (9, 3, 3), (9, 4, 2), (9, 5, 1), (10, 0, 5), (10, 1, 4), (10, 3, 2),
       (10, 4, 1), (12, 0, 3)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit25P lit25P_0 lit25P_1 lit25P_2 lit25P_3 lit25P_4 lit25P_5
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
