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
-- Half-norm of the symmetric lift of V_1 (column 1), in 6 chunks.
def lit1G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (32 * X 0 ^ 16 * X 2- 256 * X 0 ^ 15 * X 1 * X 2- 464 * X 0 ^ 15 * X 2 ^ 2+ 920 * X 0 ^ 14 * X 1 ^ 2 * X 2+ 3480 * X 0 ^ 14 * X 1 * X 2 ^ 2+ 2640 * X 0 ^ 14 * X 2 ^ 3
    - 1960 * X 0 ^ 13 * X 1 ^ 3 * X 2- 11680 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 2- 18480 * X 0 ^ 13 * X 1 * X 2 ^ 3- 7812 * X 0 ^ 13 * X 2 ^ 4+ 2750 * X 0 ^ 12 * X 1 ^ 4 * X 2
    + 23140 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 2+ 57608 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 3+ 50778 * X 0 ^ 12 * X 1 * X 2 ^ 4+ 13398 * X 0 ^ 12 * X 2 ^ 5
    - 2668 * X 0 ^ 11 * X 1 ^ 5 * X 2- 30040 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 2- 105408 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 3- 146064 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 4
    - 80388 * X 0 ^ 11 * X 1 * X 2 ^ 5- 14112 * X 0 ^ 11 * X 2 ^ 6+ 1838 * X 0 ^ 10 * X 1 ^ 6 * X 2+ 26796 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 2
    + 125723 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3)

def lit1G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (244794 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 4+ 211783 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 5+ 77616 * X 0 ^ 10 * X 1 * X 2 ^ 6+ 9420 * X 0 ^ 10 * X 2 ^ 7- 940 * X 0 ^ 9 * X 1 ^ 7 * X 2
    - 16280 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 2- 102815 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3- 263400 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 4- 322025 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5
    - 185264 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 6- 47100 * X 0 ^ 9 * X 1 * X 2 ^ 7- 4004 * X 0 ^ 9 * X 2 ^ 8+ 600 * X 0 ^ 8 * X 1 ^ 8 * X 2+ 5280 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 2
    + 64169 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3+ 187182 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 4+ 317725 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5+ 251568 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 6
    + 101274 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 7+ 18018 * X 0 ^ 8 * X 1 * X 2 ^ 8+ 1052 * X 0 ^ 8 * X 2 ^ 9- 940 * X 0 ^ 7 * X 1 ^ 9 * X 2+ 5280 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 2
    - 44234 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 3)

def lit1G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-61572 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 4- 223018 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 5- 203168 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 6- 122496 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 7
    - 33816 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 8- 4208 * X 0 ^ 7 * X 1 * X 2 ^ 9- 156 * X 0 ^ 7 * X 2 ^ 10+ 1838 * X 0 ^ 6 * X 1 ^ 10 * X 2- 16280 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 2
    + 64169 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3- 61572 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 4+ 178448 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 5+ 80416 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 6
    + 103692 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 7+ 34272 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 8+ 7137 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9+ 546 * X 0 ^ 6 * X 1 * X 2 ^ 10+ 10 * X 0 ^ 6 * X 2 ^ 11
    - 2668 * X 0 ^ 5 * X 1 ^ 11 * X 2+ 26796 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 2- 102815 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3+ 187182 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 4
    - 223018 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 5+ 80416 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 6)

def lit1G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-80160 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 7- 12468 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 8- 6683 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9- 702 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 10
    - 30 * X 0 ^ 5 * X 1 * X 2 ^ 11+ 2750 * X 0 ^ 4 * X 1 ^ 12 * X 2- 30040 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 2+ 125723 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3
    - 263400 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 4+ 317725 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5- 203168 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 6+ 103692 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 7
    - 12468 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 8+ 6456 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 9+ 390 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 10+ 42 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 11
    - 1960 * X 0 ^ 3 * X 1 ^ 13 * X 2+ 23140 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 2- 105408 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 3+ 244794 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 4
    - 322025 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5+ 251568 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 6- 122496 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 7+ 34272 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 8)

def lit1G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-6683 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9+ 390 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 10- 34 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 11+ 920 * X 0 ^ 2 * X 1 ^ 14 * X 2
    - 11680 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 2+ 57608 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 3- 146064 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 4+ 211783 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 5
    - 185264 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 6+ 101274 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 7- 33816 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 8+ 7137 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9
    - 702 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 10+ 42 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 11- 256 * X 0 * X 1 ^ 15 * X 2+ 3480 * X 0 * X 1 ^ 14 * X 2 ^ 2- 18480 * X 0 * X 1 ^ 13 * X 2 ^ 3
    + 50778 * X 0 * X 1 ^ 12 * X 2 ^ 4- 80388 * X 0 * X 1 ^ 11 * X 2 ^ 5+ 77616 * X 0 * X 1 ^ 10 * X 2 ^ 6- 47100 * X 0 * X 1 ^ 9 * X 2 ^ 7+ 18018 * X 0 * X 1 ^ 8 * X 2 ^ 8
    - 4208 * X 0 * X 1 ^ 7 * X 2 ^ 9+ 546 * X 0 * X 1 ^ 6 * X 2 ^ 10)

def lit1G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-30 * X 0 * X 1 ^ 5 * X 2 ^ 11+ 32 * X 1 ^ 16 * X 2- 464 * X 1 ^ 15 * X 2 ^ 2+ 2640 * X 1 ^ 14 * X 2 ^ 3- 7812 * X 1 ^ 13 * X 2 ^ 4+ 13398 * X 1 ^ 12 * X 2 ^ 5
    - 14112 * X 1 ^ 11 * X 2 ^ 6+ 9420 * X 1 ^ 10 * X 2 ^ 7- 4004 * X 1 ^ 9 * X 2 ^ 8+ 1052 * X 1 ^ 8 * X 2 ^ 9- 156 * X 1 ^ 7 * X 2 ^ 10+ 10 * X 1 ^ 6 * X 2 ^ 11)

-- The integral half-norm lit1G, the sum of its chunks.
def lit1G : MvPolynomial (Fin 3) ℤ :=
    lit1G_0 + lit1G_1 + lit1G_2 + lit1G_3 + lit1G_4 + lit1G_5

def lit1P_0 : Poly2 :=
    X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3

def lit1P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 5+ X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3+ X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5+ X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3+ X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5)

def lit1P_2 : Poly2 :=
    X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3+ X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9+ X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3

def lit1P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9+ X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3+ X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5+ X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5)

def lit1P_4 : Poly2 :=
    X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9+ X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 5+ X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9

def lit1P_5 : Poly2 :=
    0

-- The reduction of lit1G modulo two, the sum of its chunks.
def lit1P : Poly2 :=
    lit1P_0 + lit1P_1 + lit1P_2 + lit1P_3 + lit1P_4 + lit1P_5

theorem lemma56_nu1_half :
    threeTermNorm (baseSym 0 1) = C 2 * lit1G := by
  unfold lit1G lit1G_0 lit1G_1 lit1G_2 lit1G_3 lit1G_4 lit1G_5
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD6, threeTermNorm]
  ring

theorem lemma56_nu1_reduce_0 : reduceTwo lit1G_0 = lit1P_0 := by
  unfold lit1G_0 lit1P_0
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu1_reduce_1 : reduceTwo lit1G_1 = lit1P_1 := by
  unfold lit1G_1 lit1P_1
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu1_reduce_2 : reduceTwo lit1G_2 = lit1P_2 := by
  unfold lit1G_2 lit1P_2
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu1_reduce_3 : reduceTwo lit1G_3 = lit1P_3 := by
  unfold lit1G_3 lit1P_3
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu1_reduce_4 : reduceTwo lit1G_4 = lit1P_4 := by
  unfold lit1G_4 lit1P_4
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu1_reduce_5 : reduceTwo lit1G_5 = lit1P_5 := by
  unfold lit1G_5 lit1P_5
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp only [CharTwo.neg_eq]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu1_reduce : reduceTwo lit1G = lit1P := by
  unfold lit1G lit1P
  simp only [map_add]
  rw [lemma56_nu1_reduce_0, lemma56_nu1_reduce_1, lemma56_nu1_reduce_2, lemma56_nu1_reduce_3, lemma56_nu1_reduce_4, lemma56_nu1_reduce_5]

open PolynomialReflection in
theorem lemma56_nu1_pi : piOperator lit1P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(2, 6, 9), (2, 10, 5), (3, 5, 9), (3, 9, 5), (4, 8, 5), (4, 10, 3), (5, 3, 9), (5, 9, 3),
       (6, 2, 9), (6, 8, 3), (8, 4, 5), (8, 6, 3), (9, 3, 5), (9, 5, 3), (10, 2, 5), (10, 4, 3)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit1P lit1P_0 lit1P_1 lit1P_2 lit1P_3 lit1P_4 lit1P_5
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
