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
-- Half-norm of the symmetric lift of V_10 (column 10), in 6 chunks.
def lit10G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (680 * X 0 ^ 16 * X 2- 5440 * X 0 ^ 15 * X 1 * X 2- 7096 * X 0 ^ 15 * X 2 ^ 2+ 19836 * X 0 ^ 14 * X 1 ^ 2 * X 2+ 53220 * X 0 ^ 14 * X 1 * X 2 ^ 2
    + 31202 * X 0 ^ 14 * X 2 ^ 3- 43652 * X 0 ^ 13 * X 1 ^ 3 * X 2- 181088 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 2- 218414 * X 0 ^ 13 * X 1 * X 2 ^ 3- 76732 * X 0 ^ 13 * X 2 ^ 4
    + 64708 * X 0 ^ 12 * X 1 ^ 4 * X 2+ 369902 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 2+ 689688 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 3+ 498758 * X 0 ^ 12 * X 1 * X 2 ^ 4
    + 118434 * X 0 ^ 12 * X 2 ^ 5- 68292 * X 0 ^ 11 * X 1 ^ 5 * X 2- 505178 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 2- 1298746 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 3
    - 1451474 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 4- 710604 * X 0 ^ 11 * X 1 * X 2 ^ 5- 121676 * X 0 ^ 11 * X 2 ^ 6+ 53564 * X 0 ^ 10 * X 1 ^ 6 * X 2
    + 485331 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 2+ 1629320 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3)

def lit10G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2496769 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 4+ 1893658 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 5+ 669218 * X 0 ^ 10 * X 1 * X 2 ^ 6+ 85834 * X 0 ^ 10 * X 2 ^ 7
    - 33916 * X 0 ^ 9 * X 1 ^ 7 * X 2- 322939 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 2- 1446962 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3- 2797025 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 4
    - 2954420 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5- 1612670 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 6- 429170 * X 0 ^ 9 * X 1 * X 2 ^ 7- 42164 * X 0 ^ 9 * X 2 ^ 8
    + 25704 * X 0 ^ 8 * X 1 ^ 8 * X 2+ 111396 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 2+ 1030156 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3+ 2090352 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 4
    + 3062515 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5+ 2237880 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 6+ 933877 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 7+ 189738 * X 0 ^ 8 * X 1 * X 2 ^ 8
    + 14426 * X 0 ^ 8 * X 2 ^ 9- 33916 * X 0 ^ 7 * X 1 ^ 9 * X 2+ 111396 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 2- 801286 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 3)

def lit10G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-722282 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 4- 2340184 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 5- 1858800 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 6- 1160488 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 7
    - 358326 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 8- 57704 * X 0 ^ 7 * X 1 * X 2 ^ 9- 3384 * X 0 ^ 7 * X 2 ^ 10+ 53564 * X 0 ^ 6 * X 1 ^ 10 * X 2- 322939 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 2
    + 1030156 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3- 722282 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 4+ 1979636 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 5+ 746886 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 6
    + 1033466 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 7+ 368697 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 8+ 99232 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9+ 11844 * X 0 ^ 6 * X 1 * X 2 ^ 10
    + 522 * X 0 ^ 6 * X 2 ^ 11- 68292 * X 0 ^ 5 * X 1 ^ 11 * X 2+ 485331 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 2- 1446962 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3
    + 2090352 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 4- 2340184 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 5+ 746886 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 6)

def lit10G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-841204 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 7- 136863 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 8- 95732 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9- 15228 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 10
    - 1566 * X 0 ^ 5 * X 1 * X 2 ^ 11- 48 * X 0 ^ 5 * X 2 ^ 12+ 64708 * X 0 ^ 4 * X 1 ^ 12 * X 2- 505178 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 2
    + 1629320 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3- 2797025 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 4+ 3062515 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5- 1858800 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 6
    + 1033466 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 7- 136863 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 8+ 93982 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 9+ 8460 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 10
    + 2199 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 11+ 120 * X 0 ^ 4 * X 1 * X 2 ^ 12+ 2 * X 0 ^ 4 * X 2 ^ 13- 43652 * X 0 ^ 3 * X 1 ^ 13 * X 2+ 369902 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 2
    - 1298746 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 3+ 2496769 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 4- 2954420 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5)

def lit10G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2237880 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 6- 1160488 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 7+ 368697 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 8- 95732 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9
    + 8460 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 10- 1788 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 11- 48 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 12- 4 * X 0 ^ 3 * X 1 * X 2 ^ 13
    + 19836 * X 0 ^ 2 * X 1 ^ 14 * X 2- 181088 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 2+ 689688 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 3- 1451474 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 4
    + 1893658 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 5- 1612670 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 6+ 933877 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 7- 358326 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 8
    + 99232 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9- 15228 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 10+ 2199 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 11- 48 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 12
    + 6 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 13- 5440 * X 0 * X 1 ^ 15 * X 2+ 53220 * X 0 * X 1 ^ 14 * X 2 ^ 2- 218414 * X 0 * X 1 ^ 13 * X 2 ^ 3)

def lit10G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (498758 * X 0 * X 1 ^ 12 * X 2 ^ 4- 710604 * X 0 * X 1 ^ 11 * X 2 ^ 5+ 669218 * X 0 * X 1 ^ 10 * X 2 ^ 6- 429170 * X 0 * X 1 ^ 9 * X 2 ^ 7
    + 189738 * X 0 * X 1 ^ 8 * X 2 ^ 8- 57704 * X 0 * X 1 ^ 7 * X 2 ^ 9+ 11844 * X 0 * X 1 ^ 6 * X 2 ^ 10- 1566 * X 0 * X 1 ^ 5 * X 2 ^ 11+ 120 * X 0 * X 1 ^ 4 * X 2 ^ 12
    - 4 * X 0 * X 1 ^ 3 * X 2 ^ 13+ 680 * X 1 ^ 16 * X 2- 7096 * X 1 ^ 15 * X 2 ^ 2+ 31202 * X 1 ^ 14 * X 2 ^ 3- 76732 * X 1 ^ 13 * X 2 ^ 4+ 118434 * X 1 ^ 12 * X 2 ^ 5
    - 121676 * X 1 ^ 11 * X 2 ^ 6+ 85834 * X 1 ^ 10 * X 2 ^ 7- 42164 * X 1 ^ 9 * X 2 ^ 8+ 14426 * X 1 ^ 8 * X 2 ^ 9- 3384 * X 1 ^ 7 * X 2 ^ 10+ 522 * X 1 ^ 6 * X 2 ^ 11
    - 48 * X 1 ^ 5 * X 2 ^ 12+ 2 * X 1 ^ 4 * X 2 ^ 13)

-- The integral half-norm lit10G, the sum of its chunks.
def lit10G : MvPolynomial (Fin 3) ℤ :=
    lit10G_0 + lit10G_1 + lit10G_2 + lit10G_3 + lit10G_4 + lit10G_5

def lit10P_0 : Poly2 :=
    X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 2

def lit10P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 4+ X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 2+ X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 4+ X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5+ X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 7)

def lit10P_2 : Poly2 :=
    X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 2+ X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 8+ X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 2

def lit10P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 8+ X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 4+ X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5+ X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 8+ X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 11
    + X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 4)

def lit10P_4 : Poly2 :=
    X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 8+ X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 7+ X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 11

def lit10P_5 : Poly2 :=
    0

-- The reduction of lit10G modulo two, the sum of its chunks.
def lit10P : Poly2 :=
    lit10P_0 + lit10P_1 + lit10P_2 + lit10P_3 + lit10P_4 + lit10P_5

theorem lemma56_nu10_half :
    threeTermNorm (baseSym 2 2) = C 2 * lit10G := by
  unfold lit10G lit10G_0 lit10G_1 lit10G_2 lit10G_3 lit10G_4 lit10G_5
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, threeTermNorm]
  ring

theorem lemma56_nu10_reduce_0 : reduceTwo lit10G_0 = lit10P_0 := by
  unfold lit10G_0 lit10P_0
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu10_reduce_1 : reduceTwo lit10G_1 = lit10P_1 := by
  unfold lit10G_1 lit10P_1
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu10_reduce_2 : reduceTwo lit10G_2 = lit10P_2 := by
  unfold lit10G_2 lit10P_2
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu10_reduce_3 : reduceTwo lit10G_3 = lit10P_3 := by
  unfold lit10G_3 lit10P_3
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  try simp only [CharTwo.sub_eq_add]
  simp [ofNat_mod_poly2]

theorem lemma56_nu10_reduce_4 : reduceTwo lit10G_4 = lit10P_4 := by
  unfold lit10G_4 lit10P_4
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu10_reduce_5 : reduceTwo lit10G_5 = lit10P_5 := by
  unfold lit10G_5 lit10P_5
  simp [reduceTwo, CharTwo.sub_eq_add]
  ring_nf
  simp [ofNat_mod_poly2]

theorem lemma56_nu10_reduce : reduceTwo lit10G = lit10P := by
  unfold lit10G lit10P
  simp only [map_add]
  rw [lemma56_nu10_reduce_0, lemma56_nu10_reduce_1, lemma56_nu10_reduce_2, lemma56_nu10_reduce_3, lemma56_nu10_reduce_4, lemma56_nu10_reduce_5]

open PolynomialReflection in
theorem lemma56_nu10_pi : piOperator lit10P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(2, 4, 11), (2, 8, 7), (3, 6, 8), (3, 10, 4), (4, 2, 11), (4, 5, 8), (4, 8, 5), (4, 9, 4),
       (5, 4, 8), (5, 10, 2), (6, 3, 8), (6, 9, 2), (8, 2, 7), (8, 4, 5), (9, 4, 4), (9, 6, 2),
       (10, 3, 4), (10, 5, 2)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit10P lit10P_0 lit10P_1 lit10P_2 lit10P_3 lit10P_4 lit10P_5
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
