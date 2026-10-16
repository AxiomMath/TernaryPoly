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
-- Half-norm of the symmetric lift of V_15 (column 15), in 7 chunks.
def lit15G_0 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-272 * X 0 ^ 17+ 2312 * X 0 ^ 16 * X 1+ 4280 * X 0 ^ 16 * X 2- 8968 * X 0 ^ 15 * X 1 ^ 2- 34240 * X 0 ^ 15 * X 1 * X 2- 27712 * X 0 ^ 15 * X 2 ^ 2
    + 21020 * X 0 ^ 14 * X 1 ^ 3+ 124668 * X 0 ^ 14 * X 1 ^ 2 * X 2+ 207840 * X 0 ^ 14 * X 1 * X 2 ^ 2+ 99442 * X 0 ^ 14 * X 2 ^ 3- 33220 * X 0 ^ 13 * X 1 ^ 4
    - 273476 * X 0 ^ 13 * X 1 ^ 3 * X 2- 706948 * X 0 ^ 13 * X 1 ^ 2 * X 2 ^ 2- 696094 * X 0 ^ 13 * X 1 * X 2 ^ 3- 223260 * X 0 ^ 13 * X 2 ^ 4+ 37388 * X 0 ^ 12 * X 1 ^ 5
    + 403261 * X 0 ^ 12 * X 1 ^ 4 * X 2+ 1442922 * X 0 ^ 12 * X 1 ^ 3 * X 2 ^ 2+ 2200202 * X 0 ^ 12 * X 1 ^ 2 * X 2 ^ 3+ 1451190 * X 0 ^ 12 * X 1 * X 2 ^ 4
    + 334290 * X 0 ^ 12 * X 2 ^ 5- 30724 * X 0 ^ 11 * X 1 ^ 6- 422298 * X 0 ^ 11 * X 1 ^ 5 * X 2- 1968142 * X 0 ^ 11 * X 1 ^ 4 * X 2 ^ 2)

def lit15G_1 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-4151990 * X 0 ^ 11 * X 1 ^ 3 * X 2 ^ 3- 4233924 * X 0 ^ 11 * X 1 ^ 2 * X 2 ^ 4- 2005740 * X 0 ^ 11 * X 1 * X 2 ^ 5- 346056 * X 0 ^ 11 * X 2 ^ 6
    + 18260 * X 0 ^ 10 * X 1 ^ 7+ 327461 * X 0 ^ 10 * X 1 ^ 6 * X 2+ 1887567 * X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 2+ 5228319 * X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3
    + 7323492 * X 0 ^ 10 * X 1 ^ 3 * X 2 ^ 4+ 5372398 * X 0 ^ 10 * X 1 ^ 2 * X 2 ^ 5+ 1903308 * X 0 ^ 10 * X 1 * X 2 ^ 6+ 252739 * X 0 ^ 10 * X 2 ^ 7
    - 5660 * X 0 ^ 9 * X 1 ^ 8- 203818 * X 0 ^ 9 * X 1 ^ 7 * X 2- 1253551 * X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 2- 4671927 * X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3
    - 8272050 * X 0 ^ 9 * X 1 ^ 4 * X 2 ^ 4- 8476040 * X 0 ^ 9 * X 1 ^ 3 * X 2 ^ 5- 4614904 * X 0 ^ 9 * X 1 ^ 2 * X 2 ^ 6- 1263695 * X 0 ^ 9 * X 1 * X 2 ^ 7
    - 130848 * X 0 ^ 9 * X 2 ^ 8- 5660 * X 0 ^ 8 * X 1 ^ 9+ 152604 * X 0 ^ 8 * X 1 ^ 8 * X 2+ 431880 * X 0 ^ 8 * X 1 ^ 7 * X 2 ^ 2)

def lit15G_2 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (3358273 * X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3+ 6242670 * X 0 ^ 8 * X 1 ^ 5 * X 2 ^ 4+ 8974201 * X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5+ 6492258 * X 0 ^ 8 * X 1 ^ 3 * X 2 ^ 6
    + 2788377 * X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 7+ 588816 * X 0 ^ 8 * X 1 * X 2 ^ 8+ 48152 * X 0 ^ 8 * X 2 ^ 9+ 18260 * X 0 ^ 7 * X 1 ^ 10- 203818 * X 0 ^ 7 * X 1 ^ 9 * X 2
    + 431880 * X 0 ^ 7 * X 1 ^ 8 * X 2 ^ 2- 2633008 * X 0 ^ 7 * X 1 ^ 7 * X 2 ^ 3- 2176488 * X 0 ^ 7 * X 1 ^ 6 * X 2 ^ 4- 7103704 * X 0 ^ 7 * X 1 ^ 5 * X 2 ^ 5
    - 5484988 * X 0 ^ 7 * X 1 ^ 4 * X 2 ^ 6- 3571338 * X 0 ^ 7 * X 1 ^ 3 * X 2 ^ 7- 1120924 * X 0 ^ 7 * X 1 ^ 2 * X 2 ^ 8- 192608 * X 0 ^ 7 * X 1 * X 2 ^ 9
    - 12124 * X 0 ^ 7 * X 2 ^ 10- 30724 * X 0 ^ 6 * X 1 ^ 11+ 327461 * X 0 ^ 6 * X 1 ^ 10 * X 2- 1253551 * X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 2+ 3358273 * X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3
    - 2176488 * X 0 ^ 6 * X 1 ^ 7 * X 2 ^ 4+ 6143480 * X 0 ^ 6 * X 1 ^ 6 * X 2 ^ 5)

def lit15G_3 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (2223410 * X 0 ^ 6 * X 1 ^ 5 * X 2 ^ 6+ 3351591 * X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 7+ 1175426 * X 0 ^ 6 * X 1 ^ 3 * X 2 ^ 8+ 343771 * X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9
    + 42434 * X 0 ^ 6 * X 1 * X 2 ^ 10+ 2102 * X 0 ^ 6 * X 2 ^ 11+ 37388 * X 0 ^ 5 * X 1 ^ 12- 422298 * X 0 ^ 5 * X 1 ^ 11 * X 2+ 1887567 * X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 2
    - 4671927 * X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3+ 6242670 * X 0 ^ 5 * X 1 ^ 8 * X 2 ^ 4- 7103704 * X 0 ^ 5 * X 1 ^ 7 * X 2 ^ 5+ 2223410 * X 0 ^ 5 * X 1 ^ 6 * X 2 ^ 6
    - 2862609 * X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 7- 447046 * X 0 ^ 5 * X 1 ^ 4 * X 2 ^ 8- 357185 * X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9- 54558 * X 0 ^ 5 * X 1 ^ 2 * X 2 ^ 10
    - 6306 * X 0 ^ 5 * X 1 * X 2 ^ 11- 202 * X 0 ^ 5 * X 2 ^ 12- 33220 * X 0 ^ 4 * X 1 ^ 13+ 403261 * X 0 ^ 4 * X 1 ^ 12 * X 2- 1968142 * X 0 ^ 4 * X 1 ^ 11 * X 2 ^ 2
    + 5228319 * X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3- 8272050 * X 0 ^ 4 * X 1 ^ 9 * X 2 ^ 4)

def lit15G_4 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (8974201 * X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5- 5484988 * X 0 ^ 4 * X 1 ^ 7 * X 2 ^ 6+ 3351591 * X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 7- 447046 * X 0 ^ 4 * X 1 ^ 5 * X 2 ^ 8
    + 363892 * X 0 ^ 4 * X 1 ^ 4 * X 2 ^ 9+ 30310 * X 0 ^ 4 * X 1 ^ 3 * X 2 ^ 10+ 9576 * X 0 ^ 4 * X 1 ^ 2 * X 2 ^ 11+ 505 * X 0 ^ 4 * X 1 * X 2 ^ 12+ 11 * X 0 ^ 4 * X 2 ^ 13
    + 21020 * X 0 ^ 3 * X 1 ^ 14- 273476 * X 0 ^ 3 * X 1 ^ 13 * X 2+ 1442922 * X 0 ^ 3 * X 1 ^ 12 * X 2 ^ 2- 4151990 * X 0 ^ 3 * X 1 ^ 11 * X 2 ^ 3
    + 7323492 * X 0 ^ 3 * X 1 ^ 10 * X 2 ^ 4- 8476040 * X 0 ^ 3 * X 1 ^ 9 * X 2 ^ 5+ 6492258 * X 0 ^ 3 * X 1 ^ 8 * X 2 ^ 6- 3571338 * X 0 ^ 3 * X 1 ^ 7 * X 2 ^ 7
    + 1175426 * X 0 ^ 3 * X 1 ^ 6 * X 2 ^ 8- 357185 * X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9+ 30310 * X 0 ^ 3 * X 1 ^ 4 * X 2 ^ 10- 8642 * X 0 ^ 3 * X 1 ^ 3 * X 2 ^ 11
    - 202 * X 0 ^ 3 * X 1 ^ 2 * X 2 ^ 12- 22 * X 0 ^ 3 * X 1 * X 2 ^ 13- 8968 * X 0 ^ 2 * X 1 ^ 15)

def lit15G_5 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (124668 * X 0 ^ 2 * X 1 ^ 14 * X 2- 706948 * X 0 ^ 2 * X 1 ^ 13 * X 2 ^ 2+ 2200202 * X 0 ^ 2 * X 1 ^ 12 * X 2 ^ 3- 4233924 * X 0 ^ 2 * X 1 ^ 11 * X 2 ^ 4
    + 5372398 * X 0 ^ 2 * X 1 ^ 10 * X 2 ^ 5- 4614904 * X 0 ^ 2 * X 1 ^ 9 * X 2 ^ 6+ 2788377 * X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 7- 1120924 * X 0 ^ 2 * X 1 ^ 7 * X 2 ^ 8
    + 343771 * X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9- 54558 * X 0 ^ 2 * X 1 ^ 5 * X 2 ^ 10+ 9576 * X 0 ^ 2 * X 1 ^ 4 * X 2 ^ 11- 202 * X 0 ^ 2 * X 1 ^ 3 * X 2 ^ 12
    + 33 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 13+ 2312 * X 0 * X 1 ^ 16- 34240 * X 0 * X 1 ^ 15 * X 2+ 207840 * X 0 * X 1 ^ 14 * X 2 ^ 2- 696094 * X 0 * X 1 ^ 13 * X 2 ^ 3
    + 1451190 * X 0 * X 1 ^ 12 * X 2 ^ 4- 2005740 * X 0 * X 1 ^ 11 * X 2 ^ 5+ 1903308 * X 0 * X 1 ^ 10 * X 2 ^ 6- 1263695 * X 0 * X 1 ^ 9 * X 2 ^ 7
    + 588816 * X 0 * X 1 ^ 8 * X 2 ^ 8- 192608 * X 0 * X 1 ^ 7 * X 2 ^ 9+ 42434 * X 0 * X 1 ^ 6 * X 2 ^ 10)

def lit15G_6 : MvPolynomial (Fin 3) ℤ :=
  poly_literal% (MvPolynomial (Fin 3) ℤ)
    (-6306 * X 0 * X 1 ^ 5 * X 2 ^ 11+ 505 * X 0 * X 1 ^ 4 * X 2 ^ 12- 22 * X 0 * X 1 ^ 3 * X 2 ^ 13- 272 * X 1 ^ 17+ 4280 * X 1 ^ 16 * X 2- 27712 * X 1 ^ 15 * X 2 ^ 2
    + 99442 * X 1 ^ 14 * X 2 ^ 3- 223260 * X 1 ^ 13 * X 2 ^ 4+ 334290 * X 1 ^ 12 * X 2 ^ 5- 346056 * X 1 ^ 11 * X 2 ^ 6+ 252739 * X 1 ^ 10 * X 2 ^ 7
    - 130848 * X 1 ^ 9 * X 2 ^ 8+ 48152 * X 1 ^ 8 * X 2 ^ 9- 12124 * X 1 ^ 7 * X 2 ^ 10+ 2102 * X 1 ^ 6 * X 2 ^ 11- 202 * X 1 ^ 5 * X 2 ^ 12+ 11 * X 1 ^ 4 * X 2 ^ 13)

-- The integral half-norm lit15G, the sum of its chunks.
def lit15G : MvPolynomial (Fin 3) ℤ :=
    lit15G_0 + lit15G_1 + lit15G_2 + lit15G_3 + lit15G_4 + lit15G_5 + lit15G_6

def lit15P_0 : Poly2 :=
    X 0 ^ 12 * X 1 ^ 4 * X 2

def lit15P_1 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 10 * X 1 ^ 6 * X 2+ X 0 ^ 10 * X 1 ^ 5 * X 2 ^ 2+ X 0 ^ 10 * X 1 ^ 4 * X 2 ^ 3+ X 0 ^ 10 * X 2 ^ 7+ X 0 ^ 9 * X 1 ^ 6 * X 2 ^ 2+ X 0 ^ 9 * X 1 ^ 5 * X 2 ^ 3
    + X 0 ^ 9 * X 1 * X 2 ^ 7)

def lit15P_2 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 8 * X 1 ^ 6 * X 2 ^ 3+ X 0 ^ 8 * X 1 ^ 4 * X 2 ^ 5+ X 0 ^ 8 * X 1 ^ 2 * X 2 ^ 7+ X 0 ^ 6 * X 1 ^ 10 * X 2+ X 0 ^ 6 * X 1 ^ 9 * X 2 ^ 2+ X 0 ^ 6 * X 1 ^ 8 * X 2 ^ 3)

def lit15P_3 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 6 * X 1 ^ 4 * X 2 ^ 7+ X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 9+ X 0 ^ 5 * X 1 ^ 10 * X 2 ^ 2+ X 0 ^ 5 * X 1 ^ 9 * X 2 ^ 3+ X 0 ^ 5 * X 1 ^ 5 * X 2 ^ 7
    + X 0 ^ 5 * X 1 ^ 3 * X 2 ^ 9+ X 0 ^ 4 * X 1 ^ 12 * X 2+ X 0 ^ 4 * X 1 ^ 10 * X 2 ^ 3)

def lit15P_4 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 4 * X 1 ^ 8 * X 2 ^ 5+ X 0 ^ 4 * X 1 ^ 6 * X 2 ^ 7+ X 0 ^ 4 * X 1 * X 2 ^ 12+ X 0 ^ 4 * X 2 ^ 13+ X 0 ^ 3 * X 1 ^ 5 * X 2 ^ 9)

def lit15P_5 : Poly2 :=
  poly_literal% Poly2
    (X 0 ^ 2 * X 1 ^ 8 * X 2 ^ 7+ X 0 ^ 2 * X 1 ^ 6 * X 2 ^ 9+ X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 13+ X 0 * X 1 ^ 9 * X 2 ^ 7)

def lit15P_6 : Poly2 :=
    X 0 * X 1 ^ 4 * X 2 ^ 12+ X 1 ^ 10 * X 2 ^ 7+ X 1 ^ 4 * X 2 ^ 13

-- The reduction of lit15G modulo two, the sum of its chunks.
def lit15P : Poly2 :=
    lit15P_0 + lit15P_1 + lit15P_2 + lit15P_3 + lit15P_4 + lit15P_5 + lit15P_6

theorem lemma56_nu15_half :
    threeTermNorm (baseSym 3 3) = C 2 * lit15G := by
  unfold lit15G lit15G_0 lit15G_1 lit15G_2 lit15G_3 lit15G_4 lit15G_5 lit15G_6
  simp [baseSym, mult, oddGenLiftSym, genLiftSym, basisLift, kappa,
    liftD7, liftCplus, liftC, liftB, liftA, liftD4, liftD6, threeTermNorm]
  ring

theorem lemma56_nu15_reduce_0 : reduceTwo lit15G_0 = lit15P_0 := by
  unfold lit15G_0 lit15P_0
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu15_reduce_1 : reduceTwo lit15G_1 = lit15P_1 := by
  unfold lit15G_1 lit15P_1
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu15_reduce_2 : reduceTwo lit15G_2 = lit15P_2 := by
  unfold lit15G_2 lit15P_2
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu15_reduce_3 : reduceTwo lit15G_3 = lit15P_3 := by
  unfold lit15G_3 lit15P_3
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu15_reduce_4 : reduceTwo lit15G_4 = lit15P_4 := by
  unfold lit15G_4 lit15P_4
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu15_reduce_5 : reduceTwo lit15G_5 = lit15P_5 := by
  unfold lit15G_5 lit15P_5
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu15_reduce_6 : reduceTwo lit15G_6 = lit15P_6 := by
  unfold lit15G_6 lit15P_6
  simp [reduceTwo]
  try ring_nf
  try simp only [CharTwo.sub_eq_add]
  try simp [ofNat_mod_poly2]

theorem lemma56_nu15_reduce : reduceTwo lit15G = lit15P := by
  unfold lit15G lit15P
  simp only [map_add]
  rw [lemma56_nu15_reduce_0, lemma56_nu15_reduce_1, lemma56_nu15_reduce_2, lemma56_nu15_reduce_3, lemma56_nu15_reduce_4, lemma56_nu15_reduce_5, lemma56_nu15_reduce_6]

open PolynomialReflection in
theorem lemma56_nu15_pi : piOperator lit15P = 0 := by
  refine piOperator_eq_of_reflect (lP :=
      [(0, 4, 13), (0, 10, 7), (1, 4, 12), (1, 9, 7), (2, 2, 13), (2, 6, 9), (2, 8, 7), (3, 5, 9),
       (4, 0, 13), (4, 1, 12), (4, 6, 7), (4, 8, 5), (4, 10, 3), (4, 12, 1), (5, 3, 9), (5, 5, 7),
       (5, 9, 3), (5, 10, 2), (6, 2, 9), (6, 4, 7), (6, 8, 3), (6, 9, 2), (6, 10, 1), (8, 2, 7),
       (8, 4, 5), (8, 6, 3), (9, 1, 7), (9, 5, 3), (9, 6, 2), (10, 0, 7), (10, 4, 3), (10, 5, 2),
       (10, 6, 1), (12, 4, 1)])
    (lQ := []) ?_ ?_ ?_
  · unfold lit15P lit15P_0 lit15P_1 lit15P_2 lit15P_3 lit15P_4 lit15P_5 lit15P_6
    simp only [ev, mono, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  · simp only [ev_nil]
  · decide +kernel

end

end TernaryPeriodPolynomials.Argument.Identities.Lemma56Table
